// If you choose to use C++, read this very carefully:
// https://www.postgresql.org/docs/15/xfunc-c.html#EXTEND-CPP

#include "dog.h"
#include <map>
#include <stack>
#include <iostream>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

// clang-format off
extern "C" {
#include "../../../../src/include/postgres.h"
#include "../../../../src/include/fmgr.h"
#include "../../../../src/include/foreign/fdwapi.h"
#include "../../../../src/include/commands/defrem.h"
#include "../../../../src/include/foreign/foreign.h"
#include "../../../../src/include/nodes/pg_list.h"
#include "../../../../src/include/optimizer/optimizer.h"
#include "../../../../src/include/optimizer/pathnode.h"
#include "../../../../src/include/optimizer/restrictinfo.h"
#include "../../../../src/include/optimizer/planmain.h"
#include "../../../../src/include/access/relscan.h"
#include "../../../../src/include/utils/rel.h"
#include "../../../../src/include/nodes/execnodes.h"
#include "../../../../src/include/executor/executor.h"
#include "../../../../src/include/nodes/pathnodes.h"
#include "../../../../src/include/access/table.h"
#include "../../../../src/include/parser/parsetree.h"
#include "../../../../src/include/optimizer/tlist.h"
#include "../../../../src/include/nodes/makefuncs.h"
#include "../../../../src/include/utils/builtins.h"
}
// clang-format on

typedef struct db721FdwOptions {
    char* filename;
    char* tablename;
} db721FdwOptions;

typedef struct BlockStats {
	int num;
	int min_len;
	int max_len;
	union {
		int i;
		float f;
		char s[32];
	}min, max;
} BlockStats;

typedef struct ColumnMetadata {
	char type[32];
	int start_offest;
	int num_blocks;
	std::map<int, BlockStats*>* block_stats;
} ColumnMetadata;

typedef struct db721Metadata {
	char tablename[32];
	int max_values_per_block;
	std::map<std::string, ColumnMetadata*>* column_datas;
} db721Metadata;

const int TUPLE_LEN = 10;
typedef struct Tuple {
	Datum tuple[TUPLE_LEN];
} Tuple;

typedef struct db721ExecutionState {
	db721Metadata* meta;
	char* filename;
	FILE* table;

	char* mmap_table; // map table file to mmap_table
	size_t size;      // map file size

	int index; 				// the current index
	int first_index; 		// the scan index, based on block stats
	int last_index; 		// the last rows index, based on block stats
	Bitmapset* attrs_used;	// use for output and quals
	List* quals; 			// for update first index and last index 
	Relation rel;
	TupleDesc tupdesc;
	int total_tuples;
	ExprState* qual; 		// for ExecQual()
	Bitmapset* col_used;    // store skip column

	MemoryContext batch_cxt; // for read batch tuples in memory

	// stroe tuples
	Tuple *tuples;
	int num_tuples;
	int next_tuples;
} db721ExecutionState;

int min(int a, int b);	
int max(int a, int b);
static db721FdwOptions* db721GetOptions(Oid foreigntableid);
static db721Metadata* db721GetMetadata(db721FdwOptions* options);
static db721Metadata* parserMetadata(char* metadata, int size);
static std::map<std::string, ColumnMetadata*>* parseAllColumnMetadata(char* metadata, int* index, int size);
static ColumnMetadata* parseColumnMetadata(char* metadata, int* index, int size);
static std::map<int, BlockStats*>* parseAllBlockStats(char* metadata, int* index, int size, const char* type);
static BlockStats* parseBlockStats(char* metadata, int* index, int size, const char* type);
static void estimateCosts(PlannerInfo* root, RelOptInfo* baserel, db721Metadata* fdw_private, Cost* startup_cost, Cost* total_cost);
static db721ExecutionState* create_db721ExectionState(ForeignScanState* node);
static bool fetchTupleAtIndex(ForeignScanState* node, db721ExecutionState* festate, int index, TupleTableSlot* tuple);	
static void updateIndexWithBlockStats(db721ExecutionState* festate);
static void fetchBatchTuples(ForeignScanState* node, db721ExecutionState* festate);

extern "C" void db721_GetForeignRelSize(PlannerInfo *root, RelOptInfo *baserel,
                                      Oid foreigntableid) {
	db721FdwOptions* options = db721GetOptions(foreigntableid);
	db721Metadata* meta = db721GetMetadata(options);
	// printfMetadata(meta);
	baserel->tuples = 0;
	for(auto it1 : *(meta->column_datas)){
		for(auto it2 : *(it1.second->block_stats)){
			baserel->tuples += it2.second->num;
		}
		break;
	}

	baserel->rows = baserel->tuples * clauselist_selectivity(root, baserel->baserestrictinfo, 0, JOIN_INNER, NULL);
	baserel->fdw_private = meta;

	// free options
	pfree(options);
}

extern "C" void db721_GetForeignPaths(PlannerInfo *root, RelOptInfo *baserel,
                                    Oid foreigntableid) {
 	db721Metadata* meta = (db721Metadata*) baserel->fdw_private;
	Path* foreignScanPath = NULL;
	Cost startup_cost;
	Cost total_cost;

	estimateCosts(root, baserel, meta, &startup_cost, &total_cost);

	foreignScanPath = (Path*) create_foreignscan_path(root, 
													  baserel, 
													  NULL, 
													  baserel->rows, 
													  startup_cost, total_cost,
													  NIL, /* no pathkeys */
													  NULL, /* no outer rel either */
													  NULL, /* no extra plan */
													  NIL);/* no fdw_private*/
	add_path(baserel, (Path*)foreignScanPath);
}

extern "C" ForeignScan *
db721_GetForeignPlan(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid,
                   ForeignPath *best_path, List *tlist, List *scan_clauses,
                   Plan *outer_plan) {
	List *fdw_private = NIL;
	ListCell *lc;

	// get all attrs used for output and quals
	Bitmapset* attrs_used = NULL;
	pull_varattnos((Node*)baserel->reltarget->exprs, baserel->relid, &attrs_used);
	foreach(lc, baserel->baserestrictinfo)
	{
		RestrictInfo* rinfo = (RestrictInfo*)lfirst(lc);
		pull_varattnos((Node*) rinfo->clause, baserel->relid, &attrs_used);
	}

	scan_clauses = extract_actual_clauses(scan_clauses, false);
	db721FdwOptions* options = db721GetOptions(foreigntableid);
	fdw_private = lappend(fdw_private, baserel->fdw_private);
	fdw_private = lappend(fdw_private, makeString(options->filename));
	fdw_private = lappend(fdw_private, attrs_used);
	fdw_private = lappend(fdw_private, scan_clauses);

	return make_foreignscan(tlist,
							NIL,
							baserel->relid,
							NIL,
							fdw_private,
							NIL, // fdw_scan_tlist, replace use fdw_scan_tlist, we can set no used att to null
							scan_clauses,
							outer_plan);
}

extern "C" void db721_BeginForeignScan(ForeignScanState *node, int eflags) {
	node->fdw_state = create_db721ExectionState(node);
	db721ExecutionState* festate = (db721ExecutionState*) node->fdw_state;
	EState	   *estate = node->ss.ps.state;
	updateIndexWithBlockStats(festate);
	festate->batch_cxt = AllocSetContextCreate(estate->es_query_cxt,
												"db721_fdw batch tuple data",
												ALLOCSET_DEFAULT_SIZES);
}

extern "C" TupleTableSlot *db721_IterateForeignScan(ForeignScanState *node) {
	db721ExecutionState* festate = (db721ExecutionState*) node->fdw_state;
	TupleTableSlot *tuple = node->ss.ss_ScanTupleSlot;
	std::string error;
	ExprState* qual = festate->qual;
	ExprContext* econtext = node->ss.ps.ps_ExprContext;

	try{
		for(;;){
			bool flag = fetchTupleAtIndex(node, festate, festate->index, tuple);	
			if(!flag){
				return NULL;
			}

			econtext->ecxt_scantuple = tuple;
			if(qual == NULL || ExecQual(qual, econtext)){
				break;
			} else {
				ResetExprContext(econtext);
				continue;
			}
		}
	} catch (std::exception &e) {
		error = e.what();
		printf("catch error: %s\n", error.c_str());
		return NULL;
	}

 	return tuple;
}

extern "C" void db721_ReScanForeignScan(ForeignScanState *node) {
	db721ExecutionState* festate = (db721ExecutionState*) node->fdw_state;
	festate->index = festate->first_index;
}

extern "C" void db721_EndForeignScan(ForeignScanState *node) {
	// delete db721Metadata memory that we alloc in db721_GetForeignRelSize
	db721ExecutionState* festate = (db721ExecutionState*) node->fdw_state;
	munmap(festate->mmap_table, festate->size);
	FreeFile(festate->table);
	db721Metadata *meta = festate->meta;
	for(auto it1 : *(meta->column_datas)){
		for(auto it2 : *(it1.second->block_stats)){
			pfree(it2.second);
		}
		delete it1.second->block_stats;
		pfree(it1.second);
	}
	delete meta->column_datas;
	pfree(meta);
}

static bool fetchTupleAtIndex(ForeignScanState* node, db721ExecutionState* festate, int index, TupleTableSlot* tuple){
	if(festate->total_tuples <= index) {
		return false;
	}
	// check if current batch tuples reach to end
	if(festate->index == festate->last_index) {
		bool is_read = false;
		int column_index = festate->index / festate->meta->max_values_per_block;  
		int num_blocks = festate->meta->column_datas->begin()->second->num_blocks;
		for(int i = column_index; i < num_blocks; i++){
			if(!bms_is_member(i, festate->col_used)){
				is_read = true;
				festate->first_index = i * festate->meta->max_values_per_block;
				festate->last_index = min((i+1) * festate->meta->max_values_per_block, festate->total_tuples);
				break;
			}
		}
		if(!is_read)
			festate->first_index = festate->total_tuples;
		festate->index = festate->first_index;
		index = festate->index;
		// printf("index: %d, last index: %d\n", festate->index, festate->last_index);
	}
	if(festate->total_tuples <= index) {
		return false;
	}

	if(festate->next_tuples >= festate->num_tuples){
		fetchBatchTuples(node, festate);
	} 

	ExecClearTuple(tuple);
	memset(tuple->tts_isnull, true, sizeof(bool)*festate->tupdesc->natts);
	for(int i = 1; i <= festate->tupdesc->natts; i++){
		if(bms_is_member(i - FirstLowInvalidHeapAttributeNumber, festate->attrs_used))
			tuple->tts_isnull[i-1] = false;
	}
	memcpy(tuple->tts_values, festate->tuples[festate->next_tuples++].tuple, sizeof(Datum)*festate->tupdesc->natts);
	ExecStoreVirtualTuple(tuple);

	festate->index += 1;
	return true;
}

static void updateIndexWithBlockStats(db721ExecutionState* festate){
	// TODO: very inelegant, can i have a inelegant implement?
	// float8 operator id
	// type 701
	// =  1120
	// >  1123
	// <  1122
	// <> 1121
	// int operator  id
	// type 23
	// =  96
	// >  521
	// <  97
	// <> 518
	// text operator id
	// type 25
	// =  98
	// >  666
	// <  664
	// <> 531

	typedef union Value {
		int i;
		float8 f;
		char* s;
	}Value;

	ListCell* lc;
	foreach(lc, festate->quals) 
	{
		if(IsA(lfirst(lc), OpExpr)){
			OpExpr* expr = (OpExpr*) lfirst(lc);
			Expr* left = (Expr*) linitial(expr->args);
			Expr* right = (Expr*) lsecond(expr->args);
			Var* v;
			Const* c;

			while(left && IsA(left, RelabelType)) left = ((RelabelType*)left)->arg; 
			while(right && IsA(right, RelabelType)) right = ((RelabelType*)right)->arg; 

			if(IsA(left, Var) && IsA(right, Const)){
				v = (Var*) left;
				c = (Const*) right;
			} else { // maybe result error
				v = (Var*) right;
				c = (Const*) left;
			}

			Value value;
			value.s = (char*)palloc0(32);
			if(c->consttype == 23){
				value.i = DatumGetInt32(c->constvalue);
			} else if (c->consttype == 701) {
				value.f = DatumGetFloat8(c->constvalue);
			} else {
				text* t = (text*)c->constvalue;
				memcpy(value.s, t->vl_dat, VARSIZE(t)-4);
			}

			Form_pg_attribute attr = TupleDescAttr(festate->tupdesc, v->varattno - 1);
			auto col_meta = (*festate->meta->column_datas)[std::string(attr->attname.data)];
			// int max_values_per_block = festate->meta->max_values_per_block;
			for(unsigned int i = 0; i < col_meta->block_stats->size(); i++){
				auto stats = (*col_meta->block_stats)[i];
				// int tuples = stats->num;
				bool skip = false;

				if(strcmp(col_meta->type, "str") == 0) {
					if(expr->opno == 98){ // ==
						if(strcoll(stats->min.s, value.s) > 0 || strcoll(stats->max.s, value.s) < 0) 
							skip = true;
					} else if(expr->opno == 531) { // <>
						if(strcoll(stats->min.s, value.s) == 0 && strcoll(stats->max.s, value.s) == 0)
							skip = true;
					} else if(expr->opno == 664) { // <
						// why in postgresql, 'B' > 'b' is true? -> strcoll(): char order based ond LC_COLLATE 
						// noisepage_db=# select 'B' > 'b';
						//  ?column? 
						//  ----------
						//  t
						// (1 row)
						if(strcoll(stats->min.s, value.s) >= 0)
							skip = true;
					} else if(expr->opno == 666) { // >
						if(strcoll(stats->max.s, value.s) <= 0)
							skip = true;
					}
				} else if(strcmp(col_meta->type, "int") == 0) {
					if(expr->opno == 96) { 		 // ==
						if(stats->min.i > value.i || stats->max.i < value.i) 
							skip = true;
					} else if(expr->opno == 518) { // <>
						if(stats->min.i == value.i && stats->max.i == value.i)
							skip = true;
					} else if(expr->opno == 97) { // <
						if(stats->min.i >= value.i)
							skip = true;
					} else if(expr->opno == 521) { // >
						if(stats->max.i <= value.i)
							skip = true;
					}
				} else if(strcmp(col_meta->type, "float") == 0){
					if(expr->opno == 1120) { 		 // ==
						if(stats->min.f > value.f || stats->max.f < value.f) 
							skip = true;
					} else if(expr->opno == 1121) { // <>
						if(abs(stats->min.f - value.f) < 0.000001 && abs(stats->max.f - value.f) < 0.000001)
							skip = true;
					} else if(expr->opno == 1122) { // <
						if(stats->min.f > value.f || abs(stats->min.f - value.f) < 0.000001)
							skip = true;
					} else if(expr->opno == 1123) { // >
						if(stats->max.f < value.f || abs(stats->max.f - value.f) < 0.000001)
							skip = true;
					}
				} else {
					printf("error type\n");
				}

				if(skip) {
					festate->col_used = bms_add_member(festate->col_used, i);
				}
			}
		}
	}

	bool is_read = false;
	int num_blocks = festate->meta->column_datas->begin()->second->num_blocks;
	for(int i = 0; i < num_blocks; i++){
		if(!bms_is_member(i, festate->col_used)){
			is_read = true;
			festate->first_index = i * festate->meta->max_values_per_block;
			festate->last_index = min((i+1) * festate->meta->max_values_per_block, festate->total_tuples);
			break;
		}
	}
	if(!is_read)
		festate->first_index = festate->total_tuples;
	// remember update index
	festate->index = festate->first_index;
	// printf("index: %d, last index: %d\n", festate->index, festate->last_index);
}

static db721ExecutionState* create_db721ExectionState(ForeignScanState* node){
	db721ExecutionState *state = (db721ExecutionState*) palloc0(sizeof(db721ExecutionState));
	ForeignScan *plan = (ForeignScan*) node->ss.ps.plan;
	List* fdw_private = plan->fdw_private;
	db721Metadata* meta = NULL;
	char* filename = NULL;
	Bitmapset* attrs_used = NULL;
	List* quals = NIL;
	ListCell *lc = NULL;
	int i = 0; 

	foreach(lc, fdw_private)
	{
		switch(i)
		{
			case 0:
				meta = (db721Metadata*) lfirst(lc);
				break;
			case 1:
				filename = strVal(lfirst(lc));
				break;
			case 2:
				attrs_used = (Bitmapset*)lfirst(lc);
				break;
			case 3:
				quals = (List*)lfirst(lc);	
				break;
		}
		++i;		
	}

	// get table FILE
	FILE* tableFile = AllocateFile(filename, PG_BINARY_R);
	if(tableFile == NULL){
		printf("open file error\n");
		return nullptr;
	}

	// use mmap
	int fd = open(filename, O_RDONLY);
	if(fd < 0){
		printf("open failed\n");
		return nullptr;
	}
	struct stat st;
	fstat(fd, &st);
	state->size = st.st_size;

	state->mmap_table = static_cast<char*>(mmap(nullptr, state->size, PROT_READ, MAP_SHARED, fd, 0));
	if (state->mmap_table == MAP_FAILED) {
        perror("mmap failed");
        return nullptr;
    }

	// calculate total tuples
	int total_tuples = 0; 
	for(auto it : *(meta->column_datas)){
		for(auto it2 : *(it.second->block_stats)){
			total_tuples += it2.second->num;
		}
		break;
	}

	// make the ExprState
	ExprState* qual = ExecInitQual(quals, (PlanState*) &node->ss);

	state->meta = meta;
	state->filename = filename;
	state->index = 0;
	state->total_tuples = total_tuples;
	state->first_index = 0;
	state->last_index = total_tuples;
	state->table = tableFile;
	state->attrs_used = attrs_used; 
	state->quals = quals;
	state->rel = node->ss.ss_currentRelation;
	state->tupdesc = RelationGetDescr(state->rel);
	state->qual = qual;

	return state;
}

static void fetchBatchTuples(ForeignScanState* node, db721ExecutionState* festate){
	MemoryContext oldcontext;
	festate->tuples = NULL;
	MemoryContextReset(festate->batch_cxt);
	oldcontext = MemoryContextSwitchTo(festate->batch_cxt);
	int batch_size = 100;

	int index = festate->index;	
	int first_index = festate->first_index;
	int last_index = festate->last_index;
	
	int numrows = min(batch_size, last_index - first_index);

	festate->tuples = (Tuple*) palloc0(numrows * sizeof(Tuple));
	festate->num_tuples = numrows;
	festate->next_tuples = 0;

	for(int i = 1; i <= festate->tupdesc->natts; i++)
	{
		if(!bms_is_member(i - FirstLowInvalidHeapAttributeNumber, festate->attrs_used)){
			continue;
		}

		Form_pg_attribute attr = TupleDescAttr(festate->tupdesc, i-1);
		char* name = attr->attname.data;
		auto it = (*festate->meta->column_datas)[std::string(name)];
		char* type = it->type;
		int start_offest = it->start_offest;

		if(strcmp(type, "str") == 0){
			// char* buffer = (char*)palloc0((numrows+1)*32*sizeof(char));
			// if(fseek(festate->table, start_offest+index*32, SEEK_SET) != 0){
			// 	printf("seek to start offest int error\n");
			// }
			// int read_num = 0;
			// if((read_num = fread(buffer, 32, numrows, festate->table)) != numrows){
			// 	printf("read str fail\n");
			// }

			// i-1: attribute, j: tuple index
			for(int j = 0; j < numrows; j++){
				// int input_len = strlen(buffer+j*32);
				int input_len = strlen((const char*)festate->mmap_table+start_offest+index*32+j*32);
				int len = input_len + VARHDRSZ;
				char* result = (char*) palloc0(len);
				SET_VARSIZE(result, len);
				memcpy(VARDATA(result), festate->mmap_table+start_offest+index*32+j*32, input_len);
				festate->tuples[j].tuple[i-1] = PointerGetDatum(result);
			}
			// pfree(buffer);
		} else if(strcmp(type, "int") == 0){
			int buffer[numrows+1];
			// if(fseek(festate->table, start_offest+index*4, SEEK_SET) != 0){
			// 	printf("seek to start offest int error\n");
			// }
			// if(fread(buffer, 4, numrows, festate->table) != (size_t)numrows){
			// 	printf("read int fail\n");
			// }
			memcpy(buffer, festate->mmap_table+start_offest+index*4, numrows*4);
			// i-1: attribute, j: tuple index
			for(int j = 0; j < numrows; j++){
				festate->tuples[j].tuple[i-1] = Int32GetDatum(buffer[j]);
			}
		} else if(strcmp(type, "float") == 0){
			float buffer[numrows+1];
			// if(fseek(festate->table, start_offest+index*4, SEEK_SET) != 0){
			// 	printf("seek to start offest int error\n");
			// }
			// if(fread(buffer, 4, numrows, festate->table) != (size_t)numrows){
			// 	printf("read float fail\n");
			// }
			memcpy(buffer, festate->mmap_table+start_offest+index*4, numrows*4);
			// i-1: attribute, j: tuple index
			for(int j = 0; j < numrows; j++){
				festate->tuples[j].tuple[i-1] = Float4GetDatum(buffer[j]);
			}
		}
	}

	MemoryContextSwitchTo(oldcontext);
}

int min(int a, int b){
	if(a > b){
		return b;
	} else {
		return a;
	}
}

int max(int a, int b){
	if(a > b){
		return a;
	} else {
		return b;
	}
}

static db721FdwOptions* db721GetOptions(Oid foreigntableid){
	db721FdwOptions* options = nullptr;
	char* filename = nullptr;
	char* tablename = nullptr;
	ForeignTable *foreignTable = nullptr;
	ListCell *lc;

	foreignTable = GetForeignTable(foreigntableid);
	foreach(lc, foreignTable->options)
	{
		DefElem *def = (DefElem *) lfirst(lc);
		if(strcmp(def->defname, "filename") == 0){
      		filename = defGetString(def);
		}
		if(strcmp(def->defname, "tablename") == 0){
      		tablename = defGetString(def);
		}
	}

	options = (db721FdwOptions*) palloc0(sizeof(db721FdwOptions));
	options->filename = filename;
	options->tablename = tablename;

  	return options;
}

static db721Metadata* db721GetMetadata(db721FdwOptions* options){
	db721Metadata *metadata;

	// open table file
	FILE* tableFile = AllocateFile(options->filename, PG_BINARY_R);
	if(tableFile == NULL){
		printf("open file error\n");
		return nullptr;
	}

	// read table's metadata 
	if(fseek(tableFile, -4, SEEK_END) != 0){
		printf("seek to end fail\n");
		return nullptr;
	}
	int metadata_size;
	if(fread(&metadata_size, 4, 1, tableFile) != 1){
		printf("read metadata size fail\n");
		return nullptr;
	}
	// printf("metadata size is %d\n", metadata_size);

	// read all metadata
	char *data = (char*)palloc0(metadata_size);
	if(fseek(tableFile, -(4+metadata_size), SEEK_END) != 0){
		printf("seek to metadata fail\n");
		return nullptr;
	}
	if(fread(data, metadata_size, 1, tableFile) != 1){
		printf("read metadata fail\n");
		return nullptr;
	}
	// printf("metadata is %s\n", data);

	// parser metadata
	metadata = parserMetadata(data, metadata_size);
	if(metadata == nullptr){
		return nullptr;
	}

	// close file
	FreeFile(tableFile);

	return metadata;
}

static db721Metadata* parserMetadata(char* metadata, int size){
	int state = 0;
	char key[32];
	char value[32];
	std::fill(key, key+32, 0);
	std::fill(value, value+32, 0);
	int key_len = 0;
	int value_len = 0;
	db721Metadata* meta = (db721Metadata*) palloc0(sizeof(db721Metadata));

	for(int i = 0; i < size; i++){
		int c = metadata[i];
		if(c == '{') {
			state = 0;
			key_len = 0;
			value_len = 0;
		} else if(c == ':') {
			state = 1;	
			key[key_len++] = '\0';
			if(strcmp(key, "Table") == 0 || strcmp(key, "Max Values Per Block") == 0) {
				// do nothing
			} else if(strcmp(key, "Columns") == 0) {
				// use pointer or value
				// printf("i: %d\n", i);
				meta->column_datas = parseAllColumnMetadata(metadata, &i, size);
				if(meta->column_datas == nullptr){
					return nullptr;
				}
				// printf("i: %d\n", i);
			} else {
				printf("Metadata unknow key: %s\n", key);
				return meta;
			}
			key_len = 0;
			value_len = 0;
		} else if(c == ',' || c == '}') {
			state = 0;
			value[value_len++] = '\0';
			if(strcmp(key, "Table") == 0){
				strcpy(meta->tablename, value);
			} else if (strcmp(key, "Max Values Per Block") == 0) {
				meta->max_values_per_block = stoi(std::string(value));
			} else if (strcmp(key, "Columns") == 0) {
				// do nothing for key == Columns
			} else {
				printf("Metadata unknow key, %s\n", key);
				return meta;
			}
			key_len = 0;
			value_len = 0;
		} else if(c == ' ' || c == '"') {
			// do nothing
			if(c == ' ' && (value_len != 0 || key_len != 0)){
				if(value_len != 0){
					value[value_len++] = c;
				} else {
					key[key_len++] = c;
				}
			}
		} else {
			if(state == 0){
				key[key_len++] = c;	
			} else {
				value[value_len++] = c;
			}
		}
	}

	return meta;
}

static std::map<std::string, ColumnMetadata*>* parseAllColumnMetadata(char* metadata, int* index, int size){
	std::map<std::string, ColumnMetadata*>* meta = new std::map<std::string, ColumnMetadata*>();
	if(meta == NULL){
		printf("new map error\n");
		return NULL;
	}
	std::stack<char> s; // match '{' and '}'

	// skip the ':'
	while(metadata[*index] != ':'){
		(*index) += 1;
	}
	(*index) += 1;

	// parser columns metadata
	int state = 0;
	char key[32];
	char value[32];
	std::fill(key, key+32, 0);
	std::fill(value, value+32, 0);
	int key_len = 0;
	int value_len = 0;

	for(; (*index) < size; (*index) += 1){
		char c = metadata[*index];
		// printf("index is %d, value is %c\n", *index, c);
		if(c == '{'){
			state = 0;
			key_len = 0;
			value_len = 0;
			s.push(c);
		} else if(c == '}' || c == ','){
			state = 0;
			key_len = 0;
			value_len = 0;
			if(c == '}'){
				s.pop();
				if(s.empty()){
					break;
				}
			}
		} else if(c == ':')	{
			state = 1;
			key[key_len++] = '\0';
			// printf("index: %d\n", *index);
			(*meta)[std::string(key)] = parseColumnMetadata(metadata, index, size);
			if((*meta)[std::string(key)] == nullptr){
				return nullptr;
			}
			// printf("index: %d\n", *index);
			key_len = 0;
			value_len = 0;
		} else if(c == ' ' || c == '"') {
			// do nothing
		} else {
			if(state == 0){
				key[key_len++] = c;
			} else {
				value[value_len++] = c;
			}
		}
	}

	return meta;
}

static ColumnMetadata* parseColumnMetadata(char* metadata, int* index, int size){
	ColumnMetadata* meta = (ColumnMetadata*) palloc0(sizeof(ColumnMetadata));
	std::stack<char> s;

	// skip the ':'
	while(metadata[*index] != ':'){
		(*index) += 1;
	}
	(*index) += 1;

	// parser columns metadata
	int state = 0;
	char key[32];
	char value[32];
	std::fill(key, key+32, 0);
	std::fill(value, value+32, 0);
	int key_len = 0;
	int value_len = 0;

	for(; (*index) < size; (*index) += 1){
		char c = metadata[*index];
		if(c == '{'){
			state = 0;
			key_len = 0;
			value_len = 0;
			s.push(c);
		} else if (c == '}' || c == ','){
			state = 0;
			value[value_len++] = '\0';
			if(strcmp(key, "type") == 0){
				strcpy(meta->type, value);
			} else if(strcmp(key, "num_blocks") == 0){
				// printf("key: %s, value %s\n", key, value);
				meta->num_blocks = stoi(std::string(value));
			} else if (strcmp(key, "start_offset") == 0){
				// printf("key: %s, value %s\n", key, value);
				meta->start_offest = stoi(std::string(value));
			} else if(strcmp(key, "block_stats") == 0){
				// do nothing
			} else {
				printf("ColMetadata unknow key %s\n", key);
				return nullptr;
			}
			if(c == '}'){
				s.pop();
				if(s.empty()){
					break;
				}
			}
			key_len = 0;
			value_len = 0;
		} else if (c == ':'){
			state = 1;
			key[key_len++] = '\0';
			if(strcmp(key, "type") == 0 || strcmp(key, "num_blocks") == 0 || strcmp(key, "start_offset") == 0){
				// do nothing
			} else if(strcmp(key, "block_stats") == 0){
				meta->block_stats = parseAllBlockStats(metadata, index, size, std::string(meta->type).c_str());
				if(meta->block_stats == nullptr){
					return nullptr;
				}
			} else {
				printf("ColMetadata unknow key %s\n", key);
				return nullptr;
			}
			key_len = 0;
			value_len = 0;
		} else if (c == ' ' || c == '"') {
			// do nothing
		} else {
			if (state == 0){
				key[key_len++] = c;
			} else {
				value[value_len++] = c;
			}
		}
	}	
	return meta;
}

static std::map<int, BlockStats*>* parseAllBlockStats(char* metadata, int* index, int size, const char* type){
	std::map<int, BlockStats*>* stats = new std::map<int, BlockStats*>();
	std::stack<char> s;		

	// skip the ':'
	while(metadata[*index] != ':'){
		(*index) += 1;
	}
	(*index) += 1;

	// parser columns metadata
	int state = 0;
	char key[32];
	char value[32];
	std::fill(key, key+32, 0);
	std::fill(value, value+32, 0);
	int key_len = 0;
	int value_len = 0;

	for(; (*index) < size; (*index) += 1){
		char c = metadata[*index];
		// printf("index is %d, value is %c\n", *index, c);
		if(c == '{'){
			state = 0;
			key_len = 0;
			value_len = 0;
			s.push(c);
		} else if(c == '}' || c == ','){
			state = 0;
			key_len = 0;
			value_len = 0;
			if(c == '}'){
				s.pop();
				if(s.empty()){
					break;
				}
			}
		} else if(c == ':')	{
			state = 1;
			key[key_len++] = '\0';
			// printf("key: %s\n", key);
			(*stats)[stoi(std::string(key))] = parseBlockStats(metadata, index, size, type);
			if((*stats)[stoi(std::string(key))] == nullptr){
				return nullptr;
			}
			// printf("index: %d\n", *index);
			key_len = 0;
			value_len = 0;
		} else if(c == ' ' || c == '"') {
			// do nothing
		} else {
			if(state == 0){
				key[key_len++] = c;
			} else {
				value[value_len++] = c;
			}
		}
	}
	return stats;
}

static BlockStats* parseBlockStats(char* metadata, int* index, int size, const char* type){
	BlockStats *stats = (BlockStats*) palloc0(sizeof(BlockStats));
	std::stack<char> s; // match '{' and '}'

	// skip the ':'
	while(metadata[*index] != ':'){
		(*index) += 1;
	}
	(*index) += 1;

	// parser columns metadata
	int state = 0;
	char key[32];
	char value[32];
	std::fill(key, key+32, 0);
	std::fill(value, value+32, 0);
	int key_len = 0;
	int value_len = 0;

	for(; (*index) < size; (*index) += 1){
		char c = metadata[*index];
		// printf("index %d, value %c\n", *index, c);
		if(c == '{'){
			state = 0;
			key_len = 0;
			value_len = 0;
			s.push(c);
		} else if (c == '}' || c == ','){
			state = 0;
			value[value_len++] = '\0';
			if(strcmp(key, "num") == 0){
				stats->num = stoi(std::string(value));
			} else if (strcmp(key, "min_len") == 0){
				stats->min_len = stoi(std::string(value));
			} else if (strcmp(key, "max_len") == 0) {
				stats->max_len = stoi(std::string(value));
			} else if (strcmp(key, "min") == 0){
				if(strcmp(type, "str") == 0){
					strcpy(stats->min.s, value);
				} else if (strcmp(type, "float") == 0) {
					stats->min.f = stof(std::string(value));
				} else if (strcmp(type, "int") == 0) {
					stats->min.i = stoi(std::string(value));
				} else {
					printf("BlockStats unknow type %s\n", type);
					return nullptr;
				}
			} else if (strcmp(key, "max") == 0){
				if(strcmp(type, "str") == 0){
					strcpy(stats->max.s, value);
				} else if (strcmp(type, "float") == 0) {
					stats->max.f = stof(std::string(value));
				} else if (strcmp(type, "int") == 0) {
					stats->max.i = stoi(std::string(value));
				} else {
					printf("BlockStats unknow type %s\n", type);
					return nullptr;
				}
			} else {
				printf("BlockStats unknow key %s\n", key);
				return nullptr;
			}
			if(c == '}'){
				s.pop();
				if(s.empty()){
					break;
				}
			}
			key_len = 0;
			value_len = 0;
		} else if (c == ':') {
			state = 1;
			key[key_len++] = '\0';
			if(strcmp(key, "num") == 0 || strcmp(key, "min") == 0 || strcmp(key, "max") == 0){
				// do nothing
			} else if (strcmp(key, "min_len") == 0 || strcmp(key, "max_len") == 0){
				// do nothing
			} else {
				printf("BlockStats unknow key %s\n", key);
				return nullptr;
			}
			key_len = 0;
			value_len = 0;
		} else if(c == ' ' || c == '"') {
			// do nothing
			if(c == ' ' && (value_len != 0 || key_len != 0)){
				if(value_len != 0){
					value[value_len++] = c;
				} else {
					key[key_len++] = c;
				}
			}
		} else {
			if(state == 0){
				key[key_len++] = c;
			} else {
				value[value_len++] = c;
			}
		}
	}	

	return stats;
}

static void estimateCosts(PlannerInfo* root, RelOptInfo* baserel, db721Metadata* fdw_private, Cost* startup_cost, Cost* total_cost){
	Cost run_cost = 0;
	Cost cpu_per_tuple;
	*startup_cost = baserel->baserestrictcost.startup;
	cpu_per_tuple = cpu_tuple_cost * 10 + baserel->baserestrictcost.per_tuple;
	run_cost += cpu_per_tuple * baserel->tuples;
	*total_cost = *startup_cost + run_cost;
}

/*
Table name: Chicken
Max Values Per Block 50000
Columns:
        key: age_weeks
                type: float
                num_blocks: 3
                start_offest: 12000000
                index: 0
                        num 50000
                        min 0.000000
                        max 6.000000
                index: 1
                        num 50000
                        min 0.000000
                        max 156.000000
                index: 2
                        num 20000
                        min 0.000000
                        max 155.979996
        key: farm_name
                type: str
                num_blocks: 3
                start_offest: 480000
                index: 0
                        num 50000
                        min Cheep Birds
                        max Cheep Birds
                        min_len 11
                        max_len 11
                index: 1
                        num 50000
                        min Breakfast Lunch Dinner
                        max Eggstraordinaire
                        min_len 11
                        max_len 22
                index: 2
                        num 20000
                        min Breakfast Lunch Dinner
                        max Incubator
                        min_len 9
                        max_len 22
        key: identifier
                type: int
                num_blocks: 3
                start_offest: 0
                index: 0
                        num 50000
                        min 1
                        max 50000
                index: 1
                        num 50000
                        min 50001
                        max 100000
                index: 2
                        num 20000
                        min 100001
                        max 120000
        key: notes
                type: str
                num_blocks: 3
                start_offest: 12960000
                index: 0
                        num 50000
                        min WOODY
                        max WOODY
                        min_len 5
                        max_len 5
                index: 1
                        num 50000
                        min
                        max WOODY
                        min_len 0
                        max_len 5
                index: 2
                        num 20000
                        min
                        max WOODY
                        min_len 0
                        max_len 5
        key: sex
                type: str
                num_blocks: 3
                start_offest: 8160000
                index: 0
                        num 50000
                        min FEMALE
                        max MALE
                        min_len 4
                        max_len 6
                index: 1
                        num 50000
                        min FEMALE
                        max MALE
                        min_len 4
                        max_len 6
                index: 2
                        num 20000
                        min FEMALE
                        max MALE
                        min_len 4
                        max_len 6
        key: weight_g
                type: float
                num_blocks: 3
                start_offest: 12480000
                index: 0
                        num 50000
                        min 357.757324
                        max 3131.530762
                index: 1
                        num 50000
                        min 42.779999
                        max 3091.312988
                index: 2
                        num 20000
                        min 40.220001
                        max 3125.401367
        key: weight_model
                type: str
                num_blocks: 3
                start_offest: 4320000
                index: 0
                        num 50000
                        min GOMPERTZ
                        max WEIBULL
                        min_len 3
                        max_len 8
                index: 1
                        num 50000
                        min GOMPERTZ
                        max WEIBULL
                        min_len 3
                        max_len 8
                index: 2
                        num 20000
                        min GOMPERTZ
                        max WEIBULL
                        min_len 3
                        max_len 8
*/

/*
{"Table": "Farm", 
"Columns": {"farm_name": 
				{"type": "str", 
				"block_stats": {"0": {"num": 6, "min": "Breakfast Lunch Dinner", "max": "Incubator", "min_len": 9, "max_len": 22}}, 
				"num_blocks": 1, 
				"start_offset": 0}, 
			"min_age_weeks": 
				{"type": "float", 
				"block_stats": {"0": {"num": 6, "min": 0, "max": 52}}, 
				"num_blocks": 1, 
				"start_offset": 192}, 
			"max_age_weeks": 
				{"type": "float", 
				"block_stats": {"0": {"num": 6, "min": 2, "max": 156}}, 
				"num_blocks": 1, 
				"start_offset": 216}}, 
"Max Values Per Block": 50000}
*/