// If you choose to use C++, read this very carefully:
// https://www.postgresql.org/docs/15/xfunc-c.html#EXTEND-CPP

#include "dog.h"
#include <map>
#include <stack>
#include <iostream>

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
	std::map<std::string, BlockStats*>* block_stats;
} ColumnMetadata;

typedef struct db721Metadata {
	char tablename[32];
	int max_values_per_block;
	std::map<std::string, ColumnMetadata*>* column_datas;
} db721Metadata;

typedef struct db721ExecutionState {
	db721Metadata* meta;
	char* filename;
	FILE* table;
	int index;
} db721ExecutionState;

static db721FdwOptions* db721GetOptions(Oid foreigntableid);
static db721Metadata* db721GetMetadata(db721FdwOptions* options);
static db721Metadata* parserMetadata(char* metadata, int size);
static std::map<std::string, ColumnMetadata*>* parseAllColumnMetadata(char* metadata, int* index, int size);
static ColumnMetadata* parseColumnMetadata(char* metadata, int* index, int size);
static std::map<std::string, BlockStats*>* parseAllBlockStats(char* metadata, int* index, int size, const char* type);
static BlockStats* parseBlockStats(char* metadata, int* index, int size, const char* type);
// static void printfMetadata(db721Metadata* meta);
static void estimateCosts(PlannerInfo* root, RelOptInfo* baserel, db721Metadata* fdw_private, Cost* startup_cost, Cost* total_cost);
static db721ExecutionState* create_db721ExectionState(db721Metadata* meta, char* filename);
static bool fetchTupleAtIndex(db721ExecutionState* festate, int index, TupleTableSlot* tuple);	
static int getInt4(FILE* table, int offest, bool* ok);
static float getFloat4(FILE* table, int offest, bool *ok);
static char* getString32(FILE* table, int offest, bool *ok);

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

	// printf("tuples number is %lf\n", baserel->tuples);
	// printf("rows number is %lf\n", baserel->rows);
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
	List *params = NIL;
	scan_clauses = extract_actual_clauses(scan_clauses, false);

	db721FdwOptions* options = db721GetOptions(foreigntableid);
	params = lappend(params, baserel->fdw_private);
	params = lappend(params, makeString(options->filename));

	return make_foreignscan(tlist,
							scan_clauses,
							baserel->relid,
							NIL,
							params,
							NIL,
							NIL,
							outer_plan);
}

extern "C" void db721_BeginForeignScan(ForeignScanState *node, int eflags) {
	db721ExecutionState *festate = NULL;
	db721Metadata* meta = NULL;
	char* filename = NULL;
	ForeignScan *plan = (ForeignScan*) node->ss.ps.plan;
	List *fdw_private = plan->fdw_private;
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
		}
		++i;		
	}

	festate = create_db721ExectionState(meta, filename);
	node->fdw_state = festate;
}

extern "C" TupleTableSlot *db721_IterateForeignScan(ForeignScanState *node) {
	db721ExecutionState* festate = (db721ExecutionState*) node->fdw_state;
	TupleTableSlot *tuple = node->ss.ss_ScanTupleSlot;
	std::string error;

	// only return target value, we can use pushdown
	// ForeignScan *plan = (ForeignScan*) node->ss.ps.plan;
	// List *tlist = plan->fdw_scan_tlist; // for SELECT attribute_name FROM table_name;

	try{
		bool flag = fetchTupleAtIndex(festate, festate->index, tuple);	
		if(!flag){
			return NULL;
		}
	} catch (std::exception &e) {
		error = e.what();
	}
	if(!error.empty()){
		printf("catch error: %s\n", error.c_str());
	}

 	return tuple;
}

extern "C" void db721_ReScanForeignScan(ForeignScanState *node) {
	db721ExecutionState* festate = (db721ExecutionState*) node->fdw_state;
	festate->index = 1;
}

extern "C" void db721_EndForeignScan(ForeignScanState *node) {
	/*
	 * delete db721Metadata memory that we alloc in db721_GetForeignRelSize
	 */
	db721ExecutionState* festate = (db721ExecutionState*) node->fdw_state;
	FreeFile(festate->table);
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

/* 
 * parser db721 meta data
 */
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

static std::map<std::string, BlockStats*>* parseAllBlockStats(char* metadata, int* index, int size, const char* type){
	std::map<std::string, BlockStats*>* stats = new std::map<std::string, BlockStats*>();
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
			// printf("index: %d\n", *index);
			(*stats)[std::string(key)] = parseBlockStats(metadata, index, size, type);
			if((*stats)[std::string(key)] == nullptr){
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

static db721ExecutionState* create_db721ExectionState(db721Metadata* meta, char* filename){
	db721ExecutionState *state = (db721ExecutionState*) palloc0(sizeof(db721ExecutionState));

	FILE* tableFile = AllocateFile(filename, PG_BINARY_R);
	if(tableFile == NULL){
		printf("open file error\n");
		return nullptr;
	}

	state->meta = meta;
	state->filename = filename;
	state->index = 0;
	state->table = tableFile;

	return state;
}


static bool fetchTupleAtIndex(db721ExecutionState* festate, int index, TupleTableSlot* tuple){
	int total_tuples = 0; // record tuple number
	for(auto it : *(festate->meta->column_datas)){
		for(auto it2 : *(it.second->block_stats)){
			total_tuples += it2.second->num;
		}
		break;
	}
	if(total_tuples <= index) {
		return false;
	}
	// printf("total_tuples is %d\n", total_tuples);

	TupleDesc tupleDescriptor = tuple->tts_tupleDescriptor;
	// tuple->tts_isnull[0] = true; // make index 0 attribute to null

	ExecClearTuple(tuple);
	for(int i = 0; i < tupleDescriptor->natts; i++){
		char* name = tupleDescriptor->attrs[i].attname.data; // get attribute name
		// printf("attribute name is %s\n", name);
		auto it = (*festate->meta->column_datas)[std::string(name)];
		char* type = it->type;
		int start_offest = it->start_offest;
		// int num_blocks = it->num_blocks; // for larget table

		bool ok = true;
		if(strcmp(type, "str") == 0){
			char* str = getString32(festate->table, start_offest+index*32, &ok);
			tuple->tts_values[i] = CStringGetDatum(str);
		} else if(strcmp(type, "int") == 0){
			int integer = getInt4(festate->table, start_offest+index*4, &ok);
			tuple->tts_values[i] = Int32GetDatum(integer);
		} else if(strcmp(type, "float") == 0){
			float f = getFloat4(festate->table, start_offest+index*4, &ok);
			tuple->tts_values[i] = Float4GetDatum(f);
		} else {
			printf("error type in fetchTupleAtIndex, type: %s\n", type);
			return false;
		}
		if(!ok){
			return false;
		}
	}
	ExecStoreVirtualTuple(tuple);

	festate->index += 1;
	return true;
}

static int getInt4(FILE* table, int offest, bool *ok){
	int i;
	if(fseek(table, offest, SEEK_SET) != 0){
		printf("seek to start offest int error\n");
		*ok = false;
	}
	if(fread(&i, 4, 1, table) != 1){
		printf("read int fail\n");
		*ok = false;
	}
	// printf("the int is %d\n", i);
	return i;
}

static float getFloat4(FILE* table, int offest, bool *ok){
	float f;
	if(fseek(table, offest, SEEK_SET) != 0){
		printf("seek to start offest float error\n");
		*ok = false;
	}
	if(fread(&f, 4, 1, table) != 1){
		printf("read float fail\n");
		*ok = false;
	}
	// printf("the float is %f\n", f);
	return f;
}

static char* getString32(FILE* table, int offest, bool *ok){
	char *s = (char*) palloc0(sizeof(char)*33);
	/*
	 * why postgresql put a string in front of string type ?
	 * the first char maybe a flag for compress etc.
	 * how can i know the frist is what
	 */
	s[0] = '#'; 	
	if(fseek(table, offest,SEEK_SET) != 0){
		printf("seek to start offest str error\n");
		*ok = false;
	}
	if(fread(s+1, 32, 1, table) != 1){
		printf("read str fail\n");
		*ok = false;
	}
	// printf("the str is %s\n", s);
	return s;
}

// static void printfMetadata(db721Metadata* meta){
// 	printf("Table name: %s\n", meta->tablename);
// 	printf("Max Values Per Block %d\n", meta->max_values_per_block);
// 	printf("Columns: \n");
// 	for(auto iter : *(meta->column_datas)){
// 		printf("\tkey: %s\n", iter.first.c_str());
// 		printf("\t\ttype: %s\n", iter.second->type);
// 		printf("\t\tnum_blocks: %d\n", iter.second->num_blocks);
// 		printf("\t\tstart_offest: %d\n", iter.second->start_offest);
// 		for(auto iter2 : *(iter.second->block_stats)){
// 			printf("\t\tindex: %s\n", iter2.first.c_str());
// 			if(strcmp(iter.second->type, "str") == 0){
// 				printf("\t\t\tnum %d\n", iter2.second->num);
// 				printf("\t\t\tmin %s\n", iter2.second->min.s);
// 				printf("\t\t\tmax %s\n", iter2.second->max.s);
// 				printf("\t\t\tmin_len %d\n", iter2.second->min_len);
// 				printf("\t\t\tmax_len %d\n", iter2.second->max_len);
// 			} else if(strcmp(iter.second->type, "float") == 0){
// 				printf("\t\t\tnum %d\n", iter2.second->num);
// 				printf("\t\t\tmin %f\n", iter2.second->min.f);
// 				printf("\t\t\tmax %f\n", iter2.second->max.f);
// 			} else if(strcmp(iter.second->type, "int") == 0){
// 				printf("\t\t\tnum %d\n", iter2.second->num);
// 				printf("\t\t\tmin %d\n", iter2.second->min.i);
// 				printf("\t\t\tmax %d\n", iter2.second->max.i);
// 			}
// 		}
// 	}
// }

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