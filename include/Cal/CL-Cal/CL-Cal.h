#ifndef _H_SONGLH_CL_CAL
#define _H_SONGLH_CL_CAL


#include "llvm/Pass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/DataLayout.h"
#include "llvm-Commons/Config/Config.h"

#include <string>
#include <set>
#include <map>
#include <vector>

using namespace llvm;
using namespace std;
using namespace llvm_Commons;


typedef struct stLoadRecord {
	unsigned uInstructionID;
	long LoadAddress;
	long LoadValue;
} LoadRecord;

typedef struct stStoreRecord {
	unsigned uInstructionID;
	long StoreAddress;
	long StoreValue;
} StoreRecord;

typedef struct stInstRecord {
	unsigned uInstructionID;
	long Value;
} InstRecord;

typedef struct stParaRecord {
	unsigned uValueID;
	long Value;
} ParaRecord;

typedef struct stDelimiterRecord {
	long numExecution;
} DelimiterRecord;

typedef struct stMemRecord {
	unsigned uInstructionID;
	long uLength;
} MemRecord;

typedef struct stLogRecord {
	enum LogRecordType
	{
		Load,
		Store,
		Inst,
		Para,
		Delimiter,
		Mem
	};

	LogRecordType RecordType;
	union {
		LoadRecord LR;
		StoreRecord SR;
		InstRecord IR;
		ParaRecord PR;
		DelimiterRecord DR;
		MemRecord MR;
	};

} LogRecord;


struct CLCAL : public ModulePass
{
	static char ID;
	CLCAL();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

private:

	//parser
	void ParseInstFile(Function * pInnerFunction, Module * pModule);
	void ParseTraceFile(vector<vector<LogRecord> > & vecLogRecord);
	void FreeMemBuffer();

	//not be used
	void CalMaxMinValue(vector<vector<LogRecord> > & vecLogRecord);
	void CalMeanSD(vector<vector<LogRecord> > & vecLogRecord);

	void BuildIDInstMapping(Function * pFunction);

	void CollectMonitoredValue(set<Value *> & setMonitoredValue);
	void DecodeOneInstance(vector<LogRecord> & Instance, map<int, vector<LogRecord> > & IDValueMapping, map<int, LogRecord > & ArgValueMapping, 
							map<int, vector<char> > & IDMemMapping);
	void CompMemSequence(map<Value *, double> & ValueScoreMapping);
	void CompValueSequence(map<Value *, double> & ValueScoreMapping);
	void CompSkipLoad(map<Value *, double > & ValueScoreMapping, set<Value *> & setMonitoredValue);
	bool CompIterativeStart(Value * pValue, long Value1, long Value2, map<Value*, double>  & ValueScoreMapping);
	int CompInstancePair(vector<LogRecord> & InstanceA, vector<LogRecord> & InstanceB);

	bool CanSkipThisValue(Value * pValue);
	

private:
	//Analysis
	ScalarEvolution * SE;
	DataLayout * DL;


	map<Function *, LibraryFunctionType>  LibraryTypeMapping;
	MonitoredElement MonitoredElems;

	long lTotalMemLength;
	char * pMemBuffer;
	map<pair<long, long>, char *> IndexPonterMapping;

	//id value mappint
	map<int, Instruction *> IDInstMapping;
	map<int, Argument *> IDArgMapping;

	map<LoadInst *, vector<set<Value * > > > PossibleSkipLoadInfoMapping;

	//current loop
	LoopInfo * pLI;
	Loop * pLoop;

	//data structure for one pair
	map<int, vector<LogRecord> > IDValueMapping1;
	map<int, LogRecord > ArgValueMapping1;
	map<int, vector<char> > IDMemMapping1;

	map<int, vector<LogRecord> > IDValueMapping2;
	map<int, LogRecord > ArgValueMapping2;
	map<int, vector<char> > IDMemMapping2;

	set<size_t> setLength1;
	set<size_t> setLength2;

	//not used
	map<Value *, pair<long, long> > ValueMinMaxMapping;
	map<Value *, double> ValueMeanMapping;
	map<Value *, double> ValueSDMapping;	

};


#endif

