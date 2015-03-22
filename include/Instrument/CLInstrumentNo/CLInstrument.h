#ifndef _H_SONGLH_CLINSTRUMENTNO
#define _H_SONGLH_CLINSTRUMENTNO

#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include "llvm-Commons/Config/Config.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;
using namespace llvm_Commons;

struct CrossLoopInstrument : public ModulePass
{
	static char ID;
	CrossLoopInstrument();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

//hooks
	void SetupTypes(Module * );
	void SetupHooks(Module * );
	void SetupConstants(Module * );
	void SetupGlobals(Module * );
	void SetupStruct(Module *);

	BasicBlock * SearchPostDominatorForLoop(Loop * pLoop,  PostDominatorTree * pPDT );
	void CreateIfElseIfBlock(Loop * pInnerLoop, vector<BasicBlock *> & vecCondition);
	void CloneInnerLoop(Loop * pLoop,  ValueToValueMapTy & VMap);
	
	void CloneFunctionCalled(set<BasicBlock *> & setBlocksInLoop, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping);


	void RemapInstruction(Instruction *I, ValueToValueMapTy &VMap);

	void CollectInstrumentedInst(set<int> & setIndex, Loop * pLoop, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecIn, vector<Instruction *> & vecOut, vector<MemTransferInst *> & vecMem );
	void AddHooksToInnerLoop(Loop * pLoop, ValueToValueMapTy & VMap, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecIn, vector<Instruction *> & vecOut, vector<MemTransferInst *> & vecMem);

	void InstrumentInnerLoop(Loop * pLoop, PostDominatorTree * PDT);
	void InstrumentOuterLoop(Loop * pLoop);
	void InstrumentMain(Module * pModule);

	void InlineHookPara(Argument * pArg, Instruction * II);
	void InlineHookDelimit(Instruction * II);
	void InlineHookInst(Instruction * pI, Instruction * II);
	void InlineHookLoad(LoadInst * pLoad);
	void InlineHookMem(MemTransferInst * pMem, Instruction * II);

	void AddHooksToSkippableLoad(set<LoadInst *> & setLoad, LoopInfo * pLI, ValueToValueMapTy &VMap, set<Value *> & setMonitoredValue, BasicBlock * pCondition2);

	void ParseInstFile(Function * pInnerFunction, Module * pModule);

//	
	map<Function *, LibraryFunctionType>  LibraryTypeMapping;

	bool bGivenOuterLoop;

	MonitoredElement MonitoredElems;

	map<LoadInst *, vector<set<Value * > > > PossibleSkipLoadInfoMapping;
	//map<LoadInst *, Value *> PossibleSkipLoadTripCounter;

//
	Loop * pOuterLoop;

//type
	IntegerType *CharType ;
	IntegerType *BoolType ;
	IntegerType *LongType ;
	IntegerType *IntType  ;
	PointerType *CharStarType ;
	PointerType *LongStarType;

	Type * VoidType ;
	Type * VoidPointerType;

//type
	StructType * struct_stLoadRecord;
	StructType * struct_stStoreRecord;
	StructType * struct_stInstRecord;
	StructType * struct_stParaRecord;
	StructType * struct_stDelimiterRecord;
	StructType * struct_stLogRecord;

	StructType * struct_stMemRecord;
	StructType * union_anon_CPI;

	Type * PT_struct_stLogRecord;

//constants
	ConstantInt * ConstantInt0;
	ConstantInt * ConstantInt1;
	ConstantInt * ConstantInt2;
	ConstantInt * ConstantInt3;
	ConstantInt * ConstantInt4;
	ConstantInt * ConstantInt5;
	ConstantInt * ConstantInt10;
	ConstantInt * ConstantInt32;

	ConstantInt * ConstantLong0;
	ConstantInt * ConstantLong1;
	ConstantInt * ConstantLong32;
	ConstantInt * ConstantLong40;

	ConstantInt * ConstantIntFalse;

	ConstantInt * ConstantInt_1;
	ConstantPointerNull * ConstantNULL;


//Function
	Function * getenv;
	Function * function_atoi;
	Function * printf;
	Function * geo;
	Function * func_llvm_memcpy;


	Function * HookStore;
	Function * HookLoad;
	Function * HookPara;
	Function * HookInst;
	Function * HookDelimiter;
	Function * InitHooks;
	Function * FinalizeMemHooks;

//global
	GlobalVariable * SAMPLE_RATE;
	GlobalVariable * numGlobalCounter;
	GlobalVariable * PC_SAMPLE_RATE;
	GlobalVariable * CURRENT_SAMPLE;
	GlobalVariable * Record_CPI;
	GlobalVariable * pcBuffer_CPI;
	GlobalVariable * iRecordSize_CPI;
	GlobalVariable * iBufferIndex_CPI;

	Constant * SAMPLE_RATE_ptr;
	Constant * Output_Format_String;
	
/*	
	set<string> setPureFunctions;
	set<string> setMemoryAllocFunctions;
	set<string> setTransparentFunctions;
	set<string> setFileIO;
	set<string> setStoppedFunctions;
	set<string> setLibraryFunctions;

*/
};

#endif

