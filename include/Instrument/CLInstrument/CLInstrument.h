#ifndef _H_SONGLH_CLINSTRUMENT
#define _H_SONGLH_CLINSTRUMENT

#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;

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

//
	BasicBlock * SearchPostDominatorForLoop(Loop * pLoop,  PostDominatorTree * pPDT );
	void CreateIfElseIfBlock(Loop * pInnerLoop, BasicBlock * pPostDominator, vector<BasicBlock *> & vecCondition);
	void CloneInnerLoop(Loop * pLoop, BasicBlock * pPostDominator, vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap);
	void RemapInstruction(Instruction *I, ValueToValueMapTy &VMap);
	void ParseMonitoredInstFile(string & sFileName, Module * pModule);
	void CollectInstrumentedInst(set<int> & setIndex, Loop * pLoop, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecOut );
	void AddHooksToInnerLoop(vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecOut);

	void InstrumentInnerLoop(Loop * pLoop, PostDominatorTree * PDT);
	void InstrumentOuterLoop(Loop * pLoop);
	void InstrumentMain(Module * pModule);

	void InlineHookPara(Argument * pArg, Instruction * II);
	void InlineHookDelimit(Instruction * II);
	void InlineHookInst(Instruction * pI, Instruction * II);
	void InlineHookLoad(LoadInst * pLoad);

//	
	set<int> setInstIndex;
	vector<pair<Function *, int> > vecParaIndex;
	bool bGivenOuterLoop;

//
	Loop * pOuterLoop;

//type
	IntegerType *CharType ;
	IntegerType *BoolType ;
	IntegerType *LongType ;
	IntegerType *IntType  ;
	PointerType *CharStarType ;
	Type * VoidType ;
	Type * VoidPointerType;

//type
	StructType * struct_stLoadRecord;
	StructType * struct_stStoreRecord;
	StructType * struct_stInstRecord;
	StructType * struct_stParaRecord;
	StructType * struct_stDelimiterRecord;
	StructType * struct_stLogRecord;
	StructType * union_anon_CPI;

//constants
	ConstantInt * ConstantInt0;
	ConstantInt * ConstantInt1;
	ConstantInt * ConstantInt2;
	ConstantInt * ConstantInt3;
	ConstantInt * ConstantInt4;
	ConstantInt * ConstantInt10;
	ConstantInt * ConstantInt32;

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
	
	



};

#endif

