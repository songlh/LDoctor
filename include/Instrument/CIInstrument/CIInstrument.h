#ifndef _H_SONGLH_CIINSTRUMENT
#define _H_SONGLH_CIINSTRUMENT



#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Target/TargetLibraryInfo.h"

#include "llvm-Commons/Config/Config.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;
using namespace llvm_Commons;


struct CrossInterationInstrument :  public ModulePass
{
	static char ID;
	CrossInterationInstrument();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

private:
	void SetupTypes(Module * pModule); 
	void SetupConstants(Module * pModule);
	void SetupStruct(Module * pModule);
	void SetupHooks(Module * pModule);
	void SetupGlobals(Module * pModule);

	void InlineHookLoad(LoadInst * pLoad, Instruction * II);
	void InlineHookInst(Instruction * pI, Instruction * II);
	void InlineHookDelimit(Instruction * II);
	void InlineHookMem(MemTransferInst * pMem, Instruction * II);

	void InstrumentPreHeader(Loop * pLoop);
	void SplitHeader(Loop * pLoop);
	void InstrumentNewHeader();
	void UpdateHeader(set<BasicBlock *> & setCloned, ValueToValueMapTy & VMap);
	void UpdateExitBlock(Function * pFunction, set<BasicBlock *> & setExitBlocks, set<BasicBlock *> & setCloned, ValueToValueMapTy & VMap);

	void RemapInstruction(Instruction *I, ValueToValueMapTy &VMap);
	void DoClone(Function * pFunction, vector<BasicBlock *> & ToClone, ValueToValueMapTy & VMap, set<BasicBlock *> & setCloned);
	void AddHooksToLoop(vector<Instruction *> & vecInst, ValueToValueMapTy & VMap, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping);

	void CloneLoopBody(Loop * pLoop, vector<Instruction *> & vecInst);

	bool pointerInvalidatedByLoop(Value *V, uint64_t Size, const MDNode *TBAAInfo);
	bool isGuaranteedToExecute(Instruction &Inst);
	bool canSinkOrHoistInst(Instruction &I);
	void CollectInstrumentedInst(Loop * pLoop, vector<Instruction *> & vecInst);

	void CloneFunctionCalled(set<BasicBlock *> & setBlocksInLoop, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping);
	void InstrumentMain(Module * pModule);





private:
	map<Function *, LibraryFunctionType>  LibraryTypeMapping;
	set<int> setInstID;
	vector<pair<Function *, int> > vecParaID;


//scalar type
	IntegerType * CharType ;
	IntegerType * BoolType ;
	IntegerType * LongType ;
	IntegerType * IntType  ;
	PointerType * CharStarType ;
	PointerType * LongStarType;

	Type * VoidType ;
	Type * VoidPointerType;

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

//struct type 
	StructType * struct_stLoadRecord;
	StructType * struct_stStoreRecord;
	StructType * struct_stInstRecord;
	StructType * struct_stParaRecord;
	StructType * struct_stDelimiterRecord;
	StructType * struct_stLogRecord;
	StructType * struct_stMemRecord;
	StructType * union_anon_CPI;

//Function
	Function * getenv;
	Function * function_atoi;
	Function * printf;
	Function * geo;
	Function * func_llvm_memcpy;
	Function * InitHooks;
	Function * FinalizeMemHooks;

//global
	GlobalVariable * SAMPLE_RATE;
	GlobalVariable * numGlobalCounter;
	GlobalVariable * numInstances;
	GlobalVariable * PC_SAMPLE_RATE;
	GlobalVariable * CURRENT_SAMPLE;
	GlobalVariable * Record_CPI;
	GlobalVariable * pcBuffer_CPI;
	GlobalVariable * iRecordSize_CPI;
	GlobalVariable * iBufferIndex_CPI;

	Constant * SAMPLE_RATE_ptr;
	Constant * Output_Format_String;

//basicblock
	BasicBlock * pPreHeader;
	BasicBlock * pHeader;
	BasicBlock * pOldHeader;
	BasicBlock * pNewHeader;

//Instruction
	BinaryOperator * pAddCurrentInstances;
	LoadInst * pLoadnumGlobalCounter;
	LoadInst * pLoadCURRENT_SAMPLE;
	CastInst * pCastCURRENT_SAMPLE;
	BinaryOperator * pAddnumGlobalCounter;

	AliasSetTracker * CurAST;
	bool MayThrow;

	DataLayout * DL;
	AliasAnalysis * AA;
	//TargetLibraryInfo *TLI;

};

#endif


