#ifndef _H_SONGLH_FFRINSTRUMENT
#define _H_SONGLH_FFRINSTRUMENT


#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;
using namespace llvm_Commons;

struct FFRInstrument : public ModulePass
{
	static char ID;
	FFRInstrument();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

private:
	//hooks
	void SetupTypes(Module * pModule);
	void SetupStruct(Module * pModule);
	void SetupConstants(Module * pModule);
	void SetupHooks(Module * pModule);
	void SetupGlobals(Module * pModule);


private:
	//void ParseMonitoredInstFile(string & sFileName, Module * pModule);
	void RemapInstruction(Instruction *I, ValueToValueMapTy &VMap);
	BinaryOperator * CreateIfElseBlock(Function * pFunction, Module * pModule, vector<BasicBlock *> & vecAdd);
	void CloneFunction(Function * pFunction, vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap);
	void InstrumentMain(Module * pModule);
	void CollectInstrumentedInst(Function * pFunction, vector<LoadInst *> & vecLoad, vector<MemCpyInst *> & vecMem, vector<Instruction *>  & vecInst);
	void AddHooksToClonedFunction(BinaryOperator * pAdd, vector<BasicBlock *> & vecAdd, int iFunctionID, vector<LoadInst *> & vecLoad, 
		vector<MemCpyInst *> & vecMem, vector<Instruction *> & vecInst, ValueToValueMapTy & VMap );


	void CloneFunctionCalled(Function * pRootFunction, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping);


	void InlineHookPara(Argument * pArg, Instruction * II, BinaryOperator * pAdd, int FunctionID);
	void InlineHookLoad(LoadInst * pLoad, BinaryOperator * pAdd, int InstID);
	void InlineHookInst(Instruction * pI, Instruction * II, BinaryOperator * pAdd);
	void InlineHookMem(MemTransferInst * pMem, Instruction * II, BinaryOperator * pAdd);

	void SplitReturnBlock(Function * pFunction);

private:
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
	StructType * struct_stMemRecord;

	StructType * struct_stLogRecord;
	StructType * union_anon_CPI;

	PointerType * PT_struct_stLogRecord;



//constants
	ConstantInt * ConstantInt0;
	ConstantInt * ConstantInt1;
	ConstantInt * ConstantInt2;
	ConstantInt * ConstantInt3;
	ConstantInt * ConstantInt4;
	ConstantInt * ConstantInt10;
	ConstantInt * ConstantInt32;

	ConstantInt * ConstantLong0;
	ConstantInt * ConstantLong1;
	ConstantInt * ConstantLong32;
	ConstantInt * ConstantLong40;

	ConstantInt * ConstantIntFalse;

	ConstantInt * ConstantInt_1;
	ConstantPointerNull * ConstantNULL;

//function
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
	GlobalVariable * PC_SAMPLE_RATE;
	GlobalVariable * CURRENT_SAMPLE;
	GlobalVariable * Record_CPI;
	GlobalVariable * pcBuffer_CPI;
	GlobalVariable * iRecordSize_CPI;
	GlobalVariable * iBufferIndex_CPI;

	Constant * SAMPLE_RATE_ptr;
	Constant * Output_Format_String;


private:
	map<Function *, LibraryFunctionType>  LibraryTypeMapping;
	set<int> setInstIndex;
	vector<pair<Function *, int> > vecParaIndex;


};

#endif


