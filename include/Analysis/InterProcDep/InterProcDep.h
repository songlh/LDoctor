#ifndef _H_SONGLH_INTERPROCDEP
#define _H_SONGLH_INTERPROCDEP

#include <string>
#include <set>
#include <map>

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"


using namespace std;
using namespace llvm;


//namespace llvm_Commons
//{


enum MemoryObjectType {
	MO_LOCAL,
	MO_INPUT,
	MO_INVARIANT,
	MO_OTHER
};

struct InterProcDep: public ModulePass
{
	static char ID;
	InterProcDep();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module &M);
	virtual void print(raw_ostream &O, const Module *M) const;	


public:
	void InitlizeFuncSet();
	void InitlizeStartFunctionSet(set<Function *> & StartingSet);
	void IsRecursiveFunction(Function * pFunction, map<Function *, int> & FuncMarkMapping, vector<pair<Function *, Function *> > & vecBackEdge );
	void DetectRecursiveFunctionCall(set<Function *> & RecursiveCalls, set<Function *> & nonRecursiveCalls);

	void BuildCallerCalleeMapping(Function * pFunction);
	void DumpCallerCalleeMapping(Function * pFunction);
	void AnalyzeMemReadInst(Function * pFunction);
	int CountLocalLoad(Function * pFunction);
	void CollectSideEffectInst(Function * pFunction, set<Instruction *> & setCallSite, set<StoreInst *> & setStore, set<MemIntrinsic *> & setMemIntrics);


	void NoneIntraProcedureDependenceAnalysis(Function * pFunction, Function * pStart);
	void BottomUpDependenceAnalysis(Function * pFunction, Function * pStart);
	void TopDownDependenceAnalysis(Function * pFunction, Function * pStart);

	void NoneRecursiveDependenceAnalysis(Function * pFunction );

	


	void InterProcDependenceAnalysis();


public:
	set<Function *> StartFunctionSet;
	map<Function *, map<Function *, set<Function *> > > StartCallerCalleeMappingMapping;
	map<Function *, map<Function *, set<Instruction *> > > StartCallerCallSiteMappingMapping;
	map<Function *, map<Function *, set<Function *> > > StartCalleeCallerMappingMapping;
	map<Function *, map<Function *, set<Instruction *> > > StartCalleeCallSiteMappingMapping;

	map<Function *, map<LoadInst *, MemoryObjectType > > StartLoadTypeMappingMapping;
	map<Function *, map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> > >  StartMemTypeMappingMapping;

	map<Function *, set<StoreInst *> > StartEffectStoreMapping;
	map<Function *, set<MemIntrinsic *> > StartEffectMemMapping;
	map<Function *, set<Instruction *> > StartLibraryCallMapping;





	map<Function *, map<Function *, map<Instruction *, set<Value *> > > > StartFuncValueDependenceMappingMappingMapping;
	map<Function *, map<Function *, map<Instruction *, set<Instruction *> > > > StartFuncDependenceValueMappingMappingMapping;
	map<Function *, map<Function *, map<Instruction *, set<Instruction *> > > > StartFuncInstProcessedInstMappingMappingMapping;
	map<Function *, map<Function *, map<Instruction *, set<Value *> > > > StartFuncCallSiteCDependenceMappingMappingMapping;

	map<Function *, map<Function *, map<Argument *, set<Value * > > > > StartFuncArgDependenceMappingMappingMapping;


private:
	DataLayout * pDL;


	set<string> setPureFunctions;
	set<string> setMemoryAllocFunctions;
	set<string> setFileIO;
	set<string> setLibraryFunctions;

	//load and memintrisc dependence
	map<LoadInst *, set<Instruction *> > LoadDependentInstMapping;
	map<MemTransferInst *, set<Instruction *> > MemInstDependentInstMapping;

};



//}

#endif



