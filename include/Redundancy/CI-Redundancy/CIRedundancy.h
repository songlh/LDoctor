#ifndef _H_SONGLH_CI_REDUNDANCY
#define _H_SONGLH_CI_REDUNDANCY


#include <vector>
#include <map>
#include <set>
#include <string>

#include "llvm/Pass.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DataLayout.h"


using namespace std;
using namespace llvm;
using namespace llvm_Commons;

enum MemoryObjectType {
	MO_LOCAL,
	MO_INPUT,
	MO_INVARIANT,
	MO_OTHER
};


struct CrossIterationRedundancy : public ModulePass
{

	static char ID;
	CrossIterationRedundancy();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

private:
	//confirmed
	void InitializePureFunctionSet();
	void InitializeMemoryAllocFunctionSet();
	void BuildCallerCalleeMapping(Function * pFunction);

	//InfeasiblePath
	void DependenceAnalysisInfeasiblePath(Function * pFunction);


	//top-down
	void IntraProcedureDependenceAnalysis(Function * pFunction);
	void BottomUpDependenceAnalysis(Function * pFunction);
	void TopDownDependenceAnalysis(Function * pFunction);



	//
	void AnalyzeMemReadInst(Function * pFunction);
	int CountLocalLoad();
	void CollectSideEffectInst(set<Instruction *> & setCallSite, set<StoreInst *> & setStore, set<MemIntrinsic *> & setMemIntrics);
	void AddDependence(Value * pValue, Value * pDependence, set<Value *> & setProcessedInst, set<Value *> & setDependence);


	

	void DependenceAnalysis(Function * pFunction);
	
	//Debug
	void DumpInstructionInfo(Function * pFunction, unsigned uLine);
	

private:
	//confirmed
	map<Function *, set<Function *> > CallerCalleeMapping;
	map<Function *, set<Instruction *> > CallerCallSiteMapping;
	
	map<Function *, set<Function *> >    CalleeCallerMapping;
	map<Function *, set<Instruction *> > CalleeCallSiteMapping;

	map<LoadInst *, MemoryObjectType> LoadTypeMapping;
	map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> > MemTypeMapping;

	map<Function *, map<LoadInst *, MemoryObjectType> > FuncLoadTypeMapping;
	map<Function *, map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> > > FuncMemTypeMapping;

	//load and memintrisc dependence
	map<LoadInst *, set<Instruction *> > LoadDependentInstMapping;
	map<MemTransferInst *, set<Instruction *> > MemInstDependentInstMapping;



	//scope invariant global mapping
	//map<set<Function *>, set<Value *> > ScopeInvariantValueMapping;

	//function without side effects and only depend on inputs
	set<string> setPureFunctions;
	set<string> setMemoryAllocFunctions;

	//infeasible path
	map<Value *, set<Value *> > ValueDependenceMapping;
	map<Value *, set<Value *> > DependenceValueMapping;


	//top-down
	map<Function *, map<Instruction *, set<Value *> > > FuncValueDependenceMappingMapping;
	map<Function *, map<Instruction *, set<Instruction *> > > FuncDependenceValueMappingMapping;
	map<Function *, map<Instruction *, set<Instruction *> > > FuncInstProcessedInstMappingMapping;
	map<Function *, map<Instruction *, set<Value *> > >  FuncCallSiteCDependenceMappingMapping;

	map<Function *, map<Argument *, set<Value * > > > FuncArgDependenceMappingMapping;

private:
	//PostDominatorTree * pPDT;
	DataLayout * pDL;
	StructFieldReach * pSFReach;

};



#endif

