#ifndef _H_SONGLH_CL_REDUNDANCY
#define _H_SONGLH_CL_REDUNDANCY

#include "Analysis/InterProcDep/InterProcDep.h"
#include "llvm/Analysis/ScalarEvolution.h"

#include "llvm/IR/DataLayout.h"
#include "llvm/Pass.h"

#include <string>
#include <set>
#include <vector>

#include "llvm-Commons/Dependence/DependenceUtility.h"

using namespace llvm;
using namespace std;


enum OutsideValueKind {
	OVK_NotOnlyOne,
	OVK_NoDependence,
	OVK_OnlyControl,
	OVK_Evolve,
	OVK_Other
};




struct CrossLoopRedundancy : public ModulePass
{

	static char ID;
	CrossLoopRedundancy();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

//confirmed
	void InitializePureFunctionSet();
	void InitializeMemoryAllocFunctionSet();
	void InitializeFileIOFunctionSet();
	void InitializeLibraryFunctionSet();
	void CollectSideEffectInstructionInsideLoop(Loop * pLoop, set<Instruction *> & setSideEffectInst);

	void DumpInterProcDepResult();

	void CalDependenceForSEInst(Loop * pLoop, set<Instruction *> & SEInst, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG);
	void LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setValueInput, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG);
	
	void LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setDependentValue, PostDominatorTree * PDT);
	void CollectSideEffectInstruction(Loop * pLoop, set<Instruction *> & setSideEffectInst);

	bool ControlDependingOnItself(PHINode * pPHI, Loop * pLoop, ControlDependenceGraphBase & CDG);
	bool DataDependingOnItself(PHINode * pPHI, Loop * pLoop);

	void AnalyzeValueDefinedOutsideLoop(set<Value *> & setDependentValue, Loop * pLoop, PostDominatorTree * PDT);

private:

	map<Function *, LibraryFunctionType>  LibraryTypeMapping;

	set<Function *> setCallee;
	map<Function *, set<Instruction *> > CalleeCallSiteMapping;

	map<Value *, OutsideValueKind> OutsideValueKindMapping;
	map<Value *, vector<PHINode *> > IterativePHIMapping;
	map<Value *, vector<int64_t> > IterativeStrideMapping;

	DataLayout * pDL;
	InterProcDep * IPD;
	ScalarEvolution * SE;

};




#endif



