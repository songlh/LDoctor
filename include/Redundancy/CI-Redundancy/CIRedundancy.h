#ifndef _H_SONGLH_CI_REDUNDANCY
#define _H_SONGLH_CI_REDUNDANCY

#include <vector>
#include <map>
#include <set>
#include <string>

#include "llvm/Pass.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/ScalarEvolution.h"

#include "Analysis/InterProcDep/InterProcDep.h"


using namespace std;
using namespace llvm;
using namespace llvm_Commons;


struct CrossIterationRedundancy : public ModulePass
{
	static char ID;
	CrossIterationRedundancy();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	


private:
	void CollectSideEffectInstsInsideLoop(Loop * pLoop, set<Instruction *> & setInstructions, ControlDependenceGraphBase & CDG);
	void LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setValueInput, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG);
	void CalDependenceForSEInst(Loop * pLoop, set<Instruction *> & SEInst, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG);
	void CIDependenceAnalysis(Loop * pLoop, set<Value *> & setDependentValue, PostDominatorTree * PDT);


private:
	map<Function *, LibraryFunctionType> LibraryTypeMapping;

	set<Function *> setCallee;
	map<Function *, set<Instruction *> > CalleeCallSiteMapping;

	DataLayout * pDL;
	InterProcDep * IPD;
	PostDominatorTree * PDT;
	DominatorTree * DT;
	LoopInfo * LI;
	ScalarEvolution * SE;

};

#endif

