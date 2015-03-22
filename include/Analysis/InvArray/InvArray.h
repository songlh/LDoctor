#ifndef _H_SONGLH_INVARRAY
#define _H_SONGLH_INVARRAY

#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/DataLayout.h"

#include "llvm-Commons/Config/Config.h"
#include "llvm-Commons/CFG/CFGUtility.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

struct InvArray: public ModulePass
{
	static char ID;
	InvArray();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module &M);
	virtual void print(raw_ostream &O, const Module *M) const;

private:
	bool SearchInnerLoop();
	bool SearchOuterLoop();
	bool IsArrayAccessLoop(BasicBlock * pHeader, set<LoadInst *> & setArrayLoad);
	void AnalyzeLoopAccess(set<LoadInst *> & setArrayLoad);
	void BuildPossibleCallStack(vector<vector<Instruction *> > & vecCallStack);
	void CollectCallee(set<Function *> & setCallees);
	void CollectOtherLoops(map<Function *, vector<BasicBlock * > > & FuncHeaderMapping, set<Function *> & setCallees);
	void CollectOtherLoops(set<BasicBlock *> & setLoopHeader);
	void PruneLoop(map<Function *, vector<BasicBlock * > > & FuncHeaderMapping );
	bool ControlPrune(BasicBlock * pHeader, DominatorTree * DT , PostDominatorTree * PDT, ControlDependenceGraphBase & CDG);

private:

	BasicBlock * pInnerHeader;
	BasicBlock * pOuterHeader;

	Function * pInnerFunction;
	Function * pOuterFunction;


	Module * pModule;

	ScalarEvolution * SE;
	DataLayout * DL;


	map<Function *, LibraryFunctionType>  LibraryTypeMapping;

};


#endif

