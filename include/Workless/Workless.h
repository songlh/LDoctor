#ifndef _H_SONGLH_WORKLESS
#define _H_SONGLH_WORKLESS

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"

#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;
using namespace llvm_Commons;

struct Workless : public ModulePass
{
	static char ID;
	Workless();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

	bool CollectSideEffectFunction(Function * pFunction);
	bool BlockWithoutSideEffect(BasicBlock * BB);
	void ParsePureFunctionList(string & strFileName, Module * pM);



	bool IsWorkless0Star(set<BasicBlock *> & setType1BasicBlock, set<BasicBlock *> & setType2BasicBlock, MAPBlockBeforeAfterPair & mapBeforeAndAfter );
	bool IsWorkless0Star1(set<BasicBlock *> & setType1Block, set<BasicBlock *> & setType2Block, MAPBlockBeforeAfterPair & mapBeforeAndAfter);
	void CollectWorkingBlocks(set<BasicBlock *> & setType1Block, set<BasicBlock *> & setType2Block, set<BasicBlock *> & setWorkingBlocks, MAPBlockBeforeAfterPair & mapBeforeAndAfter);
	bool IsWorkless0Or1Star(Loop * pLoop, set<BasicBlock *> & setType1Block, set<BasicBlock *> & setType2Block, MAPBlockBeforeAfterPair & mapBeforeAndAfter, set<BasicBlock *> & setWorkingBlocks);

	void AnalyzeWorklessType(Function * pFunction, Loop * pLoop);

	void Test(Loop * pLoop);

private:
	DominatorTree * DT;
	PostDominatorTree * PDT;

	set<Function *> setPureFunction;
	set<Function *> setSideEffectFunction;
};

#endif

