#ifndef _H_SONGLH_CL_REDUNDANCY
#define _H_SONGLH_CL_REDUNDANCY


#include "llvm/IR/DataLayout.h"
#include "llvm/Pass.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;

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


	void LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setDependentValue, PostDominatorTree * PDT);


	void CollectSideEffectInstruction(Loop * pLoop, set<Instruction *> & setSideEffectInst);


private:
	set<string> setPureFunctions;
	set<string> setMemoryAllocFunctions;

	DataLayout * pDL;

};




#endif



