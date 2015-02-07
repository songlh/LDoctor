#ifndef _H_SONGLH_SYSCREDUNDANCY
#define _H_SONGLH_SYSCREDUNDANCY


#include <vector>
#include <map>
#include <set>
#include <string>

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DataLayout.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

struct SysCRedundancy : public ModulePass
{
	static char ID;
	SysCRedundancy();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;

	void CollectSEInstInsideLoop(Loop * pLoop, set<Instruction *> & setSideEffectInst);
	void CollectSEInstForCallee(Function * pFunction, set<Instruction *> & setSideEffectInst);

	void RedundantSystemCallChecking(Loop * pLoop);


private:
	set<Function *> setCallee;
	map<Function *, set<Instruction *> > CalleeCallSiteMapping;
	map<Function *, LibraryFunctionType>  LibraryTypeMapping;
	DataLayout * pDL;	

};



#endif



