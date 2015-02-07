#ifndef _H_SONGLH_FFRREDUNDANCY
#define _H_SONGLH_FFRREDUNDANCY

#include <vector>
#include <map>
#include <set>
#include <string>


#include "llvm/Pass.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DataLayout.h"

#include "Analysis/InterProcDep/InterProcDep.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

struct FFRRedundancy : public ModulePass
{
	static char ID;
	FFRRedundancy();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	

	void DependenceAnalysis(set<Value *> & setDependingValues, Function * pFunction );

	void PruneDependenceResult(set<Value *> & setDependingValues, Function * pFunction);

	void PruneArgument(set<Value *> & setDependingValues, Function * pFunction);


private:
	map<Function *, LibraryFunctionType>  LibraryTypeMapping;

	InterProcDep * IPD;

	DataLayout * pDL;
};


#endif

