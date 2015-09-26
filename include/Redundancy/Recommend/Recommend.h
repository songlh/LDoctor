#ifndef _H_SONGLH_RECOMMEND
#define _H_SONGLH_RECOMMEND

#include "Analysis/InterProcDep/InterProcDep.h"
#include "llvm/Analysis/ScalarEvolution.h"

#include "llvm/IR/DataLayout.h"
#include "llvm/Pass.h"

#include <string>
#include <set>
#include <vector>

#include "llvm-Commons/Dependence/DependenceUtility.h"

struct Recommend : public ModulePass
{

	static char ID;
	Recommend();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	
	bool NotBatchInst(Loop * pLoop );
	bool MemInst(Loop * pLoop );

private:
	map<Function *, LibraryFunctionType>  LibraryTypeMapping;
	
	map<Function *, set<Instruction *> > CalleeCallSiteMapping;

	set<Function *> setCallee;

	DataLayout * pDL;
	InterProcDep * IPD;
	ScalarEvolution * SE;


};



#endif


