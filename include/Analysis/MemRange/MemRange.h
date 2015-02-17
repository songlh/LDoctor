#ifndef _H_SONGLH_MEMRANGE
#define _H_SONGLH_MEMRANGE

#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"

using namespace std;
using namespace llvm;

struct MemRange: public ModulePass
{
	static char ID;
	MemRange();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module &M);
	virtual void print(raw_ostream &O, const Module *M) const;

private:
	void ParseMonitoredInstFile(string & sFileName, Module * pModule);
	void IndentifyMonitoredLoad(Loop * pLoop);
	void AnalyzeMonitoredLoad();


private:
	LoopInfo * LI;
	ScalarEvolution * SE;

	set<int> setInstIndex;
	vector<pair<Function *, int> > vecParaIndex;

	set<LoadInst *> setLoadInst;

};



#endif

