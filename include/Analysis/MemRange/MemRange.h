#ifndef _H_SONGLH_MEMRANGE
#define _H_SONGLH_MEMRANGE

#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/DataLayout.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

struct MemRange: public ModulePass
{
	static char ID;
	MemRange();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module &M);
	virtual void print(raw_ostream &O, const Module *M) const;

private:

	//void IndentifyMonitoredLoad(Loop * pLoop);
	void AnalyzeMonitoredLoad(Loop * pLoop);
	void DumpInstPaddingInfo();


private:
	LoopInfo * LI;
	ScalarEvolution * SE;
	DataLayout * DL;

	MonitoredElement MonitorElems;
	

	map<int, LoadInst *> IndexLoadMapping;
	map<LoadInst *, vector<set<Value *> > > LoadArrayAccessMapping;
	map<LoadInst *, int64_t> LoadStrideMapping;
	

};



#endif

