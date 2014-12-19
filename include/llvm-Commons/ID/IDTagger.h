#ifndef _H_SONGLH_IDTAGGER
#define _H_SONGLH_IDTAGGER

#include "llvm/Pass.h"
using namespace llvm;


namespace llvm_Commons
{

struct IDTagger: public ModulePass
{
	static char ID;
	IDTagger();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module &M);
};



}

#endif

