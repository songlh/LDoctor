#ifndef _H_SONGLH_SEARCH
#define _H_SONGLH_SEARCH


#include <set>

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace std;

namespace llvm_Commons
{
	Function * SearchFunctionByName(Module & , string &, string &, unsigned);
	void SearchBasicBlocksByLineNo( Function *, unsigned, vector<BasicBlock *> &);
	Loop * SearchLoopByLineNo( Function * , LoopInfo *, unsigned);

}

#endif

