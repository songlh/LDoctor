

#ifndef _H_SONGLH_INVARIANTANALYSIS
#define _H_SONGLH_INVARIANTANALYSIS


#include <vector>

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

void IndentifyInvariantGlobalVariable(Function * pF, set<Value *> & setInvariantGV, set<Function *> & setScope);

void IndentifyInvariantArray(Function * pF, set<Value *> & setArray, set<Function *> & setScope); 

}


#endif


