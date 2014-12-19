

#ifndef _H_SONGLH_DEPENDENCEUTILITY
#define _H_SONGLH_DEPENDENCEUTILITY


#include "llvm/IR/Instruction.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <vector>

using namespace std;
using namespace llvm;

namespace llvm_Commons
{

void GetDependingValue(Instruction *, vector<Value *> &);

}



#endif


