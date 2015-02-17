#ifndef _H_SONGLH_CLONE
#define _H_SONGLH_CLONE

#include <string>
#include <set>
#include <map>

#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Transforms/Utils/Cloning.h"

using namespace llvm;
using namespace std;

namespace llvm_Commons {

Function * CloneFunctionWithExtraArguments(const Function * F, ValueToValueMapTy & VMap, bool ModuleLevelChanges, vector<Type *> & ExtraArguments, ClonedCodeInfo * CodeInfo );

}



#endif

