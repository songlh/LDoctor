#ifndef _H_SONGLH_LINKLIST
#define _H_SONGLH_LINKLIST

#include "llvm/Analysis/LoopInfo.h"

#include <set>
#include <map>

using namespace llvm;
using namespace std;

namespace llvm_Commons
{

	bool isReachableThroughLinkListDereference(Instruction * IA, Instruction * IB, Loop * pLoop);
	bool isLinkListLoop(Loop * pLoop, map<PHINode *, set<Value *> > & LinkListHeaderMapping );
	bool isLinkListLoop(Loop * pLoop, set<Value *> & setLinkListHeader);

}


#endif

