#ifndef _H_SONGLH_UTILITY
#define _H_SONGLH_UTILITY

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"


#include <set>

using namespace std;
using namespace llvm;

namespace llvm_Commons
{

typedef pair<BasicBlock *, BasicBlock *> Edge;

//search exit edges for a given loop
void SearchExitEdgesForLoop( set< Edge > & setExitEdges, Loop * pLoop );

//search exit edges for a bunch of blocks
void SearchExitEdgesForBlocks( set<Edge> & setExitEdges, set<BasicBlock *> & setBlocks);

//search post dominator for a given loop
BasicBlock * SearchPostHeader(set< Edge > & , PostDominatorTree * );

//search two types of blocks for a given loop
void Search2TypeBlocksInLoop(vector<BasicBlock *> & , vector<BasicBlock *> &, 
							Loop *, Function *, PostDominatorTree *, DominatorTree * );

void Search2TypeBlocksInLoop(set<BasicBlock *> &, set<BasicBlock *> &, Loop *, Function *, PostDominatorTree *, DominatorTree *);

bool PureIntrinsic(llvm::IntrinsicInst * II);

}




#endif

