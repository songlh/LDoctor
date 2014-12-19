#ifndef _H_SONGLH_UTILITY
#define _H_SONGLH_UTILITY

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"


#include <set>

namespace llvm_Commons
{

typedef std::pair<llvm::BasicBlock *, llvm::BasicBlock *> Edge;

//search exit edges for a given loop
void SearchExitEdgesForLoop( std::set< Edge > & setExitEdges, llvm::Loop * pLoop );

//search post dominator for a given loop
llvm::BasicBlock * SearchPostHeader(std::set< Edge > & , llvm::PostDominatorTree * );

//search two types of blocks for a given loop
void Search2TypeBlocksInLoop(std::vector<llvm::BasicBlock *> & , std::vector<llvm::BasicBlock *> &, 
							llvm::Loop *, llvm::Function *, llvm::PostDominatorTree *, llvm::DominatorTree * );

}




#endif

