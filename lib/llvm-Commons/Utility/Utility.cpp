
#include "llvm-Commons/Utility/Utility.h"

using namespace std;
using namespace llvm;


namespace llvm_Commons
{

void SearchExitEdgesForLoop( set< Edge > & setExitEdges, Loop * pLoop )
{
	set<BasicBlock *> setBlocksInLoop;

	for( Loop::block_iterator b = pLoop->block_begin() , be = pLoop->block_end() ; b != be; ++ b )
	{
		setBlocksInLoop.insert( *b );
	}

	for( Loop::block_iterator b = pLoop->block_begin(), be = pLoop->block_end() ; b != be ; ++ b )
	{
		for (succ_iterator I = succ_begin(*b), E = succ_end(*b); I != E; ++I) 
		{
			if(setBlocksInLoop.find(*I) != setBlocksInLoop.end() )
			{
				continue;
			}

			Edge edge;
			edge.first = *b;
			edge.second = *I;
			setExitEdges.insert(edge) ;
		}
	}
}


BasicBlock * SearchPostHeader(set< Edge > & setExitEdges, PostDominatorTree * pPDT)
{

	set<Edge>::iterator itSetBegin = setExitEdges.begin();
	set<Edge>::iterator itSetEnd = setExitEdges.end();

	if(setExitEdges.size() == 1)
	{
		return itSetBegin->second;
	}

	BasicBlock * pResult = NULL;

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		set<Edge>::iterator itTmpBegin = setExitEdges.begin();
		set<Edge>::iterator itTmpEnd = setExitEdges.end();

		bool bFlag = true;
		while(itTmpBegin != itTmpEnd)
		{
			if(itTmpBegin != itSetBegin)
			{
				if(!pPDT->dominates(itSetBegin->second, itTmpBegin->second))
				{
					bFlag = false;
					break;
				}
			}
			itTmpBegin++;
		}

		if(bFlag)
		{
			pResult = itSetBegin->second;
			break;
		}
	}

	return pResult;

}


void Search2TypeBlocksInLoop(vector<BasicBlock *> & vecType1Blocks, vector<BasicBlock *> & vecType2Blocks, Loop * pLoop, Function * pFunction, PostDominatorTree * PDT, DominatorTree * DT)
{

	vecType1Blocks.clear();
	vecType2Blocks.clear();
	set<BasicBlock *> setBlocksInLoop;

	for( Loop::block_iterator b = pLoop->block_begin() , be = pLoop->block_end() ; b != be; ++ b )
	{
		vecType1Blocks.push_back( *b );
		setBlocksInLoop.insert(*b);
	}

	set< Edge >  setExitEdges;

	SearchExitEdgesForLoop(setExitEdges, pLoop);

	if(setExitEdges.size() == 1)
	{
		return;
	}

	BasicBlock * pPostHeader = SearchPostHeader(setExitEdges, PDT);

	if(pPostHeader == NULL)
	{
		return;
	}


//1. blocks outside the loop
//2. blocks dominate by the header
//3. blocks postdominate by the post header
//4. blocks does not post dominate all blocks in the loop

	for(Function::iterator b = pFunction->begin(), be = pFunction->end(); b != be ; b ++ )
	{
		if(setBlocksInLoop.find(b) != setBlocksInLoop.end() )
		{
			continue;
		}

		if(!DT->dominates(pLoop->getHeader(), b))
		{
			continue;
		}

		if(!PDT->dominates(pPostHeader, b))
		{
			continue;
		}

		bool bFlag = true;
		vector<BasicBlock *>::iterator itVecBegin = vecType1Blocks.begin();
		vector<BasicBlock *>::iterator itVecEnd = vecType1Blocks.end();

		while(itVecBegin != itVecEnd)
		{
			if(!PDT->dominates(b, *itVecBegin))
			{
				bFlag = false;
				break;
			}
			itVecBegin++;
		}

		if(!bFlag)
		{
			vecType2Blocks.push_back(b);
		}
	}


}



}

