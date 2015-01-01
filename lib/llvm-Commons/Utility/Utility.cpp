
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

void SearchExitEdgesForBlocks( set<Edge> & setExitEdges, set<BasicBlock *> & setBlocks)
{
	set<BasicBlock *>::iterator itSetBegin = setBlocks.begin();
	set<BasicBlock *>::iterator itSetEnd   = setBlocks.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		for (succ_iterator I = succ_begin(*itSetBegin), E = succ_end(*itSetBegin); I != E; ++I)
		{
			if(setBlocks.find(*I) != setBlocks.end())
			{
				continue;
			}

			Edge edge;
			edge.first = *itSetBegin;
			edge.second = *I;
			setExitEdges.insert(edge);
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


	set<Edge>::iterator itSetFirst = itSetBegin;
	itSetBegin++;
	BasicBlock * pResult = pPDT->findNearestCommonDominator(itSetFirst->second, itSetBegin->second);


	for(; itSetBegin != itSetEnd; itSetBegin++)
	{
		if(pResult == NULL)
		{
			return pResult;
		}

		pResult = pPDT->findNearestCommonDominator(pResult, itSetBegin->second);
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
	//if(pPostHeader == NULL)
	//{
	//	return;
	//}

	//errs() << "Post header: " << pPostHeader->getName() << "\n";

//1. blocks outside the loop
//2. blocks dominate by the header
//3. blocks postdominate by the post header
//4. blocks does not post dominate all blocks in the loop

	for(Function::iterator b = pFunction->begin(), be = pFunction->end(); b != be ; b ++ )
	{
		if(isa<UnreachableInst>(b->getTerminator()))
		{
			continue;
		}

		if(b->getName() == "" )
		{
			continue;
		}


		if(setBlocksInLoop.find(b) != setBlocksInLoop.end() )
		{
			continue;
		}

		if(!DT->dominates(pLoop->getHeader(), b))
		{
			continue;
		}

		if(pPostHeader != NULL)
		{
			if(!PDT->dominates(pPostHeader, b))
			{
				continue;
			}
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

void Search2TypeBlocksInLoop(set<BasicBlock *> & setType1Blocks, set<BasicBlock *> & setType2Blocks, Loop * pLoop, Function * pFunction, PostDominatorTree * PDT, DominatorTree * DT)
{
	vector<BasicBlock *> vecType1Blocks;
	vector<BasicBlock *> vecType2Blocks;

	Search2TypeBlocksInLoop(vecType1Blocks, vecType2Blocks, pLoop, pFunction, PDT, DT);

	setType1Blocks.insert(vecType1Blocks.begin(), vecType1Blocks.end());
	setType2Blocks.insert(vecType2Blocks.begin(), vecType2Blocks.end());



}


bool PureIntrinsic(IntrinsicInst * II)
{
	//IntrNoMem: return true
	//IntrReadArgMem: return true
	//IntrReadMem: return true
	//IntrReadWriteArgMem: return false
	int iID = II->getIntrinsicID();
	switch(iID)
	{
		case Intrinsic::vastart:                              //Variable Argument Handling Intrinsics
		case Intrinsic::vacopy:
		case Intrinsic::vaend:
			return false;
		case Intrinsic::gcroot:                               //Garbage Collection Intrinsics
			return false;
		case Intrinsic::gcread:
			return true;
		case Intrinsic::gcwrite:
			return false;
		case Intrinsic::returnaddress:                        //Code Generator Intrinsics
		case Intrinsic::frameaddress:
			return true;
		case Intrinsic::stacksave:
		case Intrinsic::stackrestore:
		case Intrinsic::prefetch:
		case Intrinsic::pcmarker:
		case Intrinsic::readcyclecounter:
		case Intrinsic::stackprotector:
			return false;
		case Intrinsic::memcpy:                               //Standard C Library Intrinsics
		case Intrinsic::memmove:
		case Intrinsic::memset:
			return false;
		case Intrinsic::sqrt:
		case Intrinsic::powi:
		case Intrinsic::sin:
		case Intrinsic::cos:
		case Intrinsic::pow:
		case Intrinsic::log:
		case Intrinsic::log10:
		case Intrinsic::log2:
		case Intrinsic::exp:
		case Intrinsic::exp2:
		case Intrinsic::fabs:
		case Intrinsic::floor:
		case Intrinsic::ceil:
		case Intrinsic::trunc:
		case Intrinsic::rint:
		case Intrinsic::nearbyint:
		case Intrinsic::fma:
		case Intrinsic::fmuladd:
			return true;
		case Intrinsic::setjmp:
		case Intrinsic::longjmp:
		case Intrinsic::sigsetjmp:
		case Intrinsic::siglongjmp:
			return false;
		case Intrinsic::objectsize:
		case Intrinsic::expect:                       //Expect Intrinsics
		case Intrinsic::bswap:                        //Bit Manipulation Intrinsics
		case Intrinsic::ctpop:
		case Intrinsic::ctlz:
		case Intrinsic::cttz:
		case Intrinsic::eh_typeid_for:                //Exception Handling
			return true;
		case Intrinsic::eh_return_i32:
		case Intrinsic::eh_return_i64:
		case Intrinsic::eh_unwind_init:
		case Intrinsic::eh_dwarf_cfa:
			return false;
		case Intrinsic::eh_sjlj_lsda:
		case Intrinsic::eh_sjlj_callsite:
			return true;
		case Intrinsic::eh_sjlj_functioncontext:
		case Intrinsic::eh_sjlj_setjmp:
		case Intrinsic::eh_sjlj_longjmp:
			return false;
		case Intrinsic::var_annotation:              //Generic Variable Attribute Intrinsics
		case Intrinsic::ptr_annotation:
		case Intrinsic::annotation:
		case Intrinsic::init_trampoline:             // Trampoline Intrinsics
			return false;
		case Intrinsic::adjust_trampoline:
		case Intrinsic::sadd_with_overflow:          //Overflow Intrinsics
		case Intrinsic::uadd_with_overflow:
		case Intrinsic::ssub_with_overflow:
		case Intrinsic::usub_with_overflow:
		case Intrinsic::smul_with_overflow:
		case Intrinsic::umul_with_overflow:
			return true;
		case Intrinsic::lifetime_start:              //Memory Use Markers
			return false;
		case Intrinsic::lifetime_end:
			return true;                         //this rule is created by Linhai
		case Intrinsic::invariant_start: 
		case Intrinsic::invariant_end:
			return false;
		case Intrinsic::flt_rounds:                  //Other Intrinsics
		case Intrinsic::trap:
		case Intrinsic::debugtrap:
			return false;
		case Intrinsic::donothing:
		case Intrinsic::convert_to_fp16:
		case Intrinsic::convert_from_fp16:
			return true;
		case Intrinsic::convertff:                   //
		case Intrinsic::convertfsi:
		case Intrinsic::convertfui:
		case Intrinsic::convertsif:
		case Intrinsic::convertuif:
		case Intrinsic::convertss:
		case Intrinsic::convertsu:
		case Intrinsic::convertus:
		case Intrinsic::convertuu:
			return false;
		case Intrinsic::dbg_declare:                  //Debugger Intrinsics
		case Intrinsic::dbg_value:
			return true;
 
	}

	return false;

}


}

