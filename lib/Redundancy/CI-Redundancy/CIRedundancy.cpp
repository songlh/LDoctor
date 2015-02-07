
#include "llvm/DebugInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"


#include "llvm-Commons/Config/Config.h"
#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"
#include "llvm-Commons/Utility/Utility.h"
#include "Redundancy/CI-Redundancy/CIRedundancy.h"

#include <fstream>

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static cl::opt<unsigned> uSrcLine("noLine", 
					cl::desc("Source Code Line Number"), cl::Optional, 
					cl::value_desc("uSrcCodeLine"));


static cl::opt<std::string> strFileName("strFile", 
					cl::desc("File Name"), cl::Optional, 
					cl::value_desc("strFileName"));

static cl::opt<std::string> strFuncName("strFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strFuncName"));

static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));


static cl::opt<std::string> strLoopHeader("strLoopHeader",
					cl::desc("Block Name for Inner Loop Header"), cl::Optional,
					cl::value_desc("strLoopHeader"));


static RegisterPass<CrossIterationRedundancy> X(
		"cross-iteration-redundancy",
		"cross iteration redundancy analysis",
		false,
		true);

char CrossIterationRedundancy::ID = 0;

void CrossIterationRedundancy::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<InterProcDep>();
}

CrossIterationRedundancy::CrossIterationRedundancy(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
}

void CrossIterationRedundancy::print(raw_ostream &O, const Module *M) const
{
	return;
}




void CrossIterationRedundancy::CollectCalleeInsideLoop(Loop * pLoop)
{
	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
	{
		for(BasicBlock::iterator II = (*BB)->begin(); II != (*BB)->end(); ++ II )
		{
			if(isa<DbgInfoIntrinsic>(II))
			{
				continue;
			}
			else if(isa<CallInst>(II) || isa<InvokeInst>(II))
			{
				CallSite cs(II);

				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				this->CalleeCallSiteMapping[pCalled].insert(II);

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end())
				{
					continue;
				}

				if(pCalled->isDeclaration())
				{
					continue;
				}

				this->setCallee.insert(pCalled); 
			}
		}
	}
}


void CrossIterationRedundancy::CollectSideEffectInstsInsideLoop(Loop * pLoop, set<Instruction *> & setInstructions)
{
	set<BasicBlock *> setBlocksInLoop;

	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{	
		setBlocksInLoop.insert(*BB);

		for(BasicBlock::iterator II = (*BB)->begin() ; II != (*BB)->end(); ++ II)
		{
			if(StoreInst * pStore = dyn_cast<StoreInst>(II) )
			{
				setInstructions.insert(pStore);
			}
			else if(isa<CallInst>(II) || isa<InvokeInst>(II) )
			{
				if(isa<DbgInfoIntrinsic>(II))
				{
					continue;
				}

				if(isa<MemIntrinsic>(II))
				{
					setInstructions.insert(II);
					continue;
				}

				CallSite cs(II);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)  // this should be changed
				{
					setInstructions.insert(II);
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
				{
					if(this->LibraryTypeMapping[pCalled] == LF_MALLOC || this->LibraryTypeMapping[pCalled] == LF_IO || this->LibraryTypeMapping[pCalled] == LF_OTHER)
					{
						setInstructions.insert(II);
					}

					continue;
				}

				if(pCalled->isDeclaration())
				{
					setInstructions.insert(II);
					continue;
				}
			}
		}
	}

	Function * pFunction = pLoop->getHeader()->getParent();

	MAPBlockBeforeAfterPair mapBeforeAfter;
	PreciseLiveAnalysis(mapBeforeAfter, pFunction);

	set<Edge> setEdges;
	SearchExitEdgesForLoop(setEdges, pLoop);

	set<Edge>::iterator itEdgeBegin = setEdges.begin();
	set<Edge>::iterator itEdgeEnd = setEdges.end();

	for(; itEdgeBegin != itEdgeEnd; itEdgeBegin++)
	{
		SETBefore::iterator itSetInstBegin = mapBeforeAfter[itEdgeBegin->second].first[itEdgeBegin->first].begin();
		SETBefore::iterator itSetInstEnd   = mapBeforeAfter[itEdgeBegin->second].first[itEdgeBegin->first].end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin++)
		{
			if(setBlocksInLoop.find((*itSetInstBegin)->getParent()) != setBlocksInLoop.end() )
			{
				setInstructions.insert(*itSetInstBegin);
			}
		}
	}



/*
	set<Instruction *>::iterator itSetBegin = setInstructions.begin();
	set<Instruction *>::iterator itSetEnd   = setInstructions.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		(*itSetBegin)->dump();
	}

*/
}

/*
void CrossIterationRedundancy::DependenceAnalysis(Loop * pLoop, set<Value *> & setValueInput, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG, set<PHINode *> & setStopPHINode)
{
	set<BasicBlock *> setBlocksInLoop;

	Function * pCurrentFunction = pLoop->getHeader()->getParent();

	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
	{
		setBlocksInLoop.insert(*BB);
	}

	set<Value *>::iterator itValSetBegin = setValueInput.begin();
	set<Value *>::iterator itValSetEnd   = setValueInput.end();

	set<Value *> setProcessedValue;

	for(; itValSetBegin != itValSetEnd; itValSetBegin++ )
	{
		
	}

}
*/
void CrossIterationRedundancy::CIDependenceAnalysis(Loop * pLoop, set<Value *> & setDependentValue, PostDominatorTree * PDT)
{
	set<PHINode *> setStopPHINode;

	BasicBlock * pHeader = pLoop->getHeader();
	
	set<BasicBlock *> setBlockInsideLoop;
	
	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{
		setBlockInsideLoop.insert(*BB);
	}

	for(BasicBlock::iterator II = pHeader->begin(); II != pHeader->end(); II ++ )
	{
		if(PHINode * pPHINode = dyn_cast<PHINode>(II) )
		{
			setStopPHINode.insert(pPHINode);
		}
	}

	set<Instruction *> setSideEffectInst;

	CollectSideEffectInstsInsideLoop(pLoop, setSideEffectInst);


}






bool CrossIterationRedundancy::runOnModule(Module& M)
{
	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	Function * pFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);
	
	if(pFunction == NULL)
	{
		errs() << "Cannot find the function containing the loop!\n";
		return false;
	}

	PostDominatorTree * PDT = &getAnalysis<PostDominatorTree>(*pFunction);
	LoopInfo * pLI = &(getAnalysis<LoopInfo>(*pFunction));
	Loop * pLoop; 

	if(strLoopHeader == "")
	{
		pLoop = SearchLoopByLineNo(pFunction, pLI, uSrcLine);
	}
	else
	{
		BasicBlock * pHeader = SearchBlockByName(pFunction, strLoopHeader);
		
		if(pHeader == NULL)
		{
			errs() << "Cannot find the given loop header!\n";
			return false;
		}

		pLoop = pLI->getLoopFor(pHeader);
	}

	if(pLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}

	CollectCalleeInsideLoop(pLoop);

	this->IPD = &getAnalysis<InterProcDep>();
	this->IPD->InitlizeStartFunctionSet(this->setCallee);
	this->IPD->InterProcDependenceAnalysis();

	set<Value *> setDependentValue;

	CIDependenceAnalysis(pLoop, setDependentValue, PDT);




	return false;
}
