#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/CFG/CFGUtility.h"
#include "llvm-Commons/Dependence/DependenceUtility.h"
#include "llvm-Commons/Config/Config.h"
#include "llvm-Commons/LinkList/LinkList.h"
#include "llvm-Commons/Array/Array.h"
#include "llvm-Commons/Loop/Loop.h"
#include "llvm-Commons/SEWrapper/SEWrapper.h"
#include "Analysis/InterProcDep/InterProcDep.h"

#include "Redundancy/Recommend/Recommend.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/DebugInfo.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static cl::opt<unsigned> uInnerSrcLine("noInnerLine", 
					cl::desc("Source Code Line Number for Inner Loop"), cl::Optional, 
					cl::value_desc("uInnerSrcCodeLine"));

static cl::opt<std::string> strInnerFileName("strInnerFile", 
					cl::desc("File Name for Inner Loop"), cl::Optional, 
					cl::value_desc("strInnerFileName"));

static cl::opt<std::string> strInnerFuncName("strInnerFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strInnerFuncName"));

static cl::opt<std::string> strLoopHeader("strLoopHeader",
					cl::desc("Block Name for Inner Loop"), cl::Optional,
					cl::value_desc("strLoopHeader"));

static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));

static RegisterPass<Recommend> X(
		"cross-loop-recommend",
		"cross loop redundancy recommend",
		false,
		true);

char Recommend::ID = 0;

void Recommend::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<DominatorTree>();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<InterProcDep>();
	//AU.addRequired<ScalarEvolution>();
}

Recommend::Recommend(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeDominatorTreePass(Registry);
	initializePostDominatorTreePass(Registry);
}

void Recommend::print(raw_ostream &O, const Module *M) const
{
	return;
}

bool Recommend::NotBatchInst(Loop * pLoop )
{

	set<Instruction *>  setSideEffectInst;

	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{	
		for(BasicBlock::iterator II = (*BB)->begin() ; II != (*BB)->end(); ++ II)
		{
			if(StoreInst * pStore = dyn_cast<StoreInst>(II) )
			{
				setSideEffectInst.insert(pStore);
			}
			else if(isa<CallInst>(II) || isa<InvokeInst>(II) )
			{
				if(isa<DbgInfoIntrinsic>(II))
				{
					continue;
				}

				if(isa<MemIntrinsic>(II))
				{
					setSideEffectInst.insert(II);
					continue;
				}

				CallSite cs(II);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)  // this should be changed
				{
					setSideEffectInst.insert(II);
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
				{
					if(this->LibraryTypeMapping[pCalled] == LF_TRANSPARENT)
					{
						continue;
					}
					else if(this->LibraryTypeMapping[pCalled] == LF_PURE)
					{
						continue;
					}

					setSideEffectInst.insert(II);
					continue;
				}

				if(pCalled->isDeclaration())
				{
					setSideEffectInst.insert(II);
					continue;
				}
			}
		}
	}

	if(setSideEffectInst.size() > 0)
	{
		return true;
	}

	return false;
}

bool Recommend::MemInst(Loop * pLoop )
{
	set<Instruction *>  setSideEffectInst;
	set<BasicBlock *> setBlocksInLoop;
	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{
		setBlocksInLoop.insert(*BB);

	}

	Function * pFunction = (*pLoop->block_begin())->getParent();

	MAPBlockBeforeAfterPair mapBeforeAndAfter;
	PreciseLiveAnalysis(mapBeforeAndAfter, pFunction);

	set<Edge> setEdges;
	SearchExitEdgesForLoop(setEdges, pLoop);

	set<Edge>::iterator itEdgeBegin = setEdges.begin();
	set<Edge>::iterator itEdgeEnd = setEdges.end();

	for(; itEdgeBegin != itEdgeEnd; itEdgeBegin++)
	{
		SETBefore::iterator itSetInstBegin = mapBeforeAndAfter[itEdgeBegin->second].first[itEdgeBegin->first].begin();
		SETBefore::iterator itSetInstEnd = mapBeforeAndAfter[itEdgeBegin->second].first[itEdgeBegin->first].end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin++)
		{
			if(setBlocksInLoop.find((*itSetInstBegin)->getParent()) != setBlocksInLoop.end() )
			{
				setSideEffectInst.insert(*itSetInstBegin);
			}
		}
	}

	if(setSideEffectInst.size()>0)
	{
		return true;
	}

	return false;
}



bool Recommend::runOnModule(Module& M)
{
	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	Function * pInnerFunction = SearchFunctionByName(M, strInnerFileName, strInnerFuncName, uInnerSrcLine);
	
	

	if(pInnerFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return false;
	}

	DominatorTree * DT      = &getAnalysis<DominatorTree>(*pInnerFunction);
	PostDominatorTree * PDT = &getAnalysis<PostDominatorTree>(*pInnerFunction);
	LoopInfo * pInnerLI = &(getAnalysis<LoopInfo>(*pInnerFunction));
	Loop * pInnerLoop; 

	if(strLoopHeader == "")
	{
		pInnerLoop = SearchLoopByLineNo(pInnerFunction, pInnerLI, uInnerSrcLine);
	}
	else
	{
		BasicBlock * pHeader = SearchBlockByName(pInnerFunction, strLoopHeader);
		if(pHeader == NULL)
		{
			errs() << "Cannot find the given loop header!\n";
			return false;
		}
		pInnerLoop = pInnerLI->getLoopFor(pHeader);	
	}

	if(pInnerLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}

	CollectCalleeInsideLoop(pInnerLoop, this->setCallee, this->CalleeCallSiteMapping, this->LibraryTypeMapping);

	this->IPD = &getAnalysis<InterProcDep>();
	this->IPD->InitlizeStartFunctionSet(this->setCallee);
	this->IPD->LibraryTypeMapping = this->LibraryTypeMapping;
	this->IPD->InterProcDependenceAnalysis();


	if(MemInst(pInnerLoop) && !NotBatchInst(pInnerLoop ))
	{
		errs() << "Memoization\n";
	}

	return false;
}



