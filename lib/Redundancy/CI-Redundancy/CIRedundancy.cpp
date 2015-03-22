
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
#include "llvm-Commons/CFG/CFGUtility.h"
#include "llvm-Commons/Dependence/DependenceUtility.h"
#include "llvm-Commons/SEWrapper/SEWrapper.h"

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
	AU.addRequired<DominatorTree>();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<InterProcDep>();
	AU.addRequired<ScalarEvolution>();
}

CrossIterationRedundancy::CrossIterationRedundancy(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeDominatorTreePass(Registry);
	initializePostDominatorTreePass(Registry);

}

void CrossIterationRedundancy::print(raw_ostream &O, const Module *M) const
{
	return;
}

/*
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
*/

void CrossIterationRedundancy::CollectSideEffectInstsInsideLoop(Loop * pLoop, set<Instruction *> & setInstructions, ControlDependenceGraphBase & CDG)
{
	set<BasicBlock *> setBlocksInLoop;
	set<Instruction *> setSDInstInType2;

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

	set<BasicBlock *> setType1Blocks;
	set<BasicBlock *> setType2Blocks;

	Search2TypeBlocksInLoop(setType1Blocks, setType2Blocks, pLoop, pFunction, this->PDT, this->DT);

	set<BasicBlock *>::iterator itSetBlockBegin = setType2Blocks.begin();
	set<BasicBlock *>::iterator itSetBlockEnd   = setType2Blocks.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++ )
	{
		BasicBlock * BB = * itSetBlockBegin;
		for(BasicBlock::iterator II = (BB)->begin() ; II != (BB)->end(); ++ II)
		{
			if(StoreInst * pStore = dyn_cast<StoreInst>(II) )
			{
				setSDInstInType2.insert(pStore);
			}
			else if(isa<CallInst>(II) || isa<InvokeInst>(II) )
			{
				if(isa<DbgInfoIntrinsic>(II))
				{
					continue;
				}

				if(isa<MemIntrinsic>(II))
				{
					setSDInstInType2.insert(II);
					continue;
				}

				CallSite cs(II);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)  // this should be changed
				{
					setSDInstInType2.insert(II);
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

					setSDInstInType2.insert(II);
					continue;
				}

				if(pCalled->isDeclaration())
				{
					setSDInstInType2.insert(II);
					continue;
				}
			}
		}
	}


	set<Edge> setType2Edges;
	SearchExitEdgesForBlocks(setType2Edges, setType2Blocks);

	itEdgeBegin = setType2Edges.begin();
	itEdgeEnd = setType2Edges.end();

	for(; itEdgeBegin != itEdgeEnd; itEdgeBegin++)
	{
		if(pLoop->contains(itEdgeBegin->second))
		{
			continue;
		}

		SETBefore::iterator itSetInstBegin = mapBeforeAfter[itEdgeBegin->second].first[itEdgeBegin->first].begin();
		SETBefore::iterator itSetInstEnd = mapBeforeAfter[itEdgeBegin->second].first[itEdgeBegin->first].end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin++)
		{
			if(setType2Blocks.find((*itSetInstBegin)->getParent()) != setType2Blocks.end() )
			{
				setSDInstInType2.insert(*itSetInstBegin);
			}
		}
	}

	set<Instruction *>::iterator itSetBegin = setSDInstInType2.begin();
	set<Instruction *>::iterator itSetEnd = setSDInstInType2.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		BasicBlock * pBlock = (*itSetBegin)->getParent();

		for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
		{					
			if(CDG.influences(*BB, pBlock))
			{
				TerminatorInst * pTerminator = (*BB)->getTerminator();
			
				if(pTerminator != NULL)
				{
					if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
					{
						if(pBranch->isConditional())
						{
							if(Instruction * pInst = dyn_cast<Instruction>(pBranch->getCondition() ))
							{
								setInstructions.insert(pInst);
							}
						}
					}
					else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
					{
						if(Instruction * pInst = dyn_cast<Instruction>(pSwitch->getCondition() ))
						{
							setInstructions.insert(pInst);
						}
					}
				}
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

//all content are dependence
void CrossIterationRedundancy::LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setValueInput, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG)
{
	set<BasicBlock *> setBlocksInLoop;

	Function * pCurrentFunction = pLoop->getHeader()->getParent();

	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
	{
		setBlocksInLoop.insert(*BB);
	}

	set<Value *> setProcessedValue;

	vector<Value *> vecWorkList;
	vecWorkList.insert(vecWorkList.begin(), setValueInput.begin(), setValueInput.end());

	BasicBlock * pHeader = pLoop->getHeader();

	while(vecWorkList.size() > 0)
	{
		Value * pCurrentValue = vecWorkList.back();
		vecWorkList.pop_back();

		if(setProcessedValue.find(pCurrentValue) != setProcessedValue.end() )
		{
			continue;
		}

		setProcessedValue.insert(pCurrentValue);

		if(!isa<Instruction>(pCurrentValue))
		{
			setDependentValue.insert(pCurrentValue);
			continue;
		}

		Instruction * pCurrent = cast<Instruction>(pCurrentValue);
		
		//skip all instrumented site
		if(pCurrent->getParent()->getParent() != pCurrentFunction )
		{
			setDependentValue.insert(pCurrent);
			continue;
		}

		if(setBlocksInLoop.find(pCurrent->getParent()) == setBlocksInLoop.end())
		{
			setDependentValue.insert(pCurrent);
			continue;
		}

		if(isa<PHINode>(pCurrent) && pCurrent->getParent() == pHeader)
		{
			setDependentValue.insert(pCurrent);
			continue;
		}

		if(isa<LoadInst>(pCurrent) || isa<MemTransferInst>(pCurrent))
		{
			setDependentValue.insert(pCurrent);
			continue;
		}

		vector<Value *> vecValueDependence;

		if(isa<MemIntrinsic>(pCurrent))
		{
			GetDependingValue(pCurrent, vecValueDependence);
		}
		else if(isa<CallInst>(pCurrent) || isa<InvokeInst>(pCurrent) )
		{
			CallSite cs(pCurrent);
			Function * pCalled = cs.getCalledFunction();

			if(pCalled == NULL)
			{
				setDependentValue.insert(pCurrent);
				continue;
			}

			if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end())
			{
				if(this->LibraryTypeMapping[pCalled] != LF_TRANSPARENT && this->LibraryTypeMapping[pCalled] != LF_MALLOC )
				{
					setDependentValue.insert(pCurrent);
					continue;
				}
				else
				{
					GetDependingValue(pCurrent, vecValueDependence);
				}
			}
			else if(pCalled->isDeclaration() )
			{
				setDependentValue.insert(pCurrent);
				continue;
			}
			else
			{
				map<Instruction *, set<Value *> > ValueDependenceMapping = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCalled][pCalled];
					
				set<ReturnInst *> setRetInst;
				GetAllReturnInst(pCalled, setRetInst);

				set<ReturnInst *>::iterator itRetBegin = setRetInst.begin();
				set<ReturnInst *>::iterator itRetEnd   = setRetInst.end();

				for(; itRetBegin != itRetEnd; itRetBegin ++ )
				{
					set<Value *>::iterator itSetValueBegin = ValueDependenceMapping[*itRetBegin].begin();
					set<Value *>::iterator itSetValueEnd   = ValueDependenceMapping[*itRetBegin].end();

					for(; itSetValueBegin != itSetValueEnd; itSetValueBegin ++ )
					{
						if(Argument * pArg = dyn_cast<Argument>(*itSetValueBegin) )
						{
							//pArg->dump();
							assert(pArg->getParent() == pCalled);	
							vecValueDependence.push_back(pCurrent->getOperand(pArg->getArgNo()));
						}
						else
						{
							vecValueDependence.push_back(*itSetValueBegin);
						}
					}
				}
			}
		}
		else
		{
			GetDependingValue(pCurrent, vecValueDependence);
		}

		vector<Value *>::iterator itVecValueBegin = vecValueDependence.begin();
		vector<Value *>::iterator itVecValueEnd   = vecValueDependence.end();

		if(isa<MemIntrinsic>(pCurrent))
		{
			itVecValueBegin ++;
		}

		for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
		{
			if(setProcessedValue.find(*itVecValueBegin) == setProcessedValue.end() )
			{
				vecWorkList.push_back(*itVecValueBegin);
			}
		}

		for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
		{
			if(CDG.influences(*BB, pCurrent->getParent()))
			{
				TerminatorInst * pTerminator = (*BB)->getTerminator();
				if(pTerminator !=NULL)
				{
					if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
					{
						if(pBranch->isConditional())
						{
							if(setProcessedValue.find(pBranch->getCondition()) == setProcessedValue.end() )
							{
								vecWorkList.push_back(pBranch->getCondition());
							}
						}
					}
					else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
					{
						if(setProcessedValue.find(pSwitch->getCondition()) == setProcessedValue.end())
						{
							vecWorkList.push_back(pSwitch->getCondition());
						}
					}
				}
			}
		}
	}
}


void CrossIterationRedundancy::CalDependenceForSEInst(Loop * pLoop, set<Instruction *> & SEInst, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG)
{
	set<Instruction *>::iterator itSetInstBegin = SEInst.begin();
	set<Instruction *>::iterator itSetInstEnd   = SEInst.end();

	BasicBlock * pHeader = pLoop->getHeader();

	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
	{
		if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(*itSetInstBegin))
		{
			setDependentValue.insert(pMem);
			continue;
		}

		if(isa<CallInst>(*itSetInstBegin) || isa<InvokeInst>(*itSetInstBegin))
		{
			CallSite cs(*itSetInstBegin);
			Function * pCalled = cs.getCalledFunction();

			if(this->setCallee.find(pCalled) != this->setCallee.end())
			{
				setDependentValue.insert(*itSetInstBegin);
				continue;
			}
		}

		if(isa<PHINode>(*itSetInstBegin) && (*itSetInstBegin)->getParent() == pHeader)
		{
			PHINode * pPHI = cast<PHINode>(*itSetInstBegin);

			for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
			{
				if(pLoop->contains(pPHI->getIncomingBlock(i)))
				{
					setDependentValue.insert(pPHI->getIncomingValue(i));
				}
			}
		}
		else
		{
			vector<Value *> vecValueDependence;
			GetDependingValue(*itSetInstBegin, vecValueDependence);

			vector<Value *>::iterator itVecValueBegin = vecValueDependence.begin();
			vector<Value *>::iterator itVecValueEnd   = vecValueDependence.end();

			if(isa<MemIntrinsic>(*itSetInstBegin))
			{
				itVecValueBegin++;
			}

			for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
			{
				setDependentValue.insert(*itVecValueBegin);
			}
		}

		//add control dependence
		for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
		{
			if(CDG.influences(*BB, (*itSetInstBegin)->getParent()))
			{
				TerminatorInst * pTerminator = (*BB)->getTerminator();
				if(pTerminator !=NULL)
				{
					if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
					{
						if(pBranch->isConditional())
						{
							setDependentValue.insert(pBranch->getCondition());
						}
					}
					else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
					{
						setDependentValue.insert(pSwitch->getCondition());
					}
				}
			}
		}
	}
}

void CrossIterationRedundancy::CIDependenceAnalysis(Loop * pLoop, set<Value *> & setDependentValue, PostDominatorTree * PDT)
{
	BasicBlock * pHeader = pLoop->getHeader();
	Function * pCurrentFunction = pHeader->getParent();

	set<BasicBlock *> setBlockInsideLoop;
	
	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{
		setBlockInsideLoop.insert(*BB);
	}

	ControlDependenceGraphBase CDG;
	CDG.graphForFunction(*pCurrentFunction, *PDT);

	set<Instruction *> setSideEffectInst;
	CollectSideEffectInstsInsideLoop(pLoop, setSideEffectInst, CDG);



	set<Value *> setSEInstDependence ;
	CalDependenceForSEInst(pLoop, setSideEffectInst, setSEInstDependence, CDG);

	LoopDependenceAnalysis(pLoop, setSEInstDependence, setDependentValue, CDG);

	set<Function *>::iterator itSetFuncBegin = this->setCallee.begin();
	set<Function *>::iterator itSetFuncEnd   = this->setCallee.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin++ )
	{
		Function * pCurrentCallee = *itSetFuncBegin;
		int iNumStore = this->IPD->StartEffectStoreMapping[pCurrentCallee].size();
		int iNumMem   = this->IPD->StartEffectMemMapping[pCurrentCallee].size();
		int iNumLibrary = this->IPD->StartLibraryCallMapping[pCurrentCallee].size();

		errs() << iNumStore << " " << iNumMem << " " << iNumLibrary << "\n";
	
		if(iNumStore + iNumMem + iNumLibrary == 0 )
		{
			continue;
		}


		set<Value *> setCDValue;

		set<Instruction *>::iterator itSetCallBegin = this->CalleeCallSiteMapping[pCurrentCallee].begin();
		set<Instruction *>::iterator itSetCallEnd   = this->CalleeCallSiteMapping[pCurrentCallee].end();

		//Control dependence 
		for(; itSetCallBegin != itSetCallEnd; itSetCallBegin ++ )
		{
			//control flow
			for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
			{
				if(CDG.influences(*BB, (*itSetCallBegin)->getParent()))
				{
					TerminatorInst * pTerminator = (*BB)->getTerminator();
					if(pTerminator !=NULL)
					{
						if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
						{
							if(pBranch->isConditional())
							{
								setCDValue.insert(pBranch->getCondition());
							}
						}
						else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
						{
							setCDValue.insert(pSwitch->getCondition());
						}
					}
				}
			}
		}

		LoopDependenceAnalysis(pLoop, setCDValue, setDependentValue, CDG);
	

		vector< set<Value *> > vecArgDependentValue;
		for(size_t i = 0; i < pCurrentCallee->arg_size(); i ++ )
		{
			itSetCallBegin = this->CalleeCallSiteMapping[pCurrentCallee].begin();
			itSetCallEnd   = this->CalleeCallSiteMapping[pCurrentCallee].end();

			set<Value *> setRealPara;

			for(; itSetCallBegin != itSetCallEnd ; itSetCallBegin ++ )
			{
				setRealPara.insert((*itSetCallBegin)->getOperand(i));
			}

			set<Value *> setRealDependentValue;
			LoopDependenceAnalysis(pLoop, setRealPara, setRealDependentValue, CDG);
			vecArgDependentValue.push_back(setRealDependentValue);

		}

		if(iNumStore > 0)
		{
			set<StoreInst *>::iterator itStoreSetBegin = this->IPD->StartEffectStoreMapping[pCurrentCallee].begin();
			set<StoreInst *>::iterator itStoreSetEnd   = this->IPD->StartEffectStoreMapping[pCurrentCallee].end();

			for(; itStoreSetBegin != itStoreSetEnd; itStoreSetBegin ++)
			{
				Function * pContain = (*itStoreSetBegin)->getParent()->getParent();

				set<Value *>::iterator itValSetBegin   = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCurrentCallee][pContain][*itStoreSetBegin].begin();
				set<Value *>::iterator itValSetEnd     = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCurrentCallee][pContain][*itStoreSetBegin].end();

				for(; itValSetBegin != itValSetEnd; itValSetBegin++)
				{
					if(Argument * pArg = dyn_cast<Argument>(*itValSetBegin))
					{
						setDependentValue.insert(vecArgDependentValue[pArg->getArgNo()].begin(), vecArgDependentValue[pArg->getArgNo()].end());
					}
					else
					{
						setDependentValue.insert(*itValSetBegin);
					}
				}
			}
		}


		if(iNumMem > 0 )
		{
			set<MemIntrinsic *>::iterator itMemSetBegin = this->IPD->StartEffectMemMapping[pCurrentCallee].begin();
			set<MemIntrinsic *>::iterator itMemSetEnd   = this->IPD->StartEffectMemMapping[pCurrentCallee].end();

			for(; itMemSetBegin != itMemSetEnd; itMemSetBegin ++ )
			{
				if(MemTransferInst * pMemTransfer = dyn_cast<MemTransferInst>(*itMemSetBegin) )
				{
					if(this->IPD->StartMemTypeMappingMapping[pCurrentCallee][pMemTransfer].second != MO_LOCAL)
					{
						setDependentValue.insert(pMemTransfer);
						continue;
					}
				}

				Function * pContain = (*itMemSetBegin)->getParent()->getParent();

				set<Value *>::iterator itValSetBegin   = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCurrentCallee][pContain][*itMemSetBegin].begin();
				set<Value *>::iterator itValSetEnd     = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCurrentCallee][pContain][*itMemSetBegin].end();

				for(; itValSetBegin != itValSetEnd; itValSetBegin++)
				{
					if(Argument * pArg = dyn_cast<Argument>(*itValSetBegin))
					{
						setDependentValue.insert(vecArgDependentValue[pArg->getArgNo()].begin(), vecArgDependentValue[pArg->getArgNo()].end());
					}
					else
					{
						setDependentValue.insert(*itValSetBegin);
					}
				}
			}
		}

		if(iNumLibrary > 0)
		{
			set<Instruction *>::iterator itCallSetBegin = this->IPD->StartLibraryCallMapping[pCurrentCallee].begin();
			set<Instruction *>::iterator itCallSetEnd   = this->IPD->StartLibraryCallMapping[pCurrentCallee].end();

			for(; itCallSetBegin != itCallSetEnd; itCallSetBegin ++ )
			{
				Function * pContain = (*itCallSetBegin)->getParent()->getParent();

				set<Value *>::iterator itValSetBegin   = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCurrentCallee][pContain][*itCallSetBegin].begin();
				set<Value *>::iterator itValSetEnd     = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCurrentCallee][pContain][*itCallSetBegin].end();

				for(; itValSetBegin != itValSetEnd; itValSetBegin++)
				{
					if(Argument * pArg = dyn_cast<Argument>(*itValSetBegin))
					{						
						setDependentValue.insert(vecArgDependentValue[pArg->getArgNo()].begin(), vecArgDependentValue[pArg->getArgNo()].end());
					}
					else
					{	
						setDependentValue.insert(*itValSetBegin);
					}
				}
			}
		}
	}
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

	this->PDT = &getAnalysis<PostDominatorTree>(*pFunction);
	this->DT  = &getAnalysis<DominatorTree>(*pFunction);
	this->LI = &(getAnalysis<LoopInfo>(*pFunction));
	this->SE = &(getAnalysis<ScalarEvolution>(*pFunction));
	this->pDL = &(getAnalysis<DataLayout>());

	Loop * pLoop; 

	if(strLoopHeader == "")
	{
		pLoop = SearchLoopByLineNo(pFunction, this->LI, uSrcLine);
	}
	else
	{
		BasicBlock * pHeader = SearchBlockByName(pFunction, strLoopHeader);
		
		if(pHeader == NULL)
		{
			errs() << "Cannot find the given loop header!\n";
			return false;
		}

		pLoop = this->LI->getLoopFor(pHeader);
	}

	if(pLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}

	//CollectCalleeInsideLoop(pLoop);
	CollectCalleeInsideLoop(pLoop, this->setCallee, this->CalleeCallSiteMapping, this->LibraryTypeMapping);


	this->IPD = &getAnalysis<InterProcDep>();
	this->IPD->InitlizeStartFunctionSet(this->setCallee);
	this->IPD->LibraryTypeMapping = this->LibraryTypeMapping;
	this->IPD->InterProcDependenceAnalysis();

	set<Value *> setDependentValue;

	CIDependenceAnalysis(pLoop, setDependentValue, PDT);

	char pPath[1000];

	set<Value *>::iterator itSetBegin = setDependentValue.begin();
	set<Value *>::iterator itSetEnd   = setDependentValue.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		if(Instruction * pInst = dyn_cast<Instruction>(*itSetBegin))
		{
			if(isa<AllocaInst>(pInst))
			{
				continue;
			}

			MDNode *Node = pInst->getMetadata("ins_id");
			if(Node!=NULL)
			{
				assert(Node->getNumOperands() == 1);
				ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
				assert(CI);
				errs() << "Inst " << CI->getZExtValue() << ":";
			}

			pInst->dump();

			if( MDNode * N = pInst->getMetadata("dbg") )
			{
				DILocation Loc(N);
				string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
				realpath( sFileNameForInstruction.c_str() , pPath);
				sFileNameForInstruction = string(pPath);                        
				unsigned int uLineNoForInstruction = Loc.getLineNumber();
				errs() << "//---"<< sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
			}

			if(PHINode * pPHI = dyn_cast<PHINode>(pInst))
			{
				if(pPHI->getParent() == pLoop->getHeader() )
				{
					if(IsIterativeVariable(pPHI, pLoop, this->SE))
					{

						errs() << "//---Iterative Variable\n" ;
						int64_t stride = CalculateStride(pPHI, pLoop, this->SE, this->pDL);
				
						if(stride != 0 )
						{
							errs() << "//---stride: " << stride << "\n";
						}
					}
				}	
			}
		}
		else if(Argument * pArg = dyn_cast<Argument>(*itSetBegin))
		{
			Function * pFunction = pArg->getParent();
			MDNode *Node = pFunction->begin()->begin()->getMetadata("func_id");
			if(Node!=NULL)
			{
				assert(Node->getNumOperands() == 1);
				ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
				assert(CI);
				errs() << "Func " << pFunction->getName() << " " << CI->getZExtValue() << " " << pArg->getArgNo() << ": ";
			}

			pArg->dump();
		}
		else
		{
			if(isa<Function>(*itSetBegin))
			{
				continue;
			}

			(*itSetBegin)->dump();
		}
	}

	return false;
}
