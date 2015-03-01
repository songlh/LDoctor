
#include <fstream>

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Metadata.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"

#include "llvm-Commons/Loop/Loop.h"

using namespace llvm;
using namespace std;


namespace llvm_Commons
{

bool blockDominatesAnExit(BasicBlock * BB, DominatorTree & DT, set<BasicBlock *> & setExitBlocks)
{
	DomTreeNode * DomNode = DT.getNode(BB);
	set<BasicBlock *>::iterator itSetBlockBegin = setExitBlocks.begin();
	set<BasicBlock *>::iterator itSetBlockEnd   = setExitBlocks.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++ )
	{
		if(DT.dominates(DomNode, DT.getNode(*itSetBlockBegin)))
		{
			return true;
		}
	}

	return false;
}


bool isExitBlock(BasicBlock *BB, const SmallVectorImpl<BasicBlock*> &ExitBlocks) 
{
	for (unsigned i = 0, e = ExitBlocks.size(); i != e; ++i)
		if (ExitBlocks[i] == BB)
			return true;
	return false;
}

bool ProcessInstruction(Instruction *Inst, const SmallVectorImpl<BasicBlock*> &ExitBlocks, DominatorTree * DT, Loop * L, PredIteratorCache & PredCache) 
{
	SmallVector<Use*, 16> UsesToRewrite;
  
	BasicBlock *InstBB = Inst->getParent();
  
	for (Value::use_iterator UI = Inst->use_begin(), E = Inst->use_end(); UI != E; ++UI) 
	{
		User *U = *UI;
		BasicBlock *UserBB = cast<Instruction>(U)->getParent();
		if (PHINode *PN = dyn_cast<PHINode>(U))
			UserBB = PN->getIncomingBlock(UI);
    
		if (InstBB != UserBB && !L->contains(UserBB))
			UsesToRewrite.push_back(&UI.getUse());
	}

	// If there are no uses outside the loop, exit with no change.
	if (UsesToRewrite.empty()) return false;

	// Invoke instructions are special in that their result value is not available
	// along their unwind edge. The code below tests to see whether DomBB dominates
	// the value, so adjust DomBB to the normal destination block, which is
	// effectively where the value is first usable.
	BasicBlock *DomBB = Inst->getParent();
	if (InvokeInst *Inv = dyn_cast<InvokeInst>(Inst))
		DomBB = Inv->getNormalDest();

	DomTreeNode *DomNode = DT->getNode(DomBB);

	SmallVector<PHINode*, 16> AddedPHIs;

	SSAUpdater SSAUpdate;
	SSAUpdate.Initialize(Inst->getType(), Inst->getName());
  
	// Insert the LCSSA phi's into all of the exit blocks dominated by the
	// value, and add them to the Phi's map.
	for (SmallVectorImpl<BasicBlock*>::const_iterator BBI = ExitBlocks.begin(), BBE = ExitBlocks.end(); BBI != BBE; ++BBI) 
	{
		BasicBlock *ExitBB = *BBI;
		if (!DT->dominates(DomNode, DT->getNode(ExitBB))) continue;
    
		// If we already inserted something for this BB, don't reprocess it.
		if (SSAUpdate.HasValueForBlock(ExitBB)) continue;
    
    	PHINode *PN = PHINode::Create(Inst->getType(), PredCache.GetNumPreds(ExitBB), Inst->getName()+".lcssa", ExitBB->begin());

		// Add inputs from inside the loop for this PHI.
		for (BasicBlock **PI = PredCache.GetPreds(ExitBB); *PI; ++PI) 
		{
			PN->addIncoming(Inst, *PI);

			// If the exit block has a predecessor not within the loop, arrange for
			// the incoming value use corresponding to that predecessor to be
			// rewritten in terms of a different LCSSA PHI.
			if (!L->contains(*PI))
				UsesToRewrite.push_back( &PN->getOperandUse(PN->getOperandNumForIncomingValue(PN->getNumIncomingValues()-1)));
		}

		AddedPHIs.push_back(PN);
    
		// Remember that this phi makes the value alive in this block.
		SSAUpdate.AddAvailableValue(ExitBB, PN);
	}

	// Rewrite all uses outside the loop in terms of the new PHIs we just
	// inserted.
	for (unsigned i = 0, e = UsesToRewrite.size(); i != e; ++i) 
	{
		// If this use is in an exit block, rewrite to use the newly inserted PHI.
		// This is required for correctness because SSAUpdate doesn't handle uses in
		// the same block.  It assumes the PHI we inserted is at the end of the
		// block.
		Instruction *User = cast<Instruction>(UsesToRewrite[i]->getUser());
		BasicBlock *UserBB = User->getParent();
		if (PHINode *PN = dyn_cast<PHINode>(User))
			UserBB = PN->getIncomingBlock(*UsesToRewrite[i]);

		if (isa<PHINode>(UserBB->begin()) && isExitBlock(UserBB, ExitBlocks)) 
		{
			// Tell the VHs that the uses changed. This updates SCEV's caches.
			if (UsesToRewrite[i]->get()->hasValueHandle())
				ValueHandleBase::ValueIsRAUWd(*UsesToRewrite[i], UserBB->begin());
			UsesToRewrite[i]->set(UserBB->begin());
			continue;
		}
    
		// Otherwise, do full PHI insertion.
		SSAUpdate.RewriteUse(*UsesToRewrite[i]);
	}

	// Remove PHI nodes that did not have any uses rewritten.
	for (unsigned i = 0, e = AddedPHIs.size(); i != e; ++i) {
		if (AddedPHIs[i]->use_empty())
			AddedPHIs[i]->eraseFromParent();
	}
  
	return true;
}

BasicBlock * RewriteLoopExitBlock(Loop *L, BasicBlock *Exit, Pass * P)
{
	SmallVector<BasicBlock*, 8> LoopBlocks;
	for (pred_iterator I = pred_begin(Exit), E = pred_end(Exit); I != E; ++I) 
	{
		BasicBlock *P = *I;
		if (L->contains(P)) 
		{
			// Don't do this if the loop is exited via an indirect branch.
			if (isa<IndirectBrInst>(P->getTerminator())) assert(0);

			LoopBlocks.push_back(P);
		}
	}

	assert(!LoopBlocks.empty() && "No edges coming in from outside the loop?");
	BasicBlock *NewExitBB = 0;

	if (Exit->isLandingPad()) 
	{
		assert(0);
	} 
	else 
	{
		NewExitBB = SplitBlockPredecessors(Exit, LoopBlocks, ".CI.loopexit", P);
	}

	return NewExitBB;
}

void LoopSimplify(Loop * pLoop, Pass * P)
{
	Function * pFunction = pLoop->getHeader()->getParent();

	//add predecessor
	BasicBlock * pPreHeader = pLoop->getLoopPreheader();

	if(pPreHeader == NULL)
	{
		BasicBlock *Header = pLoop->getHeader();

		// Compute the set of predecessors of the loop that are not in the loop.
		SmallVector<BasicBlock*, 8> OutsideBlocks;
		for (pred_iterator PI = pred_begin(Header), PE = pred_end(Header); PI != PE; ++PI) 
		{
			BasicBlock *P = *PI;
			if (!pLoop->contains(P)) 
			{   
				// Coming in from outside the loop?
				// If the loop is branched to from an indirect branch, we won't
				// be able to fully transform the loop, because it prohibits
				// edge splitting.
				if (isa<IndirectBrInst>(P->getTerminator())) assert(0);
				// Keep track of it.
				OutsideBlocks.push_back(P);
			}
		}

		// Split out the loop pre-header.
		BasicBlock *PreheaderBB;
		if (!Header->isLandingPad()) 
		{
			PreheaderBB = SplitBlockPredecessors(Header, OutsideBlocks, ".CI.preheader", P);
		} 
		else 
		{
			assert(0);
		}
	}

	SmallVector<BasicBlock*, 8> ExitBlocks;
	pLoop->getExitBlocks(ExitBlocks);

	set<BasicBlock *> ExitBlockSet(ExitBlocks.begin(), ExitBlocks.end());

	for (set<BasicBlock *>::iterator I = ExitBlockSet.begin(), E = ExitBlockSet.end(); I != E; ++I) 
	{
    	BasicBlock * ExitBlock = *I;
		for (pred_iterator PI = pred_begin(ExitBlock), PE = pred_end(ExitBlock); PI != PE; ++PI)
		{
			if (!pLoop->contains(*PI)) 
			{
				RewriteLoopExitBlock(pLoop, ExitBlock, P);
				break;
			}
		}
	}


	DominatorTree DT;
	DT.runOnFunction(*pFunction);
	PredIteratorCache PredCache;

	for(Loop::block_iterator BBI = pLoop->block_begin(), BBE = pLoop->block_end(); BBI != BBE; ++BBI)
	{
		BasicBlock * BB = *BBI;

		if(!blockDominatesAnExit(BB, DT, ExitBlockSet))
		{
			continue;
		}

		for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) 
		{
			// Reject two common cases fast: instructions with no uses (like stores)
			// and instructions with one use that is in the same block as this.
			if (I->use_empty() || (I->hasOneUse() && I->use_back()->getParent() == BB && !isa<PHINode>(I->use_back())))
				continue;
			
			ProcessInstruction(I, ExitBlocks, &DT, pLoop, PredCache);
		}
	}
}

void ProcessPHICondition(PHINode * pPHI, set<Instruction *> & setInputInst)
{
	set<Instruction *> setProcessed;
	setProcessed.insert(pPHI);

	vector<PHINode *> vecWorkList;
	vecWorkList.push_back(pPHI);

	while(vecWorkList.size()>0)
	{
		PHINode * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		for(unsigned i = 0; i < pCurrent->getNumIncomingValues(); i ++)
		{
			if(Instruction * pInst = dyn_cast<Instruction>(pCurrent->getIncomingValue(i)))
			{
				if(PHINode * pNew = dyn_cast<PHINode>(pInst))
				{
					if(setProcessed.find(pNew) == setProcessed.end())
					{
						setProcessed.insert(pNew);
						vecWorkList.push_back(pNew);
					}
				}
				else
				{
					setInputInst.insert(pInst);
				}
			}
			else if(isa<ConstantInt>(pCurrent->getIncomingValue(i)))
			{
				TerminatorInst * pTerminator = pCurrent->getIncomingBlock(i)->getTerminator();

				if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
				{
					if(Instruction * pInst = dyn_cast<Instruction>(pBranch->getCondition()))
					{
						if(PHINode * pNew = dyn_cast<PHINode>(pInst))
						{
							if(setProcessed.find(pNew) == setProcessed.end() )
							{
								setProcessed.insert(pNew);
								vecWorkList.push_back(pNew);
							}
						}
						else
						{
							setInputInst.insert(pInst);
						}
					}
				}
				else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
				{
					if(Instruction * pInst = dyn_cast<Instruction>(pSwitch->getCondition()))
					{
						if(PHINode * pNew = dyn_cast<PHINode>(pInst))
						{
							if(setProcessed.find(pNew) == setProcessed.end() )
							{
								setProcessed.insert(pNew);
								vecWorkList.push_back(pNew);
							}
						}
						else
						{
							setInputInst.insert(pInst);
						}
					}
				}
			}
		}
	}
}

void CollectExitCondition(Loop * pLoop, set<Instruction *> & setExitCond )
{
	for(Loop::block_iterator pBB = pLoop->block_begin(); pBB != pLoop->block_end(); pBB ++ )
	{
		BasicBlock * BB = * pBB;
		TerminatorInst * pTerminator = BB->getTerminator();

		if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
		{
			bool bFlag = false;

			for(unsigned i = 0; i < pBranch->getNumSuccessors(); i ++ )
			{
				if(!pLoop->contains(pBranch->getSuccessor(i)))
				{
					bFlag = true;
					break;
				}
			}

			if(bFlag)
			{
				if(Instruction * pInst = dyn_cast<Instruction>(pBranch->getCondition()))
				{
					if(PHINode * pPHI = dyn_cast<PHINode>(pInst))
					{
						set<Instruction *> setInputInst ;
						ProcessPHICondition(pPHI, setInputInst);
						setExitCond.insert(setInputInst.begin(), setInputInst.end());
					}
					else
					{
						setExitCond.insert(pInst);
					}
				}
			}
		}
		else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
		{
			bool bFlag = false;

			for(unsigned i = 0; i < pSwitch->getNumSuccessors(); i ++ )
			{
				if(!pLoop->contains(pSwitch->getSuccessor(i)))
				{
					bFlag = true;
					break;
				}
			}

			if(bFlag)
			{
				if(Instruction * pInst = dyn_cast<Instruction>(pSwitch->getCondition()))
				{
					if(PHINode * pPHI = dyn_cast<PHINode>(pInst))
					{
						set<Instruction *> setInputInst;
						ProcessPHICondition(pPHI, setInputInst);
						setExitCond.insert(setInputInst.begin(), setInputInst.end());
					}
					else
					{
						setExitCond.insert(pInst);
					}
				}
			}
		}
	}
}

void CollectAllUsesInsideLoop(Value * pValue, Loop * pLoop, set<PHINode *> & UseOne, set<Instruction *> & UseOther)
{
	for(Value::use_iterator UI = pValue->use_begin(); UI != pValue->use_end(); UI ++ )
	{
		User * U = * UI;
		Instruction * pInst = cast<Instruction>(U);

		if(pLoop->contains(pInst->getParent()))
		{
			if(PHINode * pPHI = dyn_cast<PHINode>(pInst))
			{
				for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
				{
					if(pPHI->getIncomingValue(i) == pValue && !pLoop->contains(pPHI->getIncomingBlock(i)))
					{
						UseOne.insert(pPHI);
					}
					else if(pPHI->getIncomingValue(i) == pValue && pLoop->contains(pPHI->getIncomingBlock(i)))
					{
						UseOther.insert(pPHI);
					}
				}
			}
			else
			{
				UseOther.insert(pInst);
			}
		}
	}
}

bool UsedInsideLoop(Value * pValue, Loop * pLoop)
{
	for(Value::use_iterator UI = pValue->use_begin(); UI != pValue->use_end(); UI ++ )
	{
		User * U = *UI;
		Instruction * pInst = cast<Instruction>(U);

		if(pLoop->contains(pInst->getParent()))
		{
			return true;
		}
	}

	return false;
}

bool OnlyControlInLoop(Value * pValue, Loop * pLoop)
{
	bool bFlag = false;

	for(Value::use_iterator UI = pValue->use_begin(); UI != pValue->use_end(); UI ++ )
	{
		User * U = *UI;

		Instruction * pInst = cast<Instruction>(U);

		if(!pLoop->contains(pInst->getParent()))
		{
			continue;
		}

		bFlag = true;

		if(!isa<CmpInst>(pInst))
		{
			return false;
		}

		for(Value::use_iterator CmpUI = pInst->use_begin(); CmpUI != pInst->use_end(); CmpUI ++)
		{
			User * CmpU = *CmpUI;
			Instruction * pCmpUInst = cast<Instruction>(CmpU);

			if(!pLoop->contains(pCmpUInst->getParent()))
			{
				continue;
			}

			if(!isa<BranchInst>(pCmpUInst))
			{
				return false;
			}
		}
	}

	return bFlag;
}


bool OnlyCompWithInteger(Value * pValue, Loop * pLoop)
{
	if(!isa<IntegerType>(pValue->getType()))
	{
		return false;
	}

	set<Instruction *> setProcessed;
	vector<Instruction *> vecWorkList;

	for(Value::use_iterator UI = pValue->use_begin(); UI != pValue->use_end(); UI ++ )
	{
		User * U = *UI;
		Instruction * pInst = cast<Instruction>(U);

		if(!pLoop->contains(pInst->getParent()))
		{
			continue;
		}

		for(unsigned i = 0; i < pInst->getNumOperands(); i ++ )
		{
			if(pInst->getOperand(i) == pValue)
			{
				continue;
			}

			if(Instruction * pI = dyn_cast<Instruction>(pInst->getOperand(i)))
			{
				if(!pLoop->contains(pI->getParent()))
				{
					continue;
				}

				if(setProcessed.find(pI) == setProcessed.end())
				{
					setProcessed.insert(pI);
					vecWorkList.push_back(pI);
				}
			}
		}
	}

	while(vecWorkList.size() >0)
	{
		Instruction * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		if(isa<CastInst>(pCurrent) || isa<BinaryOperator>(pCurrent) || isa<PHINode>(pCurrent) || isa<CmpInst>(pCurrent) )
		{
			for(unsigned i = 0; i < pCurrent->getNumOperands(); i ++ )
			{
				if(pCurrent->getOperand(i) == pValue)
				{
					continue;
				}

				if(Instruction * pI = dyn_cast<Instruction>(pCurrent->getOperand(i)))
				{
					if(!pLoop->contains(pI->getParent()))
					{
						continue;
					}

					if(setProcessed.find(pI) == setProcessed.end())
					{
						setProcessed.insert(pI);
						vecWorkList.push_back(pI);
					}
				}
			}
		}
		else
		{
			return false;
		}
	}


	return true;

}



}

