#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm-Commons/Array/Array.h"
#include "llvm-Commons/Loop/Loop.h"
#include "llvm-Commons/SEWrapper/SEWrapper.h"

#include <stdlib.h>
#include <stdio.h>

namespace llvm_Commons
{

/*
bool decodeSCEV(const SCEV * pSCEV, set<Value *> & setValue)
{
	if(const SCEVCastExpr * pCast = dyn_cast<const SCEVCastExpr>(pSCEV))
	{
		return decodeSCEV(pCast->getOperand(), setValue);
	}
	else if(const SCEVConstant * pConstant = dyn_cast<const SCEVConstant>(pSCEV))
	{
		setValue.insert(pConstant->getValue());
		return true;
	}
	else if(isa<const SCEVCouldNotCompute>(pSCEV))
	{
		return false;
	}
	else if(const SCEVNAryExpr * pNAry = dyn_cast<const SCEVNAryExpr>(pSCEV))
	{
		for(size_t i = 0; i < pNAry->getNumOperands(); i ++ )
		{
			if(!decodeSCEV(pNAry->getOperand(i), setValue))
			{
				return false;
			}
		}

		return true;
	}
	else if(const SCEVUDivExpr * pDiv = dyn_cast<const SCEVUDivExpr>(pSCEV))
	{
		if(!decodeSCEV(pDiv->getLHS(), setValue))
		{
			return false;
		}

		return decodeSCEV(pDiv->getRHS(), setValue);
	}
	else if(const SCEVUnknown * pUnknown = dyn_cast<const SCEVUnknown>(pSCEV))
	{
		Type * AllocTy;
		Constant * FieldNo;

		if(pUnknown->isSizeOf(AllocTy))
		{
			return true;
		}
		else if(pUnknown->isAlignOf(AllocTy))
		{
			return true;
		}
		else if(pUnknown->isOffsetOf(AllocTy, FieldNo))
		{
			return true;
		}

		setValue.insert(pUnknown->getValue());
		return true;
	}

	return false;
}

bool hasConstantStride(PHINode * pPHI, ScalarEvolution * SE, DataLayout * pDL)
{
	const SCEV * pSCEV = SE->getSCEV(pPHI);

	if(const SCEVAddRecExpr * pAdd = dyn_cast<const SCEVAddRecExpr>(pSCEV))
	{
		int64_t stride;
		if(getSignedValue(pAdd->getOperand(1), stride, pDL))
		{
			return true;
		}
	}

	return false;
}

bool isArrayLoop(Loop * pLoop, map<Instruction *, set<Value *> > & ArrayAccessBoundayMapping, ScalarEvolution * SE)
{
	return false;
}

void collectPossibleValue(Loop * pLoop, PHINode * pPHI, set<Instruction * > & setPossibleValue)
{
	set<Instruction *> setPHIValue;
	setPHIValue.insert(pPHI);

	vector<Instruction *> vecWorkList;
	vecWorkList.push_back(pPHI);

	while(vecWorkList.size() > 0)
	{
		Instruction * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		if(PHINode * pPHI = dyn_cast<PHINode>(pCurrent))
		{	
			for(unsigned i = 0 ; i < pPHI->getNumIncomingValues(); i ++ )
			{
				if(Instruction * pInst = dyn_cast<Instruction>(pPHI->getIncomingValue(i)))
				{
					if(!pLoop->contains(pInst->getParent()))
					{
						continue;
					}

					if(setPHIValue.find(pInst) == setPHIValue.end())
					{
						setPHIValue.insert(pInst);
						if(PHINode * pPHI = dyn_cast<PHINode>(pInst))
						{
							vecWorkList.push_back(pPHI);
						}
					}
				}
			}
		}
	}

	set<Instruction *>::iterator itSetValBegin = setPHIValue.begin();
	set<Instruction *>::iterator itSetValEnd   = setPHIValue.end();

	for(; itSetValBegin != itSetValEnd; itSetValBegin ++ )
	{
		setPossibleValue.insert(*itSetValBegin);

		for(Value::use_iterator UI = (*itSetValBegin)->use_begin(); UI != (*itSetValBegin)->use_end(); UI ++ )
		{
			User * U = * UI;
			Instruction * pUseInst = cast<Instruction>(U);

			if(!pLoop->contains(pUseInst->getParent()))
			{
				continue;
			}

			if(CastInst * pCast = dyn_cast<CastInst>(pUseInst))
			{
				setPossibleValue.insert(pCast);
			}
		}
	}

}


void collectIterativeVariable(Loop * pLoop, map<Instruction *, vector<Value * > > & mapBoundary, ScalarEvolution * SE, DataLayout * pDL)
{
	BasicBlock * pHeader = pLoop->getHeader();
	const SCEV * pTripCounter = SE->getBackedgeTakenCount(pLoop);

	for(BasicBlock::iterator II = pHeader->begin(); II != pHeader->end(); II ++ )
	{
		if(PHINode * pPHI = dyn_cast<PHINode>(II))
		{
			const SCEV * pSCEV = SE->getSCEV(pPHI);

			if(const SCEVAddRecExpr * pAdd = dyn_cast<const SCEVAddRecExpr>(pSCEV))
			{
				int64_t stride;

				if(!getSignedValue(pAdd->getOperand(1), stride, pDL))
				{
					continue;
				}

				set<Value *> setValue;

				if(!decodeSCEV(pAdd->getOperand(0), setValue))
				{
					continue;
				}

				set<Value *>::iterator itSetValBegin = setValue.begin();
				set<Value *>::iterator itSetValEnd   = setValue.end();

				for(; itSetValBegin != itSetValEnd; itSetValBegin ++ )
				{
					if(isa<Constant>(*itSetValBegin))
					{
						continue;
					}
					else if(isa<Instruction>(*itSetValBegin))
					{
						mapBoundary[pPHI].push_back(*itSetValBegin);
					}
					else if(isa<Argument>(*itSetValBegin))
					{
						mapBoundary[pPHI].push_back(*itSetValBegin);
					}
					else
					{
						assert(0);
					}
				}


				if(const SCEVUnknown * pUnknown = dyn_cast<SCEVUnknown>(pTripCounter))
				{
					mapBoundary[pPHI].push_back(pUnknown->getValue());
				}

				set<Instruction *> setExitCond;
				CollectExitCondition(pLoop, setExitCond);

				set<Instruction * > setPossibleValue;
				collectPossibleValue(pLoop, pPHI, setPossibleValue);

				set<Instruction *>::iterator itSetInstBegin = setExitCond.begin();
				set<Instruction *>::iterator itSetInstEnd   = setExitCond.end();

				for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
				{
					if(CmpInst * pCmp = dyn_cast<CmpInst>(*itSetInstBegin))
					{
						if(Instruction * pFirst = dyn_cast<Instruction>(pCmp->getOperand(0)))
						{
							if(setPossibleValue.find(pFirst) != setPossibleValue.end())
							{
								if(Instruction * pSecond = dyn_cast<Instruction>(pCmp->getOperand(1)))
								{
									if(!pLoop->contains(pSecond->getParent()))
									{
										mapBoundary[pPHI].push_back(pSecond);
									}
								}
								else if(isa<Argument>(pCmp->getOperand(1)))
								{
									mapBoundary[pPHI].push_back(pCmp->getOperand(1));
								}
							}
						}

						if(Instruction * pSecond = dyn_cast<Instruction>(pCmp->getOperand(1)))
						{
							if(setPossibleValue.find(pSecond) != setPossibleValue.end())
							{
								if(Instruction * pFirst = dyn_cast<Instruction>(pCmp->getOperand(0)))
								{
									if(!pLoop->contains(pFirst->getParent()))
									{
										mapBoundary[pPHI].push_back(pFirst);
									}
								}
								else if(isa<Argument>(pCmp->getOperand(0)))
								{
									mapBoundary[pPHI].push_back(pCmp->getOperand(0));
								}
							}
						}
					}
					else
					{
						assert(0);
					}
				}
			}
		}
	}
}

bool isArrayLoop(Loop * pLoop, ScalarEvolution * SE, DataLayout * pDL)
{
	vector<Instruction *> vecMemAccess;

	for(Loop::block_iterator pBB = pLoop->block_begin(); pBB != pLoop->block_end(); pBB ++ )
	{
		BasicBlock * BB = *pBB;

		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			vector<const SCEV *> vecSCEV;

			if(StoreInst * pStore = dyn_cast<StoreInst>(II))
			{
				const SCEV * S = SE->getSCEV(pStore->getPointerOperand());
				vecSCEV.push_back(S); 
			}
			else if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
			{
				const SCEV * S = SE->getSCEV(pLoad->getPointerOperand());
				vecSCEV.push_back(S);
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
			{
				const SCEV * S = SE->getSCEV(pMem->getRawSource());
				vecSCEV.push_back(S);

				S = SE->getSCEV(pMem->getRawDest());
				vecSCEV.push_back(S);
			}

			vector<const SCEV *>::iterator itVecBegin = vecSCEV.begin();
			vector<const SCEV *>::iterator itVecEnd   = vecSCEV.end();

			for(; itVecBegin != itVecEnd; itVecBegin ++ )
			{
				if(const SCEVAddRecExpr * pAdd = dyn_cast<const SCEVAddRecExpr>(*itVecBegin))
				{
					int64_t stride;

					if(!getSignedValue(pAdd->getOperand(1), stride, pDL))
					{
						continue;
					}

					if(stride < 0)
					{
						stride = (-1) * stride;
					}

					int64_t size = -1;

					if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
					{
						size = pDL->getTypeSizeInBits(pLoad->getType())/8;
					}
					else if(StoreInst * pStore = dyn_cast<StoreInst>(II))
					{
						size = pDL->getTypeSizeInBits(pStore->getValueOperand()->getType())/8;
					}
					else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
					{
						if(ConstantInt * pConstant = dyn_cast<ConstantInt>(pMem->getLength()))
						{
							size = pConstant->getLimitedValue();
						}
					}

					if(stride != size)
					{
						continue;
					}

					vecMemAccess.push_back(II);

				}
			}
		}
	}

	return false;
}
*/

bool BeArrayAccess(Loop * pLoop, LoadInst * pLoad, ScalarEvolution * SE, DataLayout * DL)
{
	Value * pPointer = pLoad->getPointerOperand();

	int64_t iLoadSize = 0;

	if(PointerType * pPointerType = dyn_cast<PointerType>(pPointer->getType()))
	{
		iLoadSize = pPointerType->getElementType()->getPrimitiveSizeInBits()/8;
	}

	int64_t iStride = CalculateStride(pPointer, pLoop, SE, DL);
	//errs() << "stride: " << iStride << "\n";

	if(iStride == 0)
	{
		return false;
	}

	if(abs(iStride) >= iLoadSize)
	{
		return true;
	}
	else
	{
		return false;
	}
}

bool BeArrayWrite(Loop * pLoop, StoreInst * pStore, ScalarEvolution * SE, DataLayout * DL)
{
	Value * pPointer = pStore->getPointerOperand();

	int64_t iStoreSize = 0;


	if(PointerType * pPointerType = dyn_cast<PointerType>(pPointer->getType()))
	{
		iStoreSize = pPointerType->getElementType()->getPrimitiveSizeInBits()/8;
	}

	int64_t iStride = CalculateStride(pPointer, pLoop, SE, DL);

	if(iStride == 0)
	{
		return false;
	}

	if(abs(iStride) == iStoreSize)
	{
		return true;
	}
	else
	{
		return false;
	}
}

/*
void CalCulateBaseAddress(LoadInst * pLoad, Loop * pLoop, ScalarEvolution * SE, DataLayout * DL, set<Value *> & setArrayBase)
{
	Value * pPointer = pLoad->getPointerOperand();
	Value * pBase = GetUnderlyingObject(pPointer, DL);

	//pBase is defined outside the loop
	if(pLoop->isLoopInvariant(pBase))
	{
		setArrayBase.insert(pBase);

		return;
	}

	//If the address is PHINode, value defined outside the loop is the possible base
	if(PHINode * pPHI = dyn_cast<PHINode>(pBase))
	{
		for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
		{
			if(!pLoop->contains(pPHI->getIncomingBlock(i)))
			{
				setArrayBase.insert(pPHI->getIncomingValue(i));
			}
		}
	}

	return;
}
*/


void AnalyzeArrayAccess(LoadInst * pLoad, Loop * pLoop, ScalarEvolution * SE, DataLayout * DL, vector<set<Value *> > & vecResult)
{
	set<Value *> setArrayBase;
	set<Value *> setArrayInit;
	set<Value *> setArrayIndex;

	Value * pPointer = pLoad->getPointerOperand();
	Value * pBase = GetUnderlyingObject(pPointer, DL);
	BasicBlock * pHeader = pLoop->getHeader();
	
	if(pLoop->isLoopInvariant(pBase))
	{
		setArrayBase.insert(pBase);

		Instruction * pPointerInst = cast<Instruction>(pPointer);

		while(isa<CastInst>(pPointerInst))
		{
			pPointerInst = cast<Instruction>(cast<CastInst>(pPointerInst)->getOperand(0));
		}

		if(!isa<GetElementPtrInst>(pPointerInst))
		{
			vecResult.push_back(setArrayBase);
			vecResult.push_back(setArrayInit);
			vecResult.push_back(setArrayIndex);
			return;
		}

		Instruction * pIndexInst = cast<Instruction>(pPointerInst->getOperand(1));


		for(BasicBlock::iterator II = pHeader->begin(); II != pHeader->end(); II ++ )
		{
			if(PHINode * pPHI = dyn_cast<PHINode>(II))
			{
				set<Value *> setPossible;
				vector<Value *> vecTodo;

				vecTodo.push_back(pPHI);

				for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
				{
					vecTodo.push_back(pPHI->getIncomingValue(i));
				}

				while(vecTodo.size() > 0)
				{
					Value * pCurrent = vecTodo.back();
					vecTodo.pop_back();

					setPossible.insert(pCurrent);

					for(Value::use_iterator UI = pCurrent->use_begin(); UI != pCurrent->use_end(); UI ++ )
					{
						User *U = *UI;

						if(isa<CastInst>(U))
						{
							vecTodo.push_back(cast<Instruction>(U));
						}
					}	
				}

				if(setPossible.find(pIndexInst) != setPossible.end())
				{
					for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
					{
						if(!pLoop->contains(pPHI->getIncomingBlock(i)))
						{
							setArrayInit.insert(pPHI->getIncomingValue(i));
						}
					}

					setArrayIndex.insert(pPHI);
				}
			}
		}

		vecResult.push_back(setArrayBase);
		vecResult.push_back(setArrayInit);
		vecResult.push_back(setArrayIndex);

		return;
	}

	//If the address is PHINode, value defined outside the loop is the possible base
	if(PHINode * pPHI = dyn_cast<PHINode>(pBase))
	{
		if(pPHI->getParent() == pHeader)
		{
			for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
			{
				if(!pLoop->contains(pPHI->getIncomingBlock(i)))
				{
					setArrayBase.insert(pPHI->getIncomingValue(i));
					setArrayInit.insert(pPHI->getIncomingValue(i));
				}
			}

			setArrayIndex.insert(pPHI);
		}
	}


	vecResult.push_back(setArrayBase);
	vecResult.push_back(setArrayInit);
	vecResult.push_back(setArrayIndex);

	return;

}

}

