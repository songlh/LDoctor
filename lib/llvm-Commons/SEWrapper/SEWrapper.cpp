
#include "llvm-Commons/SEWrapper/SEWrapper.h"
#include "llvm-Commons/Loop/Loop.h"

#include <queue>
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

using namespace llvm;
using namespace std;


namespace llvm_Commons
{

void SearchParentInst(const SCEV * pParent, const SCEV * pChild, map<const SCEV *, set<Value * > > & SCEVValMapping)
{
	set<Value *>::iterator itValBegin = SCEVValMapping[pChild].begin();
	set<Value *>::iterator itValEnd   = SCEVValMapping[pChild].end();

	set<Value *> toRemoved;

	bool bNotFound = true;

	for(; itValBegin != itValEnd; itValBegin ++ )
	{
		Value * pCurrentValue = *itValBegin;

		for(Value::use_iterator UI = pCurrentValue->use_begin(); UI != pCurrentValue->use_end(); UI ++ )
		{
			User * U = *UI;
			Instruction * pInst = cast<Instruction>(U);

			if(isa<const SCEVSignExtendExpr>(pParent))
			{
				if(pInst->getOpcode() != Instruction::SExt)
				{
					continue;
				}

				SCEVValMapping[pParent].insert(pInst);
				bNotFound = false;
			}
			else if(isa<const SCEVTruncateExpr>(pParent))
			{
				if(pInst->getOpcode() != Instruction::Trunc)
				{
					continue;
				}

				SCEVValMapping[pParent].insert(pInst);
				bNotFound = false;
			}
			else if(isa<const SCEVZeroExtendExpr>(pParent))
			{
				if(pInst->getOpcode() != Instruction::ZExt)
				{
					continue;
				}

				SCEVValMapping[pParent].insert(pInst);
				bNotFound = false;
			}
			else if(isa<const SCEVAddRecExpr>(pParent))
			{
				if(pInst->getOpcode() != Instruction::Add && pInst->getOpcode() != Instruction::Sub)
				{
					continue;
				}

				SCEVValMapping[pParent].insert(pInst);
				bNotFound = false;
			}
			else if(isa<const SCEVAddExpr>(pParent))
			{
				if(pInst->getOpcode() != Instruction::Add && pInst->getOpcode() != Instruction::Sub)
				{
					continue;
				}

				SCEVValMapping[pParent].insert(pInst);
				bNotFound = false;
			}
			else if(isa<const SCEVMulExpr>(pParent))
			{
				if(pInst->getOpcode() != Instruction::Mul )
				{
					continue;
				}

				SCEVValMapping[pParent].insert(pInst);
				bNotFound = false;
			}
			else if(isa<const SCEVUDivExpr>(pParent))
			{
				if(pInst->getOpcode() != Instruction::UDiv)
				{
					continue;
				}

				SCEVValMapping[pParent].insert(pInst);
				bNotFound = false;
			}
			else
			{
				assert(0);
			}

		}

		if(bNotFound)
		{
			toRemoved.insert(*itValBegin);
		}
	}


	itValBegin = toRemoved.begin();
	itValEnd   = toRemoved.end();

	for(; itValBegin != itValEnd; itValBegin ++ )
	{
		SCEVValMapping[pChild].erase(*itValBegin);
	}
}


void DecodeTripCounterSCEV(const SCEV * pSCEV, Loop * pLoop, set<Value *> & setTripCounter)
{
	map<const SCEV *, const SCEV *> SCEVParentMapping;
	queue<const SCEV *> vecWorkList;
	vecWorkList.push(pSCEV);
	vector<const SCEV *> vecBaseSCEV;
	set<const SCEV *> setConstant;

	while(vecWorkList.size()>0)
	{
		const SCEV * pCurrent = vecWorkList.front();
		vecWorkList.pop();

		if(const SCEVCastExpr * pCast = dyn_cast<const SCEVCastExpr>(pCurrent))
		{
			const SCEV * pNext = pCast->getOperand();
			SCEVParentMapping[pNext] = pCurrent;
			vecWorkList.push(pNext);
		}
		else if(const SCEVConstant * pConstant = dyn_cast<const SCEVConstant>(pCurrent))
		{
			setConstant.insert(pConstant);
		}
		else if(isa<const SCEVCouldNotCompute>(pCurrent))
		{
			assert(0);
		}
		else if(const SCEVNAryExpr * pNAry = dyn_cast<const SCEVNAryExpr>(pCurrent))
		{
			for(size_t i = 0; i < pNAry->getNumOperands(); i++)
			{
				const SCEV * pNext = pNAry->getOperand(i);
				SCEVParentMapping[pNext] = pNAry;
				vecWorkList.push(pNext);
			}
		}
		else if(const SCEVUDivExpr * pDiv = dyn_cast<const SCEVUDivExpr>(pCurrent))
		{
			const SCEV * pLeft = pDiv->getLHS();
			SCEVParentMapping[pLeft] = pDiv;
			vecWorkList.push(pLeft);

			const SCEV * pRight = pDiv->getRHS();
			SCEVParentMapping[pRight] = pDiv;
			vecWorkList.push(pRight);
		}
		else if(const SCEVUnknown * pUnknown = dyn_cast<SCEVUnknown>(pCurrent))
		{
			vecBaseSCEV.push_back(pUnknown);
		}
	}

	map<const SCEV *, set<Value * > > SCEVValMapping;

	vector<const SCEV *>::iterator itSCEVBegin = vecBaseSCEV.begin();
	vector<const SCEV *>::iterator itSCEVEnd   = vecBaseSCEV.end();

	for(; itSCEVBegin != itSCEVEnd; itSCEVBegin ++ )
	{
		vecWorkList.push(*itSCEVBegin);

		while(vecWorkList.size()>0 )
		{
			const SCEV * pCurrent = vecWorkList.front();
			vecWorkList.pop();

			if(const SCEVUnknown * pUnknown = dyn_cast<SCEVUnknown>(pCurrent) )
			{
				Value * pRelatedValue = pUnknown->getValue();

				if(UsedInsideLoop(pRelatedValue, pLoop))
				{
					setTripCounter.insert(pRelatedValue);
					continue;
				}

				SCEVValMapping[pUnknown].insert(pRelatedValue);
				SearchParentInst(SCEVParentMapping[pUnknown], pUnknown, SCEVValMapping);
				vecWorkList.push(SCEVParentMapping[pUnknown]);
			}
			else
			{
				set<Value *>::iterator itSetValueBegin = SCEVValMapping[pCurrent].begin();
				set<Value *>::iterator itSetValueEnd   = SCEVValMapping[pCurrent].end();

				bool bFlag = false;

				for(; itSetValueBegin != itSetValueEnd; itSetValueBegin++ )
				{
					if(UsedInsideLoop(*itSetValueBegin, pLoop))
					{
						setTripCounter.insert(*itSetValueBegin);	
						bFlag = true;			
					}
				}

				if(bFlag)
				{
					continue;
				}

				SearchParentInst(SCEVParentMapping[pCurrent], pCurrent, SCEVValMapping);
				vecWorkList.push(SCEVParentMapping[pCurrent]);
			}
		}
	}
}

const SCEV * DecondeTripCounterSCEV(const SCEV * pSCEV, Loop * pLoop, ScalarEvolution * SE)
{
	map<const SCEV *, const SCEV *> SCEVParentMapping;
	queue<const SCEV *> vecWorkList;
	vecWorkList.push(pSCEV);

	vector<const SCEV *> vecBaseSCEV;
	set<const SCEV *> setConstant;

	while(vecWorkList.size()>0)
	{
		const SCEV * pCurrent = vecWorkList.front();
		vecWorkList.pop();

		if(const SCEVCastExpr * pCast = dyn_cast<const SCEVCastExpr>(pCurrent))
		{
			const SCEV * pNext = pCast->getOperand();
			SCEVParentMapping[pNext] = pCurrent;
			vecWorkList.push(pNext);
		}
		else if(const SCEVConstant * pConstant = dyn_cast<const SCEVConstant>(pCurrent))
		{
			setConstant.insert(pConstant);
		}
		else if(isa<const SCEVCouldNotCompute>(pCurrent))
		{
			assert(0);
		}
		else if(const SCEVNAryExpr * pNAry = dyn_cast<const SCEVNAryExpr>(pCurrent))
		{
			for(size_t i = 0; i < pNAry->getNumOperands(); i++)
			{
				const SCEV * pNext = pNAry->getOperand(i);
				SCEVParentMapping[pNext] = pNAry;
				vecWorkList.push(pNext);
			}
		}
		else if(const SCEVUDivExpr * pDiv = dyn_cast<const SCEVUDivExpr>(pCurrent))
		{
			const SCEV * pLeft = pDiv->getLHS();
			SCEVParentMapping[pLeft] = pDiv;
			vecWorkList.push(pLeft);

			const SCEV * pRight = pDiv->getRHS();
			SCEVParentMapping[pRight] = pDiv;
			vecWorkList.push(pRight);
		}
		else if(const SCEVUnknown * pUnknown = dyn_cast<SCEVUnknown>(pCurrent))
		{
			vecBaseSCEV.push_back(pUnknown);
		}
	}

	map<const SCEV *, set<Value * > > SCEVValMapping;

	vector<const SCEV *>::iterator itSCEVBegin = vecBaseSCEV.begin();
	vector<const SCEV *>::iterator itSCEVEnd   = vecBaseSCEV.end();

	map<Value *, const SCEV *> ValSCEVMapping;

	for(; itSCEVBegin != itSCEVEnd; itSCEVBegin ++ )
	{
		vecWorkList.push(*itSCEVBegin);

		while(vecWorkList.size()>0 )
		{
			const SCEV * pCurrent = vecWorkList.front();
			vecWorkList.pop();

			if(const SCEVUnknown * pUnknown = dyn_cast<SCEVUnknown>(pCurrent) )
			{
				Value * pRelatedValue = pUnknown->getValue();

				if(UsedInsideLoop(pRelatedValue, pLoop))
				{
					ValSCEVMapping[pRelatedValue] = pUnknown;
					continue;
				}

				SCEVValMapping[pUnknown].insert(pRelatedValue);
				SearchParentInst(SCEVParentMapping[pUnknown], pUnknown, SCEVValMapping);
				vecWorkList.push(SCEVParentMapping[pUnknown]);
			}
			else
			{
				set<Value *>::iterator itSetValueBegin = SCEVValMapping[pCurrent].begin();
				set<Value *>::iterator itSetValueEnd   = SCEVValMapping[pCurrent].end();

				bool bFlag = false;

				for(; itSetValueBegin != itSetValueEnd; itSetValueBegin++ )
				{
					if(UsedInsideLoop(*itSetValueBegin, pLoop))
					{
						//setTripCounter.insert(*itSetValueBegin);
						ValSCEVMapping[*itSetValueBegin] = pCurrent;	
						bFlag = true;			
					}
				}

				if(bFlag)
				{
					continue;
				}

				SearchParentInst(SCEVParentMapping[pCurrent], pCurrent, SCEVValMapping);
				vecWorkList.push(SCEVParentMapping[pCurrent]);
			}
		}
	}

	map<Value *, const SCEV *>::iterator itMapBegin = ValSCEVMapping.begin();
	map<Value *, const SCEV *>::iterator itMapEnd   = ValSCEVMapping.end();

	//const SCEV * pResult = NULL;
	const SCEV * pNew = NULL;

	for(; itMapBegin != itMapEnd; itMapBegin++ )
	{
		const SCEV * pCurrent = itMapBegin->second;
		pNew = SE->getUnknown(itMapBegin->first);

		while(SCEVParentMapping.find(pCurrent) != SCEVParentMapping.end())
		{
			const SCEV * pParent = SCEVParentMapping[pCurrent];

			if(const SCEVSignExtendExpr * pSign = dyn_cast<const SCEVSignExtendExpr>(pParent))
			{
				pNew = SE->getSignExtendExpr(pNew, pSign->getType());
			}
			else if(const SCEVTruncateExpr * pTrunk = dyn_cast<const SCEVTruncateExpr>(pParent))
			{
				pNew = SE->getTruncateExpr(pNew, pTrunk->getType());
			}
			else if(const SCEVZeroExtendExpr * pExtend = dyn_cast<const SCEVZeroExtendExpr>(pParent))
			{
				pNew = SE->getZeroExtendExpr(pNew, pExtend->getType());
			}
			else if(const SCEVNAryExpr * pNAry = dyn_cast<const SCEVNAryExpr>(pParent))
			{
				SmallVector< const SCEV *, 4> Operands;

				for(size_t i = 0; i < pNAry->getNumOperands(); i ++)
				{
					if(pNAry->getOperand(i) == pCurrent )
					{
						Operands.push_back(pNew);
					}
					else
					{
						Operands.push_back(pNAry->getOperand(i));
					}
				}

				if(const SCEVAddRecExpr * pAddRec = dyn_cast<const SCEVAddRecExpr>(pParent))
				{
					pNew = SE->getAddRecExpr(Operands, pAddRec->getLoop(), pAddRec->getNoWrapFlags());
				}
				else if(const SCEVAddExpr * pAdd = dyn_cast<const SCEVAddExpr>(pParent))
				{
					pNew = SE->getAddExpr(Operands, pAdd->getNoWrapFlags() );
				}
				else if(const SCEVMulExpr * pMul = dyn_cast<const SCEVMulExpr>(pParent))
				{
					pNew = SE->getMulExpr(Operands, pMul->getNoWrapFlags());
				}
				else if(isa<const SCEVSMaxExpr>(pParent))
				{
					pNew = SE->getUMaxExpr(Operands);
				}
				else if(isa<const SCEVUMaxExpr>(pParent))
				{
					pNew = SE->getSMaxExpr(Operands);
				}
			}
			else if(const SCEVUDivExpr * pDiv = dyn_cast<const SCEVUDivExpr>(pParent))
			{
				if(pDiv->getLHS() == pCurrent)
				{
					pNew = SE->getUDivExpr(pNew, pDiv->getRHS());
				}
				else
				{
					pNew = SE->getUDivExpr(pDiv->getLHS(), pNew);
				}
			}
			else
			{
				assert(0);
			}

			pCurrent = pParent;
		}
	}

	return pNew;
}


const SCEV * CalculateLoopTripCounter(Loop * pLoop, ScalarEvolution * SE)
{
	if(BasicBlock * ExitingBB = pLoop->getExitingBlock())
	{
		const SCEV * pTripCounter = SE->getExitCount(pLoop, ExitingBB);

		if(const SCEVUnknown * pUnknown = dyn_cast<const SCEVUnknown>(pTripCounter))
		{
			return pUnknown;
		}

		if(const SCEVNAryExpr * pNAry = dyn_cast<const SCEVNAryExpr>(pTripCounter))
		{
			return DecondeTripCounterSCEV(pNAry, pLoop, SE);	
		}

	}

	return NULL;
}

void CalCulateLoopTripCounter(Loop * pLoop, ScalarEvolution * SE, set<Value *> & setTripCounter)
{
	const SCEV * pTripCounter = SE->getBackedgeTakenCount(pLoop);

	if(const SCEVUnknown * pUnknown = dyn_cast<const SCEVUnknown>(pTripCounter))
	{
		setTripCounter.insert(pUnknown->getValue());
		return;
	}

	//decode
	if(const SCEVNAryExpr * pNAry = dyn_cast<const SCEVNAryExpr>(pTripCounter))
	{
		DecodeTripCounterSCEV(pNAry, pLoop, setTripCounter);
		return;
	}

	set<Instruction *> setExitCond;

	CollectExitCondition(pLoop, setExitCond);

	set<Instruction *>::iterator itExitBegin = setExitCond.begin();
	set<Instruction *>::iterator itExitEnd   = setExitCond.end();

	for(; itExitBegin != itExitEnd; itExitBegin ++ )
	{
		if(CmpInst * pCmp = dyn_cast<CmpInst>(*itExitBegin))
		{
			const SCEV * pOne = SE->getSCEV(pCmp->getOperand(0));
			const SCEV * pTwo = SE->getSCEV(pCmp->getOperand(1));

			if(SE->getLoopDisposition(pOne, pLoop) == ScalarEvolution::LoopComputable)
			{
				if(Instruction * pInst = dyn_cast<Instruction>(pCmp->getOperand(1)))
				{
					if(!pLoop->contains(pInst->getParent()))
					{
						setTripCounter.insert(pInst);
					}
				}
				else if(isa<Argument>(pCmp->getOperand(1)))
				{
					setTripCounter.insert(pCmp->getOperand(1));
				}
			}

			if(SE->getLoopDisposition(pTwo, pLoop) == ScalarEvolution::LoopComputable)
			{
				if(Instruction * pInst = dyn_cast<Instruction>(pCmp->getOperand(0)))
				{
					if(!pLoop->contains(pInst->getParent()))
					{
						setTripCounter.insert(pInst);
					}
				}
				else if(isa<Argument>(pCmp->getOperand(0)))
				{
					setTripCounter.insert(pCmp->getOperand(0));
				}
			}

		}
		else if(isa<CallInst>(*itExitBegin))
		{
			continue;
		}
		else
		{
			assert(0);
		}
	}

}


bool IsIterativeVariable(PHINode * pPHI, Loop * pLoop,  ScalarEvolution * SE)
{
	const SCEV * pSCEV = SE->getSCEV(pPHI);
	if(SE->getLoopDisposition(pSCEV, pLoop) == ScalarEvolution::LoopComputable)
	{
		return true;
	}
	else
	{
		return false;
	}
}

bool IsIterativeVariable(const SCEV * pSCEV, Loop * pLoop,  ScalarEvolution * SE)
{
	if(SE->getLoopDisposition(pSCEV, pLoop) == ScalarEvolution::LoopComputable)
	{
		return true;
	}
	else 
	{
		return false;
	}
}

int64_t CalculateSignedValue(const SCEV * pSCEV, DataLayout * DL)
{
	int64_t res;
	int64_t tmp;
	int64_t left;
	int64_t right;


	if(const SCEVConstant * C = dyn_cast<const SCEVConstant>(pSCEV))
	{
		return C->getValue()->getValue().getSExtValue();
	}
	else if(const SCEVUnknown *U = dyn_cast<const SCEVUnknown>(pSCEV))
	{
		Type * AllocTy;

		if(U->isSizeOf(AllocTy))
		{
			return DL->getTypeSizeInBits(AllocTy)/8;
		}
		else
		{
			return 0;
		}		
	}
	else if (const SCEVAddExpr *Add = dyn_cast<const SCEVAddExpr>(pSCEV))
	{
		res = 0;

		for (unsigned i = 0, e = Add->getNumOperands(); i != e; ++i)
		{
			tmp = CalculateSignedValue(Add->getOperand(i), DL);

			if(tmp == 0)
			{
				return 0;
			}

			res += tmp;
		}

		return res;
	}
	else if(const SCEVMulExpr * Mul = dyn_cast<const SCEVMulExpr>(pSCEV))
	{
		res = 1;

		for (unsigned i = 0, e = Mul->getNumOperands(); i != e; ++i)
		{
			tmp = CalculateSignedValue(Mul->getOperand(i), DL);

			if(tmp == 0)
			{
				return 0;
			}

			res *= tmp;
		}

		return res;
	}
	else if(const SCEVSMaxExpr *SMax = dyn_cast<const SCEVSMaxExpr>(pSCEV))
	{	
		for (unsigned i = 0, e = SMax->getNumOperands(); i != e; ++i)
		{
			tmp = CalculateSignedValue(SMax->getOperand(i), DL);

			if(tmp == 0)
			{
				return 0;
			}

			if(i == 0)
			{
				res = tmp;
			}
			else
			{
				res = max(res, tmp);
			}
		}

		return res;
	}
	else if(const SCEVUMaxExpr *UMax = dyn_cast<const SCEVUMaxExpr>(pSCEV))
	{
		for (unsigned i = 0, e = UMax->getNumOperands(); i != e; ++i)
		{
			tmp = CalculateSignedValue(UMax->getOperand(i), DL);

			if(tmp == 0)
			{
				return 0;
			}

			if(i == 0)
			{
				res = tmp;
			}
			else
			{
				res = max(res, tmp);
			}
		}

		return res;
	}
	else if(const SCEVUDivExpr *UDiv = dyn_cast<const SCEVUDivExpr>(pSCEV))
	{
		left = CalculateSignedValue(UDiv->getLHS(), DL);

		if(left == 0)
		{
			return 0;
		}

		right = CalculateSignedValue(UDiv->getRHS(), DL);
		
		if(right == 0)
		{
			return 0;
		}

		res = left/right;

		return res;
	}
	else if(const SCEVZeroExtendExpr *ZExt = dyn_cast<const SCEVZeroExtendExpr>(pSCEV))
	{
		return CalculateSignedValue(ZExt->getOperand(), DL);
	}
	else if(const SCEVSignExtendExpr *SExt = dyn_cast<const SCEVSignExtendExpr>(pSCEV))
	{
		return CalculateSignedValue(SExt->getOperand(), DL);
	}
	else if(const SCEVTruncateExpr *Trunc = dyn_cast<const SCEVTruncateExpr>(pSCEV))
	{	
		return CalculateSignedValue(Trunc->getOperand(), DL);
	}
	else if(const SCEVAddRecExpr *AddRec = dyn_cast<const SCEVAddRecExpr>(pSCEV))
	{
		res = 0;

		for (unsigned i = 0, e = AddRec->getNumOperands(); i != e; ++i)
		{
			tmp = CalculateSignedValue(AddRec->getOperand(i), DL);
			
			if(tmp == 0)
			{
				return 0;
			}

			res += tmp;
		}

		return res;
	}
	else
	{
		return 0;
	}
}

int64_t CalculateStride(PHINode * pPHI, Loop * pLoop, ScalarEvolution * SE, DataLayout * DL)
{
	const SCEV * pSCEV = SE->getSCEV(pPHI);

	if(!IsIterativeVariable(pSCEV, pLoop, SE))
	{
		return 0;
	}

	if(const SCEVAddRecExpr * pAddRec = dyn_cast<const SCEVAddRecExpr>(pSCEV))
	{
		return CalculateSignedValue(pAddRec->getOperand(1), DL);
	}
	else
	{
		return 0;
	}
}

int64_t CalculateStride(Value * pValue, Loop * pLoop, ScalarEvolution * SE, DataLayout * DL)
{	
	const SCEV * pSCEV = SE->getSCEV(pValue);

	if(!IsIterativeVariable(pSCEV, pLoop, SE))
	{
		errs() << "hereh" << "\n";
		return 0;
	}

	if(const SCEVAddRecExpr * pAddRec = dyn_cast<const SCEVAddRecExpr>(pSCEV))
	{
		return CalculateSignedValue(pAddRec->getOperand(1), DL);
	}
	else
	{
		errs() << "here" << "\n";
		return 0;
	}
}



void SearchContainedValue(const SCEV * pSCEV, set<Value *> & setValue)
{
	vector<const SCEV * > vecWorkList;
	vecWorkList.push_back(pSCEV);

	while(vecWorkList.size()>0)
	{
		const SCEV * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		if(const SCEVCastExpr * pCast = dyn_cast<const SCEVCastExpr>(pCurrent))
		{
			vecWorkList.push_back(pCast->getOperand());
		}
		else if(const SCEVConstant * pConstant = dyn_cast<const SCEVConstant>(pCurrent))
		{
			setValue.insert(pConstant->getValue());
		}
		else if(isa<const SCEVCouldNotCompute>(pCurrent))
		{
			continue;
		}
		else if(const SCEVNAryExpr * pNAry = dyn_cast<const SCEVNAryExpr>(pCurrent))
		{
			for(size_t i = 0; i < pNAry->getNumOperands(); i ++ )
			{
				vecWorkList.push_back(pNAry->getOperand(i));
			}

		}
		else if(const SCEVUDivExpr * pDiv = dyn_cast<const SCEVUDivExpr>(pCurrent))
		{
			vecWorkList.push_back(pDiv->getLHS());
			vecWorkList.push_back(pDiv->getRHS());
		}
		else if(const SCEVUnknown * pUnknown = dyn_cast<const SCEVUnknown>(pCurrent))
		{
			Type * AllocTy;
			Constant * FieldNo;

			if(pUnknown->isSizeOf(AllocTy))
			{
				continue;
			}
			else if(pUnknown->isAlignOf(AllocTy))
			{
				continue;
			}
			else if(pUnknown->isOffsetOf(AllocTy, FieldNo))
			{
				continue;
			}

			setValue.insert(pUnknown->getValue());
		}
	}
}

}

