#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"

#include "llvm/DebugInfo.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"


using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static RegisterPass<StructFieldReach> X(
		"struct-field-reach",
		"reach analysis for struct field",
		false,
		true);


void RefineRangeSet(set<pair<uint64_t, uint64_t> > & oldRangeSet, set<pair<uint64_t, uint64_t> > & newRangeSet, pair<uint64_t, uint64_t> pairRange)
{
	newRangeSet.clear();

	set<pair<uint64_t, uint64_t> >::iterator itRangeBegin = oldRangeSet.begin();
	set<pair<uint64_t, uint64_t> >::iterator itRangeEnd = oldRangeSet.end();

	for(; itRangeBegin != itRangeEnd; itRangeBegin ++ )
	{
		if(itRangeBegin->first >= pairRange.second )
		{
			newRangeSet.insert(*itRangeBegin);
		}
		else if(itRangeBegin->second <= pairRange.first )
		{
			newRangeSet.insert(*itRangeBegin);
		}
		else if(itRangeBegin->first >= pairRange.first )
		{
			if(itRangeBegin->second > pairRange.second )
			{
				pair<uint64_t, uint64_t> pairTmp;
				pairTmp.first = pairRange.second;
				pairTmp.second = itRangeBegin->second;
				newRangeSet.insert(pairTmp);
			}
		}
		else if(itRangeBegin->first < pairRange.first )
		{
			pair<uint64_t, uint64_t> pairTmp;
			pairTmp.first = itRangeBegin->first;
			pairTmp.second = pairRange.first;
			newRangeSet.insert(pairTmp);

			if(itRangeBegin->second > pairRange.second )
			{
				pair<uint64_t, uint64_t> pairTmp;
				pairTmp.first = pairRange.second;
				pairTmp.second = itRangeBegin->second;
				newRangeSet.insert(pairTmp);
			}
		}

	}

}



char StructFieldReach::ID = 0;

void StructFieldReach::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesAll();
	AU.addRequired<DataLayout>();
	AU.addRequired<TargetLibraryInfo>();
	AU.addRequired<AliasAnalysis>();

}

StructFieldReach::StructFieldReach(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeTargetLibraryInfoPass(Registry);
	initializeAliasAnalysisAnalysisGroup(Registry);
}

void StructFieldReach::print(raw_ostream &O, const Module *M) const
{
	return;
}

void StructFieldReach::BuildMemFootPrintMapping(Function * pFunction)
{
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			if(isa<LoadInst>(II) || isa<StoreInst>(II) || isa<MemIntrinsic>(II))
			{
				MemFootPrint foot;
				CalMemFootPrint(II, &foot, this->pDL);
				this->InstMemFootPrintMapping[II] = foot;
			}
		}
	}
}

void StructFieldReach::InitBeforeAfterSet(Function * pF)
{
	for(Function::iterator BB = pF->begin(); BB != pF->end(); BB++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			vector<Instruction *> vecPredInst;
			this->InstPredInstVecMapping[II] = vecPredInst;

			vector<Instruction *> vecSuccInst;
			this->InstSuccInstVecMapping[II] = vecSuccInst;


			set<MemFootPrint *> beforeSet;
			this->InstBeforeSetMapping[II] = beforeSet;

			set<MemFootPrint *> afterSet;
			this->InstAfterSetMapping[II] = afterSet;

			set<MemFootPrint *> beforeExtendSet;
			this->InstBeforeExtendSetMapping[II] = beforeExtendSet;

			set<MemFootPrint *> afterExtendSet;
			this->InstAfterExtendSetMapping[II] = afterExtendSet;

		}
	}

	for(Function::iterator BB = pF->begin(); BB != pF->end(); BB ++)
	{
		BasicBlock::iterator itFirstInst = BB->begin();

		if(itFirstInst == BB->end() )
		{
			continue;
		}

		for(pred_iterator pred = pred_begin(BB); pred != pred_end(BB); pred++ )
		{
			this->InstPredInstVecMapping[itFirstInst].push_back((*pred)->getTerminator());
		}

		BasicBlock::iterator itLastInst = BB->getTerminator();
		for(succ_iterator succ = succ_begin(BB); succ != succ_end(BB); succ++ )
		{
			if((*succ)->begin() == (*succ)->end())
			{
				continue;
			}
			this->InstSuccInstVecMapping[itLastInst].push_back((*succ)->begin());
		}

		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			BasicBlock::iterator ITmp;
			if(II != BB->begin())
			{
				ITmp = II;
				ITmp--;
				this->InstPredInstVecMapping[II].push_back(ITmp);
			}

			ITmp = II;
			ITmp ++;

			if(ITmp != BB->end() )
			{
				this->InstSuccInstVecMapping[II].push_back(ITmp);
			}
		}
	}
}

void StructFieldReach::AssignID()
{
	map<Instruction*, MemFootPrint>::iterator itInstPrintBegin = this->InstMemFootPrintMapping.begin();
	map<Instruction*, MemFootPrint>::iterator itInstPrintEnd = this->InstMemFootPrintMapping.end();

	int iCurrent = 0;

	for(; itInstPrintBegin != itInstPrintEnd; itInstPrintBegin++)
	{
		this->MemFootPrintIDMapping[&(itInstPrintBegin->second)] = iCurrent;
		this->IDMemFootPrintMapping[iCurrent] = &(itInstPrintBegin->second);

		iCurrent ++;
	}
}

void StructFieldReach::DumpMemFootPrint()
{
	map<int, MemFootPrint *>::iterator itIDPrintBegin = this->IDMemFootPrintMapping.begin();
	map<int, MemFootPrint *>::iterator itIDPrintEnd = this->IDMemFootPrintMapping.end();

	for(; itIDPrintBegin != itIDPrintEnd ; itIDPrintBegin ++)
	{
		errs() << itIDPrintBegin->first << "\n";
		PrintMemFootPrint(itIDPrintBegin->second);
	}
}


void StructFieldReach::DumpCachedRelation()
{
	errs() << this->FootPrintPairRelationMapping.size() << "\n";

	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind>::iterator itMapBegin = this->FootPrintPairRelationMapping.begin();
	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind>::iterator itMapEnd = this->FootPrintPairRelationMapping.end();

	int iIdentical = 0;
	int iCover = 0;
	int iCovered = 0;
	int iOverlap = 0;
	int iNo = 0;
	int iUnknown = 0;

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		if(itMapBegin->second == MR_IDENTICAL)
		{	
			iIdentical += 1;
		}
		else if(itMapBegin->second == MR_COVER)
		{
			iCover += 1;
		}
		else if(itMapBegin->second == MR_COVERED)
		{
			iCovered +=1;
		}
		else if(itMapBegin->second == MR_OVERLAP)
		{
			iOverlap += 1;
		}
		else if(itMapBegin->second == MR_NO)
		{
			iNo += 1;
		}
		else
		{
			iUnknown += 1;
		}
	}

	errs() << "MR_IDENTICAL: " << iIdentical << "\n";
	errs() << "MR_COVER: " << iCover << "\n";
	errs() << "MR_COVERED: " << iCovered << "\n";
	errs() << "MR_OVERLAP: " << iOverlap << "\n";
	errs() << "MR_NO: " << iNo << "\n";
	errs() << "MR_UNKNOWN: " << iUnknown << "\n";

/*	
	itMapBegin = this->FootPrintPairRelationMapping.begin();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		if(itMapBegin->second != MR_OVERLAP )
		{
			continue;
		}

		errs() << this->MemFootPrintIDMapping[itMapBegin->first.first] << "\n";
		PrintMemFootPrint(itMapBegin->first.first);

		errs() << this->MemFootPrintIDMapping[itMapBegin->first.second] << "\n";
		PrintMemFootPrint(itMapBegin->first.second);

		errs() << "**************************************************************************************\n";
	}
*/	
}

void StructFieldReach::DumpCachedInterRelation()
{
	errs() << "\nExtended Set:\n";
	errs() << this->InterFootPrintPairRelationMapping.size() << "\n";
	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind>::iterator itMapBegin = this->InterFootPrintPairRelationMapping.begin();
	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind>::iterator itMapEnd = this->InterFootPrintPairRelationMapping.end();

	int iIdentical = 0;
	int iCover = 0;
	int iCovered = 0;
	int iOverlap = 0;
	int iNo = 0;
	int iUnknown = 0;

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		if(itMapBegin->second == MR_IDENTICAL)
		{	
			iIdentical += 1;
		}
		else if(itMapBegin->second == MR_COVER)
		{
			iCover += 1;
		}
		else if(itMapBegin->second == MR_COVERED)
		{
			iCovered +=1;
		}
		else if(itMapBegin->second == MR_OVERLAP)
		{
			iOverlap += 1;
		}
		else if(itMapBegin->second == MR_NO)
		{
			iNo += 1;
		}
		else
		{
			iUnknown += 1;
		}
	}

	errs() << "MR_IDENTICAL: " << iIdentical << "\n";
	errs() << "MR_COVER: " << iCover << "\n";
	errs() << "MR_COVERED: " << iCovered << "\n";
	errs() << "MR_OVERLAP: " << iOverlap << "\n";
	errs() << "MR_NO: " << iNo << "\n";
	errs() << "MR_UNKNOWN: " << iUnknown << "\n";

/*
	itMapBegin = this->InterFootPrintPairRelationMapping.begin();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		if(itMapBegin->second != MR_IDENTICAL )
		{
			continue;
		}

		errs() << this->MemFootPrintIDMapping[itMapBegin->first.first] << "\n";
		PrintMemFootPrint(itMapBegin->first.first);

		errs() << this->MemFootPrintIDMapping[itMapBegin->first.second] << "\n";
		PrintMemFootPrint(itMapBegin->first.second);

		errs() << "**************************************************************************************\n";
	}
*/
}

MemRelationKind StructFieldReach::CalIntraMemWriteRelation(MemFootPrint* pPrint1, MemFootPrint * pPrint2)
{
	if(pPrint1 == pPrint2)
	{
		return MR_IDENTICAL;
	}

	if(pPrint1->pI == pPrint2->pI)
	{
		return MR_IDENTICAL;
	}

	Function * pCurrentFunction = NULL;

	if(pPrint1->pI->getParent()->getParent() == pPrint2->pI->getParent()->getParent() )
	{
		pCurrentFunction = pPrint1->pI->getParent()->getParent();
	}

	if(pCurrentFunction == NULL)
	{
		return MR_UNKNOWN;
	}

// check cache
	pair<MemFootPrint *, MemFootPrint *> PrintPair;
	if(pPrint1 > pPrint2)
	{
		PrintPair.second = pPrint1;
		PrintPair.first = pPrint2;
	}
	else
	{
		PrintPair.first = pPrint1;
		PrintPair.second = pPrint2;
	}

	if(this->FootPrintPairRelationMapping.find(PrintPair) != this->FootPrintPairRelationMapping.end() )
	{
		if(PrintPair.first == pPrint2 )
		{
			if(this->FootPrintPairRelationMapping[PrintPair] == MR_COVER )
			{
				return MR_COVERED;
			}
			else if(this->FootPrintPairRelationMapping[PrintPair] == MR_COVERED)
			{
				return MR_COVER;
			}
		}

		return this->FootPrintPairRelationMapping[PrintPair];
	}

	MemRelationKind kindResult = MR_UNKNOWN;

	if(BeDifferentBaseObject(pPrint1, pPrint2, this->pDL))
	{
		kindResult = MR_NO;
	}

	bool bSameObjectCheck = false;
	if(kindResult == MR_UNKNOWN && BeSameBaseObject(pPrint1, pPrint2))
	{
		kindResult = CmpMemFootPrintForSameBase(pPrint1, pPrint2);
		bSameObjectCheck = true;
	}

	if(kindResult == MR_UNKNOWN)
	{
		AliasAnalysis::AliasResult aliasResult = this->pAA->alias(pPrint1->pBaseObject, 1, pPrint2->pBaseObject, 1);
		if(aliasResult == AliasAnalysis::NoAlias)
		{
			kindResult = MR_NO;
		}
		else if(aliasResult == AliasAnalysis::MustAlias && !bSameObjectCheck)
		{
			kindResult = CmpMemFootPrintForSameBase(pPrint1, pPrint2);
			bSameObjectCheck = true;
		}
	}

	if(kindResult == MR_UNKNOWN)
	{
		AliasAnalysis::AliasResult aliasResult = this->pAA->alias(pPrint1->pPointer, pPrint1->uLength, pPrint2->pPointer, pPrint2->uLength);

		if(aliasResult == AliasAnalysis::MustAlias)
		{
			if(pPrint1->uLength == UnknownSize || pPrint2->uLength == UnknownSize)
			{
				kindResult = MR_OVERLAP;
			}
			else
			{
				if(pPrint1->uLength == pPrint2->uLength)
				{
					kindResult = MR_IDENTICAL;
				}
				else if(pPrint1->uLength < pPrint2->uLength)
				{
					kindResult = MR_COVERED;
				}
				else
				{
					kindResult = MR_COVER;
				}
			}

		}
		else if(aliasResult == AliasAnalysis::NoAlias)
		{
			kindResult = MR_NO;
		
		}
		else if(aliasResult == AliasAnalysis::PartialAlias)
		{
			kindResult = MR_OVERLAP;
		}
		else
		{
			kindResult = MR_UNKNOWN;
		}

	}

	if(kindResult == MR_UNKNOWN && bSameObjectCheck)
	{
		if(pPrint1->uOffset == pPrint2->uOffset)
		{
			if(pPrint1->uMaxLength != UnknownSize && pPrint2->uMaxLength != UnknownSize)
			{
				kindResult = MR_OVERLAP;
			}
		}
	}

//update cache
	if(PrintPair.first == pPrint2 )
	{
		if(kindResult == MR_COVER)
		{
			this->FootPrintPairRelationMapping[PrintPair] = MR_COVERED;
		}
		else if(kindResult == MR_COVERED)
		{
			this->FootPrintPairRelationMapping[PrintPair] = MR_COVER;
		}
		else
		{
			this->FootPrintPairRelationMapping[PrintPair] = kindResult;
		}
	}
	else
	{
		this->FootPrintPairRelationMapping[PrintPair] = kindResult;
	}

	return kindResult;
}


MemRelationKind StructFieldReach::CalInterMemWriteRelation(MemFootPrint* pPrint1, MemFootPrint * pPrint2)
{
	if(pPrint1 == pPrint2)
	{
		return MR_IDENTICAL;
	}

	if(pPrint1->bReturn == false && pPrint2->bReturn == false)
	{
		errs() << "both not return\n";
		exit(0);
	}

	if(pPrint1->bReturn && pPrint2->bReturn)
	{
		errs() << "both return \n";
		exit(0);
	}

//check cache
	pair<MemFootPrint *, MemFootPrint *> PrintPair;
	if(pPrint1 > pPrint2)
	{
		PrintPair.second = pPrint1;
		PrintPair.first = pPrint2;
	}
	else
	{
		PrintPair.first = pPrint1;
		PrintPair.second = pPrint2;
	}

	if(this->InterFootPrintPairRelationMapping.find(PrintPair) != this->InterFootPrintPairRelationMapping.end() )
	{
		if(PrintPair.first == pPrint2 )
		{
			if(this->InterFootPrintPairRelationMapping[PrintPair] == MR_COVER )
			{
				return MR_COVERED;
			}
			else if(this->InterFootPrintPairRelationMapping[PrintPair] == MR_COVERED)
			{
				return MR_COVER;
			}
		}

		return this->InterFootPrintPairRelationMapping[PrintPair];
	}

	MemRelationKind kindResult = MR_UNKNOWN;

	if(BeDifferentBaseObject(pPrint1, pPrint2, this->pDL))
	{
		kindResult = MR_NO;
	}

	bool bSameObjectCheck = false;
	if(kindResult == MR_UNKNOWN && BeSameBaseObject(pPrint1, pPrint2))
	{
		kindResult = CmpInterMemFootPrintForSameBase(pPrint1, pPrint2);
		bSameObjectCheck = true;
	}

	if(kindResult == MR_UNKNOWN)
	{
		AliasAnalysis::AliasResult aliasResult = this->pAA->alias(pPrint1->pBaseObject, 1, pPrint2->pBaseObject, 1);
		if(aliasResult == AliasAnalysis::NoAlias)
		{
			kindResult = MR_NO;
		}
		else if(aliasResult == AliasAnalysis::MustAlias && !bSameObjectCheck)
		{
			kindResult = CmpInterMemFootPrintForSameBase(pPrint1, pPrint2);
			bSameObjectCheck = true;
		}
	}

//update cache
	if(PrintPair.first == pPrint2 )
	{
		if(kindResult == MR_COVER)
		{
			this->InterFootPrintPairRelationMapping[PrintPair] = MR_COVERED;
		}
		else if(kindResult == MR_COVERED)
		{
			this->InterFootPrintPairRelationMapping[PrintPair] = MR_COVER;
		}
		else
		{
			this->InterFootPrintPairRelationMapping[PrintPair] = kindResult;
		}
	}
	else
	{
		this->InterFootPrintPairRelationMapping[PrintPair] = kindResult;
	}

	return kindResult;
}

void StructFieldReach::RefineIntraMemFootPrintSet(set<MemFootPrint *> & setMemFootPrint, MemFootPrint * pFoot)
{
	if(pFoot->GEPVariableIndices.size() > 0)
	{
		return;
	}

	if(pFoot->uLength == UnknownSize || pFoot->uOffset == UnknownSize)
	{
		return;
	}

	set<MemFootPrint *>::iterator itSetBegin = setMemFootPrint.begin();
	set<MemFootPrint *>::iterator itSetEnd = setMemFootPrint.end();

	BasicBlock * pBlock = pFoot->pI->getParent();
	set<MemFootPrint *> setCandidate;

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		if((*itSetBegin)->GEPVariableIndices.size() > 0)
		{
			continue;
		}

		if((*itSetBegin)->uLength == UnknownSize || (*itSetBegin)->uOffset == UnknownSize)
		{
			continue;
		}

		if((*itSetBegin)->pI->getParent() != pBlock)
		{
			continue;
		}

		setCandidate.insert(*itSetBegin);
	}

	if(setCandidate.size() == 0)
	{
		return;
	}

	itSetBegin = setMemFootPrint.begin();
	itSetEnd = setMemFootPrint.end();

	set<MemFootPrint *> setToBeRemoved;
	
	for(; itSetBegin != itSetEnd; itSetBegin++ )
	{
		if((*itSetBegin)->GEPVariableIndices.size() > 0)
		{
			continue;
		}

		if((*itSetBegin)->uLength == UnknownSize || (*itSetBegin)->uOffset == UnknownSize )
		{
			continue;
		}

		if(CalIntraMemWriteRelation(pFoot, *itSetBegin) != MR_COVERED )
		{
			continue;
		}

		set<pair<uint64_t, uint64_t> > setOldRanges;
		set<pair<uint64_t, uint64_t> > setNewRanges;

		pair<uint64_t, uint64_t> pairRoot;
		pairRoot.first = (*itSetBegin)->uOffset;
		pairRoot.second = (*itSetBegin)->uOffset + (*itSetBegin)->uLength;
		setOldRanges.insert(pairRoot);

		pair<uint64_t, uint64_t> pairTmp;
		pairTmp.first = pFoot->uOffset;
		pairTmp.second = pFoot->uOffset + pFoot->uLength;

		RefineRangeSet(setOldRanges, setNewRanges, pairTmp);

		setOldRanges = setNewRanges;

		set<MemFootPrint *>::iterator itSetCandidateBegin = setCandidate.begin();
		set<MemFootPrint *>::iterator itSetCandidateEnd = setCandidate.end();

		for(; itSetCandidateBegin !=itSetCandidateEnd; itSetCandidateBegin ++)
		{
			if( *itSetBegin == *itSetCandidateBegin)
			{
				continue;
			}

			if(CalIntraMemWriteRelation(*itSetCandidateBegin, *itSetBegin) != MR_COVERED )
			{
				continue;
			}

			pairTmp.first = (*itSetCandidateBegin)->uOffset;
			pairTmp.second = (*itSetCandidateBegin)->uOffset + (*itSetCandidateBegin)->uLength;

			RefineRangeSet(setOldRanges, setNewRanges, pairTmp);

			setOldRanges = setNewRanges;
		}

		if(setOldRanges.size() == 0)
		{
			setToBeRemoved.insert(*itSetBegin);
		}
	}

	itSetBegin = setToBeRemoved.begin();
	itSetEnd = setToBeRemoved.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		setMemFootPrint.erase(*itSetBegin);

		//errs() << "here" << "\n";
		//exit(0);
	}
}


void StructFieldReach::RefineInterMemFootPrintSet(set<MemFootPrint *> & setMemFootPrint, set<MemFootPrint *> & beforeSet, MemFootPrint * pFoot)
{
	if(pFoot->GEPVariableIndices.size() > 0)
	{
		return;
	}

	if(pFoot->uLength == UnknownSize || pFoot->uOffset == UnknownSize)
	{
		return;
	}

	set<MemFootPrint *>::iterator itSetBegin = beforeSet.begin();
	set<MemFootPrint *>::iterator itSetEnd = beforeSet.end();

	BasicBlock * pBlock = pFoot->pI->getParent();
	set<MemFootPrint *> setCandidate;

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		if((*itSetBegin)->GEPVariableIndices.size() > 0)
		{
			continue;
		}

		if((*itSetBegin)->uLength == UnknownSize || (*itSetBegin)->uOffset == UnknownSize)
		{
			continue;
		}

		if((*itSetBegin)->pI->getParent() != pBlock)
		{
			continue;
		}

		BasicBlock::iterator pII = (*itSetBegin)->pI;

		for(; pII != (*itSetBegin)->pI->getParent()->end(); pII ++)
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(pII))
			{
				if(pInstruction == pFoot->pI)
				{
					setCandidate.insert(*itSetBegin);
					break;
				}
			}
			else if(isa<CallInst>(pII) || isa<InvokeInst>(pII))
			{
				break;
			}
		}
	}

	if(setCandidate.size() == 0)
	{
		return;
	}

	itSetBegin = setMemFootPrint.begin();
	itSetEnd = setMemFootPrint.end();

	set<MemFootPrint *> setToBeRemoved;

	for(; itSetBegin != itSetEnd; itSetBegin++ )
	{
		if((*itSetBegin)->GEPVariableIndices.size() > 0)
		{
			continue;
		}

		if((*itSetBegin)->uLength == UnknownSize || (*itSetBegin)->uOffset == UnknownSize )
		{
			continue;
		}

		if(CalInterMemWriteRelation(pFoot, *itSetBegin) != MR_COVERED )
		{
			continue;
		}

		set<pair<uint64_t, uint64_t> > setOldRanges;
		set<pair<uint64_t, uint64_t> > setNewRanges;

		pair<uint64_t, uint64_t> pairRoot;
		pairRoot.first = (*itSetBegin)->uOffset;
		pairRoot.second = (*itSetBegin)->uOffset + (*itSetBegin)->uLength;
		setOldRanges.insert(pairRoot);

		pair<uint64_t, uint64_t> pairTmp;
		pairTmp.first = pFoot->uOffset;
		pairTmp.second = pFoot->uOffset + pFoot->uLength;

		RefineRangeSet(setOldRanges, setNewRanges, pairTmp);

		setOldRanges = setNewRanges;

		set<MemFootPrint *>::iterator itSetCandidateBegin = setCandidate.begin();
		set<MemFootPrint *>::iterator itSetCandidateEnd = setCandidate.end();

		for(; itSetCandidateBegin !=itSetCandidateEnd; itSetCandidateBegin ++)
		{
			if( *itSetBegin == *itSetCandidateBegin)
			{
				continue;
			}

			if(CalInterMemWriteRelation(*itSetCandidateBegin, *itSetBegin) != MR_COVERED )
			{
				continue;
			}

			pairTmp.first = (*itSetCandidateBegin)->uOffset;
			pairTmp.second = (*itSetCandidateBegin)->uOffset + (*itSetCandidateBegin)->uLength;

			RefineRangeSet(setOldRanges, setNewRanges, pairTmp);

			setOldRanges = setNewRanges;
		}

		if(setOldRanges.size() == 0)
		{
			setToBeRemoved.insert(*itSetBegin);
		}

	}

	itSetBegin = setToBeRemoved.begin();
	itSetEnd = setToBeRemoved.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		setMemFootPrint.erase(*itSetBegin);
		

	}
}


void StructFieldReach::CalIntraAfterSet( set<MemFootPrint *> & beforeSet, set<MemFootPrint *> & afterSet, Instruction * pCurrent )
{
	afterSet.clear();

	set<MemFootPrint *>::iterator itSetFootBegin = beforeSet.begin();
	set<MemFootPrint *>::iterator itSetFootEnd = beforeSet.end();

	if(isa<StoreInst>(pCurrent) || isa<MemIntrinsic>(pCurrent))
	{

		bool bFlag = false;
		for(; itSetFootBegin != itSetFootEnd; itSetFootBegin ++)
		{
			MemRelationKind resultKind = CalIntraMemWriteRelation(&(this->InstMemFootPrintMapping[pCurrent]), *itSetFootBegin);

			if(!(resultKind == MR_IDENTICAL || resultKind == MR_COVER))
			{
				afterSet.insert(*itSetFootBegin);
			}

			if(resultKind == MR_COVERED)
			{
				bFlag = true;
			}
		}

		if(bFlag)
		{
			RefineIntraMemFootPrintSet(afterSet, &(this->InstMemFootPrintMapping[pCurrent]));
		}

		afterSet.insert( &(this->InstMemFootPrintMapping[pCurrent]));

		//add a simple prune here
	}
	else
	{	
		for(; itSetFootBegin != itSetFootEnd; itSetFootBegin ++)
		{
			afterSet.insert(*itSetFootBegin);
		}
	}
}

void StructFieldReach::IntraFieldReachAnalysis(Function * pF)
{
	map<Instruction *, set< MemFootPrint *> >::iterator itMapInstBegin = this->InstBeforeSetMapping.begin();
	map<Instruction *, set< MemFootPrint *> >::iterator itMapInstEnd = this->InstBeforeSetMapping.end();

	vector<Instruction *> vecWorkList;

	for(; itMapInstBegin != itMapInstEnd; itMapInstBegin++ )
	{
		vecWorkList.push_back(itMapInstBegin->first);
	}

	while(vecWorkList.size()>0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		vector<Instruction *>::iterator itPredInstVecBegin = this->InstPredInstVecMapping[pCurrent].begin();
		vector<Instruction *>::iterator itPredInstVecEnd = this->InstPredInstVecMapping[pCurrent].end();

		this->InstBeforeSetMapping[pCurrent].clear();

		for(; itPredInstVecBegin != itPredInstVecEnd; itPredInstVecBegin ++ )
		{
			set<MemFootPrint *>::iterator itAfterSetBegin = this->InstAfterSetMapping[*itPredInstVecBegin].begin();
			set<MemFootPrint *>::iterator itAfterSetEnd = this->InstAfterSetMapping[*itPredInstVecBegin].end();

			for(; itAfterSetBegin != itAfterSetEnd; itAfterSetBegin ++ )
			{
				this->InstBeforeSetMapping[pCurrent].insert(*itAfterSetBegin);
			}
		}

		set<MemFootPrint *> afterSet;

		CalIntraAfterSet(this->InstBeforeSetMapping[pCurrent], afterSet, pCurrent);

		if(CmpMemFootPrintSet(this->InstAfterSetMapping[pCurrent], afterSet))
		{
			continue;
		}

		this->InstAfterSetMapping[pCurrent] = afterSet;

		vector<Instruction *>::iterator itSuccInstVecBegin = this->InstSuccInstVecMapping[pCurrent].begin();
		vector<Instruction *>::iterator itSuccInstVecEnd = this->InstSuccInstVecMapping[pCurrent].end();

		for(; itSuccInstVecBegin != itSuccInstVecEnd; itSuccInstVecBegin ++ )
		{
			vecWorkList.push_back(*itSuccInstVecBegin);
		}
	}
}

void StructFieldReach::CollectLiveInput(Function * pFunction, vector< pair<MemFootPrint *, int> > & vecLiveInput )
{
	ReturnInst * pRet = NULL;
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			if(ReturnInst * pR = dyn_cast<ReturnInst>(II))
			{
				pRet = pR;
			}
		}
	}

	vector<Argument *> vecArgument;

	for(Function::arg_iterator argBe = pFunction->arg_begin(); argBe != pFunction->arg_end(); argBe ++ )
	{
		vecArgument.push_back(argBe);
		
	}


	set<MemFootPrint *>::iterator itSetBegin = this->InstBeforeSetMapping[pRet].begin();
	set<MemFootPrint *>::iterator itSetEnd = this->InstBeforeSetMapping[pRet].end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{


		vector<Argument *>::iterator itVecArgBegin = vecArgument.begin();
		vector<Argument *>::iterator itVecArgEnd = vecArgument.end();

		int iIndex = 0;

		for(; itVecArgBegin != itVecArgEnd; itVecArgBegin++)
		{
			if(*itVecArgBegin == (*itSetBegin)->pBaseObject)
			{
				pair<MemFootPrint *, int> pairTmp;
				pairTmp.first = *itSetBegin;
				pairTmp.second = iIndex;
				vecLiveInput.push_back(pairTmp);
			}

			iIndex ++;
		}
	}

}



void StructFieldReach::CalAfterExtendSet( set<MemFootPrint *> & beforeSet, set<MemFootPrint *> & afterSet, Instruction * pCurrent, Function * pFunction, vector<pair<MemFootPrint *, int> > & vecLiveInput )
{
	afterSet.clear();

	set<MemFootPrint *>::iterator itSetFootBegin = beforeSet.begin();
	set<MemFootPrint *>::iterator itSetFootEnd = beforeSet.end();

	if(isa<StoreInst>(pCurrent) || isa<MemIntrinsic>(pCurrent))
	{
		bool bFlag = false;
		for(; itSetFootBegin != itSetFootEnd; itSetFootBegin ++)
		{
			MemRelationKind resultKind = CalInterMemWriteRelation(&(this->InstMemFootPrintMapping[pCurrent]), *itSetFootBegin);

			if(!(resultKind == MR_IDENTICAL || resultKind == MR_COVER))
			{
				afterSet.insert(*itSetFootBegin);
			}

			if(resultKind == MR_COVERED)
			{
				bFlag = true;
			}
		}

		if(bFlag)
		{
			RefineInterMemFootPrintSet(afterSet, this->InstBeforeSetMapping[pCurrent], &(this->InstMemFootPrintMapping[pCurrent]));
		}
	}
	else if(CallInst * pCall = dyn_cast<CallInst>(pCurrent))
	{
		for(; itSetFootBegin != itSetFootEnd; itSetFootBegin ++)
		{
			afterSet.insert(*itSetFootBegin);
		}

		Function * pCalledFunction = pCall->getCalledFunction();

		if(pCalledFunction == pFunction)
		{
			if(this->CallInstMemFootPrintMapping.find(pCall) == this->CallInstMemFootPrintMapping.end() )
			{
				vector<MemFootPrint> vecTmp;

				this->CallInstMemFootPrintMapping[pCall] = vecTmp;
				vector<pair<MemFootPrint *, int > >::iterator itVecPairBegin = vecLiveInput.begin();
				vector<pair<MemFootPrint *, int > >::iterator itVecPairEnd = vecLiveInput.end();

				for(; itVecPairBegin != itVecPairEnd; itVecPairBegin++ )
				{
					//it is possible that we need to do address translation later
					MemFootPrint tmpPrint;
					CopyMemFootPrint(itVecPairBegin->first, &tmpPrint);
					ChangeBaseObject(&tmpPrint, pCall->getOperand(itVecPairBegin->second), this->pDL);
					tmpPrint.bReturn = true;
					this->CallInstMemFootPrintMapping[pCall].push_back(tmpPrint);
				}
			}

			vector<MemFootPrint>::iterator itVecPrintBegin = this->CallInstMemFootPrintMapping[pCall].begin();
			vector<MemFootPrint>::iterator itVecPrintEnd = this->CallInstMemFootPrintMapping[pCall].end();

			for(; itVecPrintBegin != itVecPrintEnd; itVecPrintBegin++ )
			{
				afterSet.insert(&(*itVecPrintBegin));
			}
		}
	}
	else
	{
		for(; itSetFootBegin != itSetFootEnd; itSetFootBegin ++)
		{
			afterSet.insert(*itSetFootBegin);
		}
	}
}



void StructFieldReach::InterFieldReachAnalysis(Function * pFunction, vector<pair<MemFootPrint *, int> > & vecLiveInput)
{
	map<Instruction *, set< MemFootPrint *> >::iterator itMapInstBegin = this->InstBeforeExtendSetMapping.begin();
	map<Instruction *, set< MemFootPrint *> >::iterator itMapInstEnd = this->InstBeforeExtendSetMapping.end();

	vector<Instruction *> vecWorkList;

	for(; itMapInstBegin != itMapInstEnd; itMapInstBegin++ )
	{
		vecWorkList.push_back(itMapInstBegin->first);
	}

	while(vecWorkList.size()>0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		vector<Instruction *>::iterator itPredInstVecBegin = this->InstPredInstVecMapping[pCurrent].begin();
		vector<Instruction *>::iterator itPredInstVecEnd = this->InstPredInstVecMapping[pCurrent].end();

		this->InstBeforeExtendSetMapping[pCurrent].clear();

		for(; itPredInstVecBegin != itPredInstVecEnd; itPredInstVecBegin ++ )
		{
			set<MemFootPrint *>::iterator itAfterSetBegin = this->InstAfterExtendSetMapping[*itPredInstVecBegin].begin();
			set<MemFootPrint *>::iterator itAfterSetEnd = this->InstAfterExtendSetMapping[*itPredInstVecBegin].end();

			for(; itAfterSetBegin != itAfterSetEnd; itAfterSetBegin ++ )
			{
				this->InstBeforeExtendSetMapping[pCurrent].insert(*itAfterSetBegin);
			}
		}

		set<MemFootPrint *> afterSet;

		CalAfterExtendSet(this->InstBeforeExtendSetMapping[pCurrent], afterSet, pCurrent, pFunction, vecLiveInput );
		
		if(CmpMemFootPrintSet(this->InstAfterExtendSetMapping[pCurrent], afterSet))
		{
			continue;
		}


		this->InstAfterExtendSetMapping[pCurrent] = afterSet;

		vector<Instruction *>::iterator itSuccInstVecBegin = this->InstSuccInstVecMapping[pCurrent].begin();
		vector<Instruction *>::iterator itSuccInstVecEnd = this->InstSuccInstVecMapping[pCurrent].end();

		for(; itSuccInstVecBegin != itSuccInstVecEnd; itSuccInstVecBegin ++ )
		{
			vecWorkList.push_back(*itSuccInstVecBegin);
		}
	}
}

void StructFieldReach::CalLoadDependentStore(Function * pFunction)
{
	int iLoad = 0;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
			{
				iLoad ++;
				set<Instruction *> setDependentInst;

				set< MemFootPrint *>::iterator itFootSetBegin = this->InstBeforeSetMapping[pLoad].begin();
				set< MemFootPrint *>::iterator itFootSetEnd = this->InstBeforeSetMapping[pLoad].end();

				for(; itFootSetBegin != itFootSetEnd; itFootSetBegin ++)
				{
					MemRelationKind resultKind = CalIntraMemWriteRelation(&(this->InstMemFootPrintMapping[pLoad]), *itFootSetBegin);

					if(resultKind == MR_IDENTICAL || resultKind == MR_COVER || resultKind == MR_COVERED || resultKind == MR_OVERLAP)
					{
						setDependentInst.insert((*itFootSetBegin)->pI);
					}
				}

				itFootSetBegin = this->InstBeforeExtendSetMapping[pLoad].begin();
				itFootSetEnd = this->InstBeforeExtendSetMapping[pLoad].end();

				for(; itFootSetBegin != itFootSetEnd; itFootSetBegin++ )
				{
					MemRelationKind resultKind = CalInterMemWriteRelation(&(this->InstMemFootPrintMapping[pLoad]), *itFootSetBegin);

					if(resultKind == MR_IDENTICAL || resultKind == MR_COVER || resultKind == MR_COVERED || resultKind == MR_OVERLAP)
					{
						setDependentInst.insert((*itFootSetBegin)->pI);
					}
				}

				this->LoadDependentInstMapping[pLoad] = setDependentInst;

			}
		}
	}
}


void StructFieldReach::DebugResult(Function * pFunction)
{

/*
	Instruction * pII = NULL;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			if(!isa<LoadInst>(II))
			{
				continue;
			}

			if( MDNode *N = II->getMetadata("dbg") )
			{
				                     
				unsigned int uLineNoForInstruction = Loc.getLineNumber();
				if(uLineNoForInstruction == 2765)
				{
					pII = II;
				}
			}
		}
	}

*/

}

void StructFieldReach::DumpLoadDependingStore()
{
	map<LoadInst *, set<Instruction *> >::iterator itMapBegin = this->LoadDependentInstMapping.begin();
	map<LoadInst *, set<Instruction *> >::iterator itMapEnd = this->LoadDependentInstMapping.end();

	char pPath[1000];

	for(; itMapBegin != itMapEnd; itMapBegin++)
	{
		if(itMapBegin->second.size() == 0)
		{
			continue;
		}

		itMapBegin->first->dump();
		if( MDNode *N = itMapBegin->first->getMetadata("dbg") )
		{
			DILocation Loc(N);
			string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
			realpath( sFileNameForInstruction.c_str() , pPath);
			sFileNameForInstruction = string(pPath);                        
			unsigned int uLineNoForInstruction = Loc.getLineNumber();
			errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
		}

		set<Instruction *>::iterator itSetBegin = itMapBegin->second.begin();
		set<Instruction *>::iterator itSetEnd = itMapBegin->second.end();

		for(; itSetBegin != itSetEnd; itSetBegin++)
		{
			(*itSetBegin)->dump();
			if( MDNode *N = (*itSetBegin)->getMetadata("dbg") )
			{
				DILocation Loc(N);
				string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
				realpath( sFileNameForInstruction.c_str() , pPath);
				sFileNameForInstruction = string(pPath);                        
				unsigned int uLineNoForInstruction = Loc.getLineNumber();
				errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
			}

		}

		errs() << "****************************************************************\n";
	}
}

void StructFieldReach::CalMemIntrinsicDependence(Function * pFunction )
{

	int iMem = 0;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
			{
				//bool bFlag = false;
				iMem++;
				MemFootPrint pFoot;
				CalMemFootPrintForMemInstSrc(pMem, &pFoot, this->pDL);
				this->MemInstMemFootPrintMapping[pMem] = pFoot;

/*
				if( MDNode *N = pMem->getMetadata("dbg") )
				{
					DILocation Loc(N);
					if( Loc.getLineNumber() == 2839 )
					{
						PrintMemFootPrint(&pFoot);
						bFlag = true;
					}
				}
*/
				set<Instruction *> setDependentInst;

				set< MemFootPrint *>::iterator itFootSetBegin = this->InstBeforeSetMapping[pMem].begin();
				set< MemFootPrint *>::iterator itFootSetEnd = this->InstBeforeSetMapping[pMem].end();

				for(; itFootSetBegin != itFootSetEnd; itFootSetBegin ++)
				{
					MemRelationKind resultKind = CalIntraMemWriteRelation(&(this->MemInstMemFootPrintMapping[pMem]), *itFootSetBegin);

					if(resultKind == MR_IDENTICAL || resultKind == MR_COVER || resultKind == MR_COVERED || resultKind == MR_OVERLAP)
					{
						setDependentInst.insert((*itFootSetBegin)->pI);
					}

/*
					if(bFlag)
					{
						//errs() << resultKind << "\n";
						if(MDNode *N = (*itFootSetBegin)->pI->getMetadata("dbg"))
						{
							DILocation Loc(N);
							if( Loc.getLineNumber() == 2740 )
							{
								errs() << resultKind << "\n";
								PrintMemFootPrint(*itFootSetBegin);
								exit(0);
							}
						}
					}
*/
				}

				

				itFootSetBegin = this->InstBeforeExtendSetMapping[pMem].begin();
				itFootSetEnd = this->InstBeforeExtendSetMapping[pMem].end();

				for(; itFootSetBegin != itFootSetEnd; itFootSetBegin++ )
				{
					MemRelationKind resultKind = CalInterMemWriteRelation(&(this->MemInstMemFootPrintMapping[pMem]), *itFootSetBegin);

					if(resultKind == MR_IDENTICAL || resultKind == MR_COVER || resultKind == MR_COVERED || resultKind == MR_OVERLAP)
					{
						setDependentInst.insert((*itFootSetBegin)->pI);
					}
				}

				this->MemInstDependentInstMapping[pMem] = setDependentInst;				
			}
		}
	}
}

void StructFieldReach::DumpMemInstDependingStore()
{
	map<MemTransferInst *, set<Instruction *> >::iterator itMapBegin = this->MemInstDependentInstMapping.begin();
	map<MemTransferInst *, set<Instruction *> >::iterator itMapEnd = this->MemInstDependentInstMapping.end();

	char pPath[1000];

	for(; itMapBegin != itMapEnd; itMapBegin++)
	{
		itMapBegin->first->dump();
		if( MDNode *N = itMapBegin->first->getMetadata("dbg") )
		{
			DILocation Loc(N);
			string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
			realpath( sFileNameForInstruction.c_str() , pPath);
			sFileNameForInstruction = string(pPath);                        
			unsigned int uLineNoForInstruction = Loc.getLineNumber();
			errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
		}

		set<Instruction *>::iterator itSetBegin = itMapBegin->second.begin();
		set<Instruction *>::iterator itSetEnd = itMapBegin->second.end();

		for(; itSetBegin != itSetEnd; itSetBegin++)
		{
			(*itSetBegin)->dump();
			if( MDNode *N = (*itSetBegin)->getMetadata("dbg") )
			{
				DILocation Loc(N);
				string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
				realpath( sFileNameForInstruction.c_str() , pPath);
				sFileNameForInstruction = string(pPath);                        
				unsigned int uLineNoForInstruction = Loc.getLineNumber();
				errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
			}

		}

		errs() << "****************************************************************\n";
	}
}

void StructFieldReach::ClearCache()
{
	this->InstPredInstVecMapping.clear();
	this->InstSuccInstVecMapping.clear();

	this->InstBeforeSetMapping.clear();
	this->InstAfterSetMapping.clear();

	this->InstBeforeExtendSetMapping.clear();
	this->InstAfterExtendSetMapping.clear();

	this->InstMemFootPrintMapping.clear();
	this->CallInstMemFootPrintMapping.clear();
	this->MemInstMemFootPrintMapping.clear();

	this->MemFootPrintIDMapping.clear();
	this->IDMemFootPrintMapping.clear();

	this->FootPrintPairRelationMapping.clear();
	this->InterFootPrintPairRelationMapping.clear();
}


void StructFieldReach::TestDriver(Module & M)
{
	Function * pFunction = M.getFunction("synth_mult");
	BuildMemFootPrintMapping(pFunction);
	InitBeforeAfterSet(pFunction);
	IntraFieldReachAnalysis(pFunction);
	//DumpCachedRelation();
	vector< pair<MemFootPrint *, int> >  vecLiveInput;
	CollectLiveInput(pFunction, vecLiveInput );
	InterFieldReachAnalysis(pFunction, vecLiveInput);
	//DumpCachedInterRelation();
	CalLoadDependentStore(pFunction);
	//DumpLoadDependingStore();
	CalMemIntrinsicDependence(pFunction);
	//DumpMemInstDependingStore();
}

void StructFieldReach::visit( Function * pFunction )
{
	BuildMemFootPrintMapping(pFunction);
	InitBeforeAfterSet(pFunction);
	IntraFieldReachAnalysis(pFunction);

	vector< pair<MemFootPrint *, int> >  vecLiveInput;
	CollectLiveInput(pFunction, vecLiveInput );
	InterFieldReachAnalysis(pFunction, vecLiveInput);

	CalLoadDependentStore(pFunction);
	CalMemIntrinsicDependence(pFunction);
	ClearCache();
}


void StructFieldReach::InitToDoSet(set<Function *> & ToDo)
{
	this->setToDo = ToDo;
}

void StructFieldReach::runAnalysis()
{
	set<Function *>::iterator itSetBegin = this->setToDo.begin();
	set<Function *>::iterator itSetEnd   = this->setToDo.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		visit(*itSetBegin);
	}

	//DumpLoadDependingStore();
}


bool StructFieldReach::runOnModule(Module& M)
{
	this->pAA = &getAnalysis<AliasAnalysis>();
	this->pDL = &getAnalysis<DataLayout>();
	this->pTLI = &getAnalysis<TargetLibraryInfo>();

	//Function * pFunction = M.getFunction("pp_base_format");

	//Function * pFunction = M.getFunction("get_callee_fndecl");
	//this->setToDo.insert(pFunction);
	//pFunction = M.getFunction("real_zerop");
	//this->setToDo.insert(pFunction);
	//runAnalysis();

	
	return false;
}
