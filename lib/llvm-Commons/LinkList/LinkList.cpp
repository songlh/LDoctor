
#include "llvm/IR/Instructions.h"

#include "llvm-Commons/LinkList/LinkList.h"

namespace llvm_Commons
{

bool isReachableThroughLinkListDereference(Instruction * IA, Instruction * IB, Loop * pLoop)
{
	if(IA == IB)
	{
		return false;
	}	

	if(IA->getType() != IB->getType() )
	{
		return false;
	}

	vector<Instruction *> vecWorkList;
	set<Instruction *> setProcessed;
	vecWorkList.push_back(IA);

	Type * pPointerType = IA->getType();

	while(vecWorkList.size())
	{
		Instruction * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		for(Value::use_iterator U = pCurrent->use_begin(); U != pCurrent->use_end(); U ++ )
		{
			if(Instruction * pInst = dyn_cast<Instruction>(*U))
			{
				if(!pLoop->contains(pInst->getParent()))
				{
					continue;
				}

				if(GetElementPtrInst * pGet = dyn_cast<GetElementPtrInst>(pInst))
				{
					for(Value::use_iterator GU = pGet->use_begin(); GU != pGet->use_end(); GU ++ )
					{
						if(LoadInst * pLoad = dyn_cast<LoadInst>(*GU))
						{
							if(pLoad->getType() != pPointerType)
							{
								continue;
							}

							if(pLoad == IB)
							{
								return true;
							}

							if(setProcessed.find(pLoad) == setProcessed.end())
							{
								setProcessed.insert(pLoad);
								vecWorkList.push_back(pLoad);
							}
						}
					}
				}
				else if(PHINode * pPHI = dyn_cast<PHINode>(pInst))
				{
					if(pPHI == IB)
					{
						return true;
					}

					if(setProcessed.find(pPHI) == setProcessed.end())
					{
						setProcessed.insert(pPHI);
						vecWorkList.push_back(pPHI);
					}
				}
			}
		}
	}

	return false;

}



bool isLinkListLoop(Loop * pLoop, map<PHINode *, set<Value *> > & LinkListHeaderMapping )
{
	BasicBlock * pHeader = pLoop->getHeader();

	vector<PHINode *> vecToDo;

	for(BasicBlock::iterator II = pHeader->begin(); II != pHeader->end(); II ++ )
	{
		if(isa<PHINode>(II))
		{
			if(PointerType * pPointerType = dyn_cast<PointerType>(II->getType()))
			{
				if(isa<StructType>(pPointerType->getElementType()))
				{
					vecToDo.push_back(cast<PHINode>(II));
				}
			}
		}
		else
		{
			break;
		}
	}


	if(vecToDo.size() == 0)
	{
		return false;
	}

	vector<PHINode *>::iterator itVecPhiBegin = vecToDo.begin();
	vector<PHINode *>::iterator itVecPhiEnd   = vecToDo.end();


	for(; itVecPhiBegin != itVecPhiEnd; itVecPhiBegin ++ )
	{
		PHINode * pPHI = *itVecPhiBegin;

		bool bFlag = true;

		for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
		{
			if(pLoop->contains(pPHI->getIncomingBlock(i)))
			{
				if(Instruction * pInst = dyn_cast<Instruction>(pPHI->getIncomingValue(i)))
				{
					if(!isReachableThroughLinkListDereference(pPHI, pInst, pLoop))
					{
						bFlag = false;
						break;
					}
				}
				else
				{
					bFlag = false;
					break;
				}
			}
		}

		if(bFlag)
		{
			for(unsigned i = 0; i < pPHI->getNumIncomingValues(); i ++ )
			{
				if(!pLoop->contains(pPHI->getIncomingBlock(i)))
				{
					LinkListHeaderMapping[pPHI].insert(pPHI->getIncomingValue(i));
				}
			}
		}
	}


	if(LinkListHeaderMapping.size() > 0)
	{
		return true;
	}
	else
	{
		return false;
	}
}


bool isLinkListLoop(Loop * pLoop, set<Value *> & setLinkListHeader)
{
	map<PHINode *, set<Value *> > LinkListHeaderMapping;
	bool bResult = isLinkListLoop(pLoop, LinkListHeaderMapping);

	map<PHINode *, set<Value *> >::iterator itMapBegin = LinkListHeaderMapping.begin();
	map<PHINode *, set<Value *> >::iterator itMapEnd   = LinkListHeaderMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		setLinkListHeader.insert(itMapBegin->second.begin(), itMapBegin->second.end() );
	}

	return bResult;

}

}

