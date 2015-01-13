#include "Workless/Workless.h"

#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/CommandLine.h"

#include <fstream>

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static RegisterPass<Workless> X(
		"workless-analysis",
		"static workless analysis",
		false,
		true);

static cl::opt<unsigned> uSrcLine("noLine", 
					cl::desc("Source Code Line Number for the Loop"), cl::Optional, 
					cl::value_desc("uSrcCodeLine"));


static cl::opt<std::string> strFileName("strFile", 
					cl::desc("File Name for the Loop"), cl::Optional, 
					cl::value_desc("strFileName"));

static cl::opt<std::string> strPureFileName("strPureFile", 
					cl::desc("File Name for pure libraries"), cl::Optional, 
					cl::value_desc("strPureFileName"));

static cl::opt<std::string> strFuncName("strFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strFuncName"));



char Workless::ID = 0;

void Workless::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<DominatorTree>();
	AU.addRequired<LoopInfo>();
}

Workless::Workless(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDominatorTreePass(Registry);
	initializePostDominatorTreePass(Registry);	
}

void Workless::print(raw_ostream &O, const Module *M) const
{
	return;
}

void Workless::ParsePureFunctionList(string & strFileName, Module * pM)
{
	string line;
	ifstream ifile(strFileName.c_str());
	if (ifile.is_open())
	{
		while(getline(ifile, line))
		{
			Function * pFunction = pM->getFunction(line.c_str());
			if(pFunction != NULL)
			{
				//pFunction->dump();
				setPureFunction.insert(pFunction);
			}
		}

		ifile.close();
	}

	//errs() << "number of pure functin:" << setPureFunction.size() << "\n";
}


bool Workless::CollectSideEffectFunction(Function * pFunction)
{
	vector<Function *> vecWorkList;
	set<Function *> setProcessed;

	vecWorkList.push_back(pFunction);
	setProcessed.insert(pFunction);

	while(vecWorkList.size())
	{
		Function * pCurrent = vecWorkList[vecWorkList.size()-1];

		vecWorkList.pop_back();

		if(this->setPureFunction.find(pCurrent) != this->setPureFunction.end())
		{
			continue;
		}

		if(this->setSideEffectFunction.find(pCurrent) != this->setSideEffectFunction.end() )
		{
			this->setSideEffectFunction.insert(pFunction);
			return false;
		}

		if(pCurrent->isDeclaration())
		{
			if(pCurrent->onlyReadsMemory())
			{
				continue;
			}
			else
			{
				this->setSideEffectFunction.insert(pFunction);
				this->setSideEffectFunction.insert(pCurrent);
				return false;
			}
		}


		for(Function::iterator BB = pCurrent->begin(); BB != pCurrent->end(); BB ++ )
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				if(MemIntrinsic * pMem = dyn_cast<MemIntrinsic>(II))
				{
					Value * pDest = pMem->getRawDest();
					if(BeLocalObject(pDest))
					{
						continue;
					} 
					else
					{
						this->setSideEffectFunction.insert(pFunction);
						this->setSideEffectFunction.insert(pCurrent);
						return false;
					}
				}
				else if(IntrinsicInst * pIntr = dyn_cast<IntrinsicInst>(II))
				{
					if(PureIntrinsic(pIntr))
					{
						continue;
					}
					else
					{
						this->setSideEffectFunction.insert(pFunction);
						this->setSideEffectFunction.insert(pCurrent);
						return false;
					}
				}
				else if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					CallSite cs(II);
					Function * pCalledFunction = cs.getCalledFunction();

					if(pCalledFunction == NULL)
					{
						this->setSideEffectFunction.insert(pFunction);
						this->setSideEffectFunction.insert(pCurrent);
						return false;
					}

					if(this->setSideEffectFunction.find(pCalledFunction) != this->setSideEffectFunction.end())
					{
						this->setSideEffectFunction.insert(pCurrent);
						this->setSideEffectFunction.insert(pFunction);
						return false;
					}

					if(this->setPureFunction.find(pCalledFunction) != this->setPureFunction.end() )
					{
						continue;
					}

					if(setProcessed.find(pCalledFunction) == setProcessed.end() )
					{
						setProcessed.insert(pCalledFunction);
						vecWorkList.push_back(pCalledFunction);
					}
				}
				else if(StoreInst * pStore = dyn_cast<StoreInst>(II))
				{
					Value * pDest = pStore->getPointerOperand();
					if(BeLocalObject(pDest))
					{
						continue;
					}
					else
					{
						this->setSideEffectFunction.insert(pFunction);
						this->setSideEffectFunction.insert(pCurrent);
						return false;
					}
				}
				else
				{
					bool bFlag = false;
					switch(II->getOpcode())
					{
						default: break;
						case Instruction::Fence:                    //Instructions may write to memory
						case Instruction::VAArg:
						case Instruction::AtomicCmpXchg:
						case Instruction::AtomicRMW:
							bFlag = true;
							break;
						case Instruction::Load:
							bFlag = !cast<LoadInst>(II)->isUnordered();
							break;
						case Instruction::Resume:               //Instruction may throw
							bFlag = true;
							break;

					}

					if(bFlag)
					{
						this->setSideEffectFunction.insert(pFunction); 
						this->setSideEffectFunction.insert(pCurrent);
						return false;
					}
				}
			}
		}

	}

	this->setPureFunction.insert(pFunction);
	return true;
}

bool Workless::BlockWithoutSideEffect(BasicBlock * BB)
{
	//errs() << BB->getName() << "\n";
	//BB->dump();
	if(isa<UnreachableInst>(BB->getTerminator()))
	{
		return true;
		//errs() << "here" <<"\n";
	}


	for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
	{
		//II->dump();
		//errs() << isa<MemIntrinsic>(II) << " " << isa<CallInst>(II) << "\n";
		if(IntrinsicInst * pIntr = dyn_cast<IntrinsicInst>(II))
		{
			//pIntr->dump();
			if(PureIntrinsic(pIntr))
			{
				continue;
			}
			else
			{
				return false;
			}
		}
		else if(isa<CallInst>(II) || isa<InvokeInst>(II))
		{
			CallSite cs(II);
			Function * pCalledFunction = cs.getCalledFunction();

			if(pCalledFunction == NULL)
			{
				return false;
			}

			if(pCalledFunction->isDeclaration() )
			{
				return false;
			}

			if(this->setSideEffectFunction.find(pCalledFunction) != this->setSideEffectFunction.end())
			{
				return false;
			}
		}
		else if(isa<StoreInst>(II))
		{
			return false;
		}
		else
		{
			bool bFlag = false;
			switch(II->getOpcode())
			{
				default: break;
				case Instruction::Fence:                    //Instructions may write to memory
				case Instruction::VAArg:
				case Instruction::AtomicCmpXchg:
				case Instruction::AtomicRMW:
					bFlag = true;
					break;
				case Instruction::Load:
					bFlag = !cast<LoadInst>(II)->isUnordered();
					break;
				case Instruction::Resume:               //Instruction may throw
					bFlag = true;
					break;

			}

			if(bFlag)
			{
				return false;
			}
		}
	}

	return true;
}


void Workless::Test(Loop * pLoop)
{
	for(Loop::block_iterator b = pLoop->block_begin(); b != pLoop->block_end(); b ++ )
	{
		BasicBlock * BB = *b;

		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			if(isa<DbgInfoIntrinsic>(II))
			{

			}
			else if(CallInst * pCall = dyn_cast<CallInst>(II) )
			{
				Function * pFunction = pCall->getCalledFunction();
				CollectSideEffectFunction(pFunction);

			}
		}
	}

/*
	errs() << "finish function call\n";

	set<Function *>::iterator itSetFuncBegin = this->setSideEffectFunction.begin();
	set<Function *>::iterator itSetFuncEnd   = this->setSideEffectFunction.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++)
	{
		errs() << (*itSetFuncBegin)->getName() << "\n";
		(*itSetFuncBegin)->dump();
	}
*/
}

bool Workless::IsWorkless0Star(set<BasicBlock *> & setType1BasicBlock, set<BasicBlock *> & setType2BasicBlock, MAPBlockBeforeAfterPair & mapBeforeAndAfter )
{
	set<BasicBlock *>::iterator itSetBlockBegin = setType1BasicBlock.begin();
	set<BasicBlock *>::iterator itSetBlockEnd   = setType1BasicBlock.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++)
	{
		 //(*itSetBlockBegin)->dump() ;
		 //errs() << BlockWithoutSideEffect(*itSetBlockBegin) << "\n";
		if(!BlockWithoutSideEffect(*itSetBlockBegin))
		{
			return false;
		}
	}

	itSetBlockBegin = setType2BasicBlock.begin();
	itSetBlockEnd   = setType2BasicBlock.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++ )
	{
		if(!BlockWithoutSideEffect(*itSetBlockBegin))
		{
			return false;
		}
	}

	set<BasicBlock *> setAllBlocks;
	setAllBlocks.insert(setType1BasicBlock.begin(), setType1BasicBlock.end());
	setAllBlocks.insert(setType2BasicBlock.begin(), setType2BasicBlock.end());

	set<Edge> setExitEdge;

	SearchExitEdgesForBlocks(setExitEdge, setAllBlocks);
	
	set<Edge>::iterator itSetEdgeBegin = setExitEdge.begin();
	set<Edge>::iterator itSetEdgeEnd   = setExitEdge.end();

	for(; itSetEdgeBegin != itSetEdgeEnd; itSetEdgeBegin ++)
	{
		SETBefore setBefore = mapBeforeAndAfter[(*itSetEdgeBegin).second].first[(*itSetEdgeBegin).first]; 

		//errs() << itSetEdgeBegin->first->getName() << "->" << itSetEdgeBegin->second->getName() << "\n";


		SETBefore::iterator itSetBegin = setBefore.begin();
		SETBefore::iterator itSetEnd = setBefore.end();

		while(itSetBegin != itSetEnd )
		{
			if( setAllBlocks.find((*itSetBegin)->getParent() ) != setAllBlocks.end() )
			{
				return false;
			}

			itSetBegin++;
		}

	}


	return true;
}

bool Workless::IsWorkless0Star1(set<BasicBlock *> & setType1Block, set<BasicBlock *> & setType2Block, MAPBlockBeforeAfterPair & mapBeforeAndAfter)
{
	set<BasicBlock *>::iterator itSetBlockBegin = setType1Block.begin();
	set<BasicBlock *>::iterator itSetBlockEnd   = setType1Block.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++)
	{
		if(!BlockWithoutSideEffect(*itSetBlockBegin))
		{
			return false;
		}
	}

	if(setType2Block.size() == 0)
	{
		return false;
	}

	itSetBlockBegin = setType2Block.begin();
	itSetBlockEnd   = setType2Block.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++ )
	{

		if(!BlockWithoutSideEffect(*itSetBlockBegin))
		{
			return true;
		}
	}

	set<BasicBlock *> setAllBlocks;
	setAllBlocks.insert(setType1Block.begin(), setType1Block.end());
	setAllBlocks.insert(setType2Block.begin(), setType2Block.end());

	set<Edge> setExitEdge;
	SearchExitEdgesForBlocks(setExitEdge, setAllBlocks);

	set<Edge>::iterator itSetEdgeBegin = setExitEdge.begin();
	set<Edge>::iterator itSetEdgeEnd   = setExitEdge.end();

	bool pureEdge = false;

	for(; itSetEdgeBegin != itSetEdgeEnd; itSetEdgeBegin ++)
	{
		SETBefore setBefore = mapBeforeAndAfter[(*itSetEdgeBegin).second].first[(*itSetEdgeBegin).first]; 
		
		SETBefore::iterator itSetBegin = setBefore.begin();
		SETBefore::iterator itSetEnd = setBefore.end();
		
		bool bFlag = true;

		for(; itSetBegin != itSetEnd; itSetBegin++ )
		{
			if( setType1Block.find((*itSetBegin)->getParent()) != setType1Block.end() )
			{
				if(setType2Block.find((*itSetEdgeBegin).first) != setType2Block.end() )
				{
					bFlag = false;
					continue;
				}
				else
				{
					return false;
				}
			}
			else if(setType2Block.find((*itSetBegin)->getParent()) != setType2Block.end() )
			{
				bFlag = false;
				continue;
			}
		}

		if(bFlag)
		{
			pureEdge = true;
		}

	}

	if(pureEdge)
	{
		return true;
	}
	else
	{
		return false;
	}

}

void Workless::CollectWorkingBlocks(set<BasicBlock *> & setType1Block, set<BasicBlock *> & setType2Block, set<BasicBlock *> & setWorkingBlocks, MAPBlockBeforeAfterPair & mapBeforeAndAfter)
{
	set<BasicBlock *>::iterator itSetBegin = setType1Block.begin();
	set<BasicBlock *>::iterator itSetEnd   = setType1Block.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		if(!BlockWithoutSideEffect(*itSetBegin))
		{
			//errs() << "working block: " << (*itSetBegin)->getName() << "\n";
			setWorkingBlocks.insert(*itSetBegin);
		}
	}

	set<Edge> setExitEdge;
	SearchExitEdgesForBlocks(setExitEdge, setType1Block);

	//errs() << "Exit Edge: " << setExitEdge.size() << "\n";

	set<Edge>::iterator itSetEdgeBegin = setExitEdge.begin();
	set<Edge>::iterator itSetEdgeEnd   = setExitEdge.end();

	for(; itSetEdgeBegin != itSetEdgeEnd; itSetEdgeBegin ++ )
	{
		//if(setType2Block.find(itSetEdgeBegin->second) != setType2Block.end() )
		//{
		//	continue;
		//}

		SETBefore setBefore = mapBeforeAndAfter[itSetEdgeBegin->second].first[itSetEdgeBegin->first];
		//errs() << itSetEdgeBegin->first->getName() << "->" << itSetEdgeBegin->second->getName() << "\n";

		SETBefore::iterator itSetBegin = setBefore.begin();
		SETBefore::iterator itSetEnd = setBefore.end();

		for(; itSetBegin != itSetEnd; itSetBegin++ )
		{
			if( setType1Block.find( ( *itSetBegin)->getParent() ) != setType1Block.end() )
			{
				
				bool bFlag = true;

				for(Value::use_iterator  ubb = (*itSetBegin)->use_begin(); ubb != (*itSetBegin)->use_end(); ubb ++ )
				{
					if(setType1Block.find((cast<Instruction>(*ubb))->getParent()) == setType1Block.end() && setType2Block.find((cast<Instruction>(*ubb))->getParent()) == setType2Block.end() )
					{
						bFlag= false;
						break;
					}
				}

				if(bFlag)
				{
					continue;
				}



				if(PHINode * pPHINode = dyn_cast<PHINode>(*itSetBegin))
				{
					//(*itSetBegin)->dump();
					vector<PHINode *> vecPendingPHIInstructions;
					set<PHINode *> setHandledPHIInstructions;
					for(unsigned int i = 0 ; i < pPHINode->getNumIncomingValues(); i++)
					{
						if(setType1Block.find(pPHINode->getIncomingBlock(i)) != setType1Block.end())
						{
							if(PHINode * pPHI = dyn_cast<PHINode>(pPHINode->getIncomingValue(i)))
							{
								vecPendingPHIInstructions.push_back(pPHI);
								setHandledPHIInstructions.insert(pPHI);
							}
							else if(Instruction * pInst = dyn_cast<Instruction>(pPHINode->getIncomingValue(i)))
							{
								if(setType1Block.find(pInst->getParent()) != setType1Block.end())
								{

									if(this->PDT->dominates(pPHINode->getIncomingBlock(i), pInst->getParent()))
									{
										//errs() << "1" << pInst->getParent()->getName() << "\n";
										setWorkingBlocks.insert(pInst->getParent());
									}
									else
									{
										//errs() << "2" << pPHINode->getIncomingBlock(i)->getName() << "\n";
										setWorkingBlocks.insert(pPHINode->getIncomingBlock(i));
									}
								}
								else
								{
									//errs() << "3" << pPHINode->getIncomingBlock(i)->getName() << "\n";
									setWorkingBlocks.insert(pPHINode->getIncomingBlock(i));
								}
							}
							else
							{
								//errs() << "4" << pPHINode->getIncomingBlock(i)->getName() << "\n";
								setWorkingBlocks.insert(pPHINode->getIncomingBlock(i));
							}
						}
					}

					while(vecPendingPHIInstructions.size() > 0)
					{
						PHINode * pPHICurrent = vecPendingPHIInstructions[vecPendingPHIInstructions.size() -1 ];
						vecPendingPHIInstructions.pop_back();

						//pPHICurrent->dump();
						for(unsigned int i = 0 ; i < pPHICurrent->getNumIncomingValues(); i++)
						{
							if(setType1Block.find(pPHICurrent->getIncomingBlock(i)) != setType1Block.end())
							{
								if(PHINode * pPHI = dyn_cast<PHINode>(pPHICurrent->getIncomingValue(i)))
								{
									if(setHandledPHIInstructions.find(pPHI) == setHandledPHIInstructions.end())
									{
										vecPendingPHIInstructions.push_back(pPHI);
										setHandledPHIInstructions.insert(pPHI);
									}
								}
								else if(Instruction * pInst = dyn_cast<Instruction>(pPHICurrent->getIncomingValue(i)))
								{
									if(setType1Block.find(pInst->getParent()) != setType1Block.end())
									{
										
										if(this->PDT->dominates(pPHICurrent->getIncomingBlock(i), pInst->getParent()))
										{
											//errs() << "5" << pInst->getParent()->getName() << "\n";
											setWorkingBlocks.insert(pInst->getParent());
										}
										else
										{
											//errs() << "6" << pPHICurrent->getIncomingBlock(i)->getName() << "\n";
											setWorkingBlocks.insert(pPHICurrent->getIncomingBlock(i));
										}
									}
									else
									{
										//errs() << "7" << pPHICurrent->getIncomingBlock(i)->getName() << "\n";
										setWorkingBlocks.insert(pPHICurrent->getIncomingBlock(i));
									}
								}
								else
								{
									//errs() << "8" << pPHICurrent->getIncomingBlock(i)->getName() << "\n";
									setWorkingBlocks.insert(pPHICurrent->getIncomingBlock(i));
								}
							}
						}
					}
				}
				else
				{
					setWorkingBlocks.insert((*itSetBegin)->getParent());
				}
			}
		}
	}

	//errs() << "After first loop: " << setWorkingBlocks.size() << "\n";

	set<BasicBlock *> setTmp = setWorkingBlocks;
	setWorkingBlocks.clear();

	itSetBegin = setTmp.begin();
	itSetEnd   = setTmp.end();

	for(; itSetBegin != itSetEnd; itSetBegin++)
	{
		set<BasicBlock *>::iterator itSetBeginTmp = setTmp.begin();
		set<BasicBlock *>::iterator itSetEndTmp   = setTmp.end();

		bool bFlag = true;
		for(; itSetBeginTmp != itSetEndTmp; itSetBeginTmp ++ )
		{
			if(*itSetBegin == *itSetBeginTmp)
			{
				continue;
			}

			if(this->PDT->dominates(*itSetBeginTmp, *itSetBegin))
			{
				bFlag = false;
				break;

			}
		}

		if(bFlag)
		{
			setWorkingBlocks.insert(*itSetBegin);
		}
	}

/*
	set<BasicBlock *>::iterator itSetBlockBegin = setWorkingBlocks.begin();
	set<BasicBlock *>::iterator itSetBlockEnd   = setWorkingBlocks.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++)
	{
		errs() << (*itSetBlockBegin)->getName() << "\n";
	}
	*/
}


bool Workless::IsWorkless0Or1Star(Loop * pLoop, set<BasicBlock *> & setType1Block, set<BasicBlock *> & setType2Block, MAPBlockBeforeAfterPair & mapBeforeAndAfter, set<BasicBlock *> & setWorkingBlocks)
{
	//set<BasicBlock *> setWorkingBlocks;
	CollectWorkingBlocks(setType1Block, setType2Block, setWorkingBlocks, mapBeforeAndAfter);

	//errs() << "working block: " << setWorkingBlocks.size() << "\n";



	if(setWorkingBlocks.size() == 0)
	{
		return false;
	}

	
	BasicBlock * pHeader = pLoop->getHeader();
	//pHeader->dump();
	if(setWorkingBlocks.find(pHeader) != setWorkingBlocks.end())
	{
		return false;
	}


	
	vector<BasicBlock *> vecWorkList;
	set<BasicBlock *> setProcessed;

	for (succ_iterator I = succ_begin(pHeader), E = succ_end(pHeader); I != E; ++I)
	{
		if( pHeader == *I)
		{
			return true;
		}



		if(setWorkingBlocks.find(*I) == setWorkingBlocks.end() && setProcessed.find(*I) == setProcessed.end() && setType1Block.find(*I) != setType1Block.end() )
		{
			setProcessed.insert(*I);
			vecWorkList.push_back(*I);

		}
	}



	
	while(vecWorkList.size() > 0)
	{
		BasicBlock * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		//errs() << pCurrent->getName() << "\n";

		for (succ_iterator I = succ_begin(pCurrent), E = succ_end(pCurrent); I != E; ++I)
		{
			if( pHeader == *I)
			{
				return true;
			}

			if(setWorkingBlocks.find(*I) == setWorkingBlocks.end() && setProcessed.find(*I) == setProcessed.end() && setType1Block.find(*I) != setType1Block.end() )
			{
				setProcessed.insert(*I);
				vecWorkList.push_back(*I);
			}
		}

	}

	return false;

}



void Workless::AnalyzeWorklessType(Function * pFunction, Loop * pLoop)
{
	
	set<BasicBlock *> setType1Blocks;
	set<BasicBlock *> setType2Blocks;

	Search2TypeBlocksInLoop(setType1Blocks, setType2Blocks, pLoop, pFunction, this->PDT, this->DT);
	//errs() << "Type 2 :" << setType2Blocks.size() << "\n";


	MAPBlockBeforeAfterPair mapBeforeAndAfter;
	PreciseLiveAnalysis(mapBeforeAndAfter, pFunction);

	if(IsWorkless0Star(setType1Blocks, setType2Blocks, mapBeforeAndAfter) )
	{
		errs() << "WorkLess 0*\n";
	} 


	if(IsWorkless0Star1(setType1Blocks, setType2Blocks, mapBeforeAndAfter))
	{
		errs() << "Workless 0*1?\n";
	}
	

	set<BasicBlock *> setWorkingBlocks;
	if(IsWorkless0Or1Star(pLoop, setType1Blocks, setType2Blocks, mapBeforeAndAfter, setWorkingBlocks))
	{
		errs() << "Workless [0|1]*\n";
		errs() << "Working blocks: \n";
		set<BasicBlock *>::iterator itSetBlockBegin = setWorkingBlocks.begin();
		set<BasicBlock *>::iterator itSetBlockEnd   = setWorkingBlocks.end();

		for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin++ )
		{
			errs() << "=" << (*itSetBlockBegin)->getName() << "\n";
		}
	}

}




bool Workless::runOnModule(Module& M)
{	

	Function * pFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);
	if(pFunction == NULL)
	{
		errs() << "Cannot find the input function\n";
		return false;
	}

	//pFunction->dump();

	this->DT = &getAnalysis<DominatorTree>(*pFunction);
	this->PDT = &getAnalysis<PostDominatorTree>(*pFunction);

	LoopInfo *pLoopInfo = &(getAnalysis<LoopInfo>(*pFunction));
	Loop * pLoop = SearchLoopByLineNo(pFunction, pLoopInfo, uSrcLine);

	//pLoop->dump();
	if(pLoop == NULL)
	{
		errs() << "Cannot find the input loop\n";
		return false;
	}

	if(strPureFileName != "")
	{
		ParsePureFunctionList(strPureFileName, &M);
	}


	for(Module::iterator FF = M.begin(); FF != M.end(); FF++)
	{
		CollectSideEffectFunction(FF);
	}

	

/*
	set<Function *>::iterator itSetBegin = this->setSideEffectFunction.begin();
	set<Function *>::iterator itSetEnd   = this->setSideEffectFunction.end();

	for(; itSetBegin != itSetEnd; itSetBegin++ )
	{
		errs() << (*itSetBegin)->getName() <<  "\n";
	}
*/
	AnalyzeWorklessType(pFunction, pLoop);

	return false;
}

