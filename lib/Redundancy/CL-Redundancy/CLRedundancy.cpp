#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/CFG/CFGUtility.h"
#include "llvm-Commons/Dependence/DependenceUtility.h"

#include "Redundancy/CL-Redundancy/CLRedundancy.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/CommandLine.h"



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

static cl::opt<unsigned> uOuterSrcLine("noOuterLine", 
					cl::desc("Source Code Line Number for Outer Loop"), cl::Optional, 
					cl::value_desc("uSrcOuterCodeLine"));

static cl::opt<std::string> strOuterFileName("strOuterFile", 
					cl::desc("File Name for Outer Loop"), cl::Optional, 
					cl::value_desc("strOuterFileName"));

static cl::opt<std::string> strOuterFuncName("strOuterFunc", 
					cl::desc("Function Name for Outer Loop"), cl::Optional, 
					cl::value_desc("strOuterFuncName"));


static RegisterPass<CrossLoopRedundancy> X(
		"cross-loop-redundancy",
		"cross loop redundancy analysis",
		false,
		true);

char CrossLoopRedundancy::ID = 0;

void CrossLoopRedundancy::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
}

CrossLoopRedundancy::CrossLoopRedundancy(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	
}

void CrossLoopRedundancy::print(raw_ostream &O, const Module *M) const
{
	return;
}

void CrossLoopRedundancy::InitializePureFunctionSet()
{
	this->setPureFunctions.insert("floor_log2");
	this->setPureFunctions.insert("exact_log2");
	this->setPureFunctions.insert("_ZSt18_Rb_tree_incrementPSt18_Rb_tree_node_base");

}

void CrossLoopRedundancy::InitializeMemoryAllocFunctionSet()
{
	this->setMemoryAllocFunctions.insert("ggc_alloc");
	this->setMemoryAllocFunctions.insert("malloc");
	this->setMemoryAllocFunctions.insert("xcalloc");
}

void CrossLoopRedundancy::InitializeFileIOFunctionSet()
{
	this->setFileIO.insert("fwrite");
	this->setFileIO.insert("fputc");
	this->setFileIO.insert("fflush");
	this->setFileIO.insert("fopen");
	this->setFileIO.insert("fclose");
}


void CrossLoopRedundancy::CollectSideEffectInstruction(Loop * pLoop, set<Instruction *> & setSideEffectInsts)
{
	vector<Function *> vecWorkList;
	set<Function *> setProcessed;
	set<BasicBlock *> setBlocksInLoop;

	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{
		
		setBlocksInLoop.insert(*BB);
		for(BasicBlock::iterator II = (*BB)->begin() ; II != (*BB)->end(); ++ II)
		{
			if(StoreInst * pStore = dyn_cast<StoreInst>(II) )
			{
				setSideEffectInsts.insert(pStore);
			}
			else if(isa<CallInst>(II) || isa<InvokeInst>(II) )
			{
				if(isa<DbgInfoIntrinsic>(II))
				{
					continue;
				}

				if(isa<MemIntrinsic>(II))
				{
					setSideEffectInsts.insert(II);
					continue;
				}

				CallSite cs(II);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				if(this->setPureFunctions.find(pCalled->getName()) != this->setPureFunctions.end())
				{
					continue;
				}

				if(this->setMemoryAllocFunctions.find(pCalled->getName()) != this->setMemoryAllocFunctions.end())
				{
					setSideEffectInsts.insert(II);
					continue;
				}

				if(pCalled->isDeclaration())
				{
					setSideEffectInsts.insert(II);
					continue;
				}

				if(setProcessed.find(pCalled) == setProcessed.end())
				{
					setProcessed.insert(pCalled);
					vecWorkList.push_back(pCalled);
				}
			}
		}
	}

	while(vecWorkList.size()>0)
	{
		Function * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		for(Function::iterator BB = pCurrent->begin(); BB != pCurrent->end(); BB ++ )
		{
			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				if(StoreInst * pStore = dyn_cast<StoreInst>(II))
				{
					Value * pPointer = pStore->getPointerOperand();
					Value * pBase = GetUnderlyingObject(pPointer, this->pDL);

					if(!BeLocalObject(pBase))
					{
						setSideEffectInsts.insert(pStore);
					}
				}
				else if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					if(isa<DbgInfoIntrinsic>(II))
					{
						continue;
					}

					if(MemIntrinsic * pMem = dyn_cast<MemIntrinsic>(II))
					{
						Value * pPointer = pMem->getRawDest();
						Value * pBase = GetUnderlyingObject(pPointer, this->pDL);

						if(!BeLocalObject(pBase))
						{
							setSideEffectInsts.insert(II);
						}
						
						continue;
					}

					CallSite cs(II);
					Function * pCalled = cs.getCalledFunction();

					if(pCalled == NULL)
					{
						continue;
					}

					if(this->setPureFunctions.find(pCalled->getName()) != this->setPureFunctions.end())
					{
						continue;
					}

					if(this->setMemoryAllocFunctions.find(pCalled->getName()) != this->setMemoryAllocFunctions.end())
					{
						setSideEffectInsts.insert(II);
						continue;
					}

					if(pCalled->isDeclaration())
					{
						setSideEffectInsts.insert(II);
						continue;
					}

					if(setProcessed.find(pCalled) == setProcessed.end())
					{
						setProcessed.insert(pCalled);
						vecWorkList.push_back(pCalled);
					}
				}
			}
		}
	}

	Function * pFunction = (*pLoop->block_begin())->getParent();

	MAPBeforeAfterPair mapBeforeAfter;
	LiveAnalysis(mapBeforeAfter, pFunction);

	set<Edge> setEdges;
	SearchExitEdgesForLoop(setEdges, pLoop);

	set<Edge>::iterator itEdgeBegin = setEdges.begin();
	set<Edge>::iterator itEdgeEnd = setEdges.end();

	for(; itEdgeBegin != itEdgeEnd; itEdgeBegin++)
	{
		SETBefore::iterator itSetInstBegin = mapBeforeAfter[itEdgeBegin->second].first.begin();
		SETBefore::iterator itSetInstEnd = mapBeforeAfter[itEdgeBegin->second].first.end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin++)
		{
			if(setBlocksInLoop.find((*itSetInstBegin)->getParent()) != setBlocksInLoop.end() )
			{
				setSideEffectInsts.insert(*itSetInstBegin);
			}
		}
	}

/*
	set<Instruction *>::iterator itSetInstBegin = setSideEffectInsts.begin();
	set<Instruction *>::iterator itSetInstEnd   = setSideEffectInsts.end();

	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
	{
		(*itSetInstBegin)->dump();
	}

*/
}


void CrossLoopRedundancy::LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setDependingValue, PostDominatorTree * PDT)
{
	Function * pCurrentFunction = (*pLoop->block_begin())->getParent();
	set<Instruction *> setInstruction;
	CollectSideEffectInstruction(pLoop, setInstruction);

	//errs() << pCurrentFunction->getName() << "\n";
	//PostDominatorTree * PDT = &getAnalysis<PostDominatorTree>(*pCurrentFunction);

	ControlDependenceGraphBase CDG;
	CDG.graphForFunction(*pCurrentFunction, *PDT);
	
	set<BasicBlock *> setBlocksInLoop;

	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{
		setBlocksInLoop.insert(*BB);
	}

	//errs() << "Here\n";
	set<Instruction *>::iterator itSetInstBegin = setInstruction.begin();
	set<Instruction *>::iterator itSetInstEnd   = setInstruction.end();

	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
	{
		Function * pFunction = (*itSetInstBegin)->getParent()->getParent();
		if(pFunction != pCurrentFunction)
		{
			continue;
		}

		vector<Value *> vecDependingValue;
		set<Value *> setProcessedValue;
		setProcessedValue.insert(*itSetInstBegin);

		//control flow
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
							if(setProcessedValue.find(pBranch->getCondition()) == setProcessedValue.end() )
							{

								setProcessedValue.insert(pBranch->getCondition());
								vecDependingValue.push_back(pBranch->getCondition());
							}
						}
					}
					else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
					{
						if(setProcessedValue.find(pSwitch->getCondition()) == setProcessedValue.end())
						{
							setProcessedValue.insert(pSwitch->getCondition());
							vecDependingValue.push_back(pSwitch->getCondition());
						}
					}
				}
			}
		}

		vector<Value *> vecTmp;
		GetDependingValue(*itSetInstBegin, vecTmp);
		vector<Value *>::iterator itVecValueBegin = vecTmp.begin();
		vector<Value *>::iterator itVecValueEnd   = vecTmp.end();

		for(; itVecValueBegin != itVecValueEnd ; itVecValueBegin ++)
		{
			if(setProcessedValue.find(*itVecValueBegin) == setProcessedValue.end() )
			{
				setProcessedValue.insert(*itVecValueBegin);
				vecDependingValue.push_back(*itVecValueBegin);
			}
		}

		


		while(vecDependingValue.size() > 0)
		{
			Value * pCurrentValue = vecDependingValue[vecDependingValue.size()-1];
			vecDependingValue.pop_back();

			if(Instruction * pInstruction = dyn_cast<Instruction>(pCurrentValue))
			{
				if(setBlocksInLoop.find(pInstruction->getParent()) == setBlocksInLoop.end())
				{
					setDependingValue.insert(pInstruction);
					continue;
				}

				//add function call here

				for(Loop::block_iterator BB = pLoop->block_begin() ; BB != pLoop->block_end(); ++ BB)
				{
					if(CDG.influences(*BB, pInstruction->getParent()))
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
										setProcessedValue.insert(pBranch->getCondition());
										vecDependingValue.push_back(pBranch->getCondition());
									}
								}
							}
							else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator) )
							{
								if(setProcessedValue.find(pSwitch->getCondition()) == setProcessedValue.end())
								{
									setProcessedValue.insert(pSwitch->getCondition());
									vecDependingValue.push_back(pSwitch->getCondition());
								}
							}
						}
					}
				}

				if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction) )
				{
					setDependingValue.insert(pLoad);
					continue;
				}

				vecTmp.clear();
				GetDependingValue(pInstruction, vecTmp);

				itVecValueBegin = vecTmp.begin();
				itVecValueEnd = vecTmp.end();

				for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++)
				{
					if( setProcessedValue.find(*itVecValueBegin) == setProcessedValue.end() )
					{
						setProcessedValue.insert(*itVecValueBegin);
						vecDependingValue.push_back(*itVecValueBegin);
					}
				}
			}
			else
			{
				setDependingValue.insert(pCurrentValue);
			}
		}

	}

}



bool CrossLoopRedundancy::runOnModule(Module& M)
{

	InitializePureFunctionSet();
	InitializeMemoryAllocFunctionSet();
	InitializeFileIOFunctionSet();

	this->pDL = &getAnalysis<DataLayout>();

	Function * pInnerFunction = SearchFunctionByName(M, strInnerFileName, strInnerFuncName, uInnerSrcLine);
	if(pInnerFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return false;
	}

	PostDominatorTree * PDT = &getAnalysis<PostDominatorTree>(*pInnerFunction);
	LoopInfo * pInnerLI = &(getAnalysis<LoopInfo>(*pInnerFunction));
	Loop * pInnerLoop = SearchLoopByLineNo(pInnerFunction, pInnerLI, uInnerSrcLine);
	pInnerLoop->dump();
	if(pInnerLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}

	set<Value *> setValue;
	LoopDependenceAnalysis(pInnerLoop, setValue, PDT);

	set<Value *>::iterator itSetBegin = setValue.begin();
	set<Value *>::iterator itSetEnd   = setValue.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		if(Instruction * pInst = dyn_cast<Instruction>(*itSetBegin))
		{
			MDNode *Node = pInst->getMetadata("ins_id");
			if(Node!=NULL)
			{
				assert(Node->getNumOperands() == 1);
				ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
				assert(CI);
				errs() << "Inst " << CI->getZExtValue() << ":";
			}

			pInst->dump();
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
			(*itSetBegin)->dump();
		}
	}


	return false;
}

