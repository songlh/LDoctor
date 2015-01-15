#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/CFG/CFGUtility.h"
#include "llvm-Commons/Dependence/DependenceUtility.h"
#include "Analysis/InterProcDep/InterProcDep.h"

#include "Redundancy/CL-Redundancy/CLRedundancy.h"

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




void PrintDependence( Instruction * pI, set<Value *> & setDependence )
{

	char pPath[1000];
	pI->dump();

	if( MDNode * N = pI->getMetadata("dbg") )
	{
		DILocation Loc(N);
		string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
		realpath( sFileNameForInstruction.c_str() , pPath);
		sFileNameForInstruction = string(pPath);                        
		unsigned int uLineNoForInstruction = Loc.getLineNumber();
		errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
	}

	set<Value *>::iterator itSetBegin = setDependence.begin();
	set<Value *>::iterator itSetEnd = setDependence.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		(*itSetBegin)->dump();

		if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetBegin))
		{
			if( MDNode * N = pInstruction->getMetadata("dbg") )
			{
				DILocation Loc(N);
				string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
				realpath( sFileNameForInstruction.c_str() , pPath);
				sFileNameForInstruction = string(pPath);                        
				unsigned int uLineNoForInstruction = Loc.getLineNumber();
				errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
			}
		}
		
	}

	errs() << "*******************************************\n";
}

void GetAllReturnInst(Function * pFunction, set<ReturnInst *> & setRet)
{
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{	
			if(ReturnInst * pRet = dyn_cast<ReturnInst>(II)	)
			{
				Value * pRetValue = pRet->getReturnValue();

				if(pRetValue != NULL)
				{
					setRet.insert(pRet);
				}
			}
		}
	}
}


char CrossLoopRedundancy::ID = 0;

void CrossLoopRedundancy::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<InterProcDep>();
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
	this->setPureFunctions.insert("JS_ASSERT");
	this->setPureFunctions.insert("JS_Assert");
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
	this->setFileIO.insert("fgetc");
	this->setFileIO.insert("fflush");
	this->setFileIO.insert("fopen");
	this->setFileIO.insert("fclose");
}

void CrossLoopRedundancy::InitializeLibraryFunctionSet()
{
	InitializePureFunctionSet();
	InitializeMemoryAllocFunctionSet();
	InitializeFileIOFunctionSet();

	this->setLibraryFunctions.insert(this->setPureFunctions.begin(), this->setPureFunctions.end());
	this->setLibraryFunctions.insert(this->setMemoryAllocFunctions.begin(), this->setMemoryAllocFunctions.end());
	this->setLibraryFunctions.insert(this->setFileIO.begin(), this->setFileIO.end());
	this->setLibraryFunctions.insert("rand");
}

void CrossLoopRedundancy::CollectCalleeInsideInnerLoop(Loop * pLoop)
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
				//II->dump();
				CallSite cs(II);

				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				this->CalleeCallSiteMapping[pCalled].insert(II);

				if(this->setLibraryFunctions.find(pCalled->getName()) != this->setLibraryFunctions.end())
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

void CrossLoopRedundancy::DumpInterProcDepResult()
{
	set<Function *>::iterator itSetFuncBegin = this->setCallee.begin();
	set<Function *>::iterator itSetFuncEnd   = this->setCallee.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++)
	{
		errs() << (*itSetFuncBegin)->getName() << "\n";

		errs() << "Store: " << this->IPD->StartEffectStoreMapping[*itSetFuncBegin].size() << "\n";
		errs() << "Mem: "   << this->IPD->StartEffectMemMapping[*itSetFuncBegin].size() << "\n";
		errs() << "Library: " << this->IPD->StartLibraryCallMapping[*itSetFuncBegin].size() << "\n";

		
		set<StoreInst *>::iterator itStoreSetBegin = this->IPD->StartEffectStoreMapping[*itSetFuncBegin].begin();
		set<StoreInst *>::iterator itStoreSetEnd   = this->IPD->StartEffectStoreMapping[*itSetFuncBegin].end();

		map<Function *, map<Instruction *, set<Value *> > > FuncValueDependenceMappingMapping = this->IPD->StartFuncValueDependenceMappingMappingMapping[*itSetFuncBegin];

		for(; itStoreSetBegin != itStoreSetEnd; itStoreSetBegin++ )
		{
			Function * pCurrent = (*itStoreSetBegin)->getParent()->getParent();
			PrintDependence(*itStoreSetBegin, FuncValueDependenceMappingMapping[pCurrent][*itStoreSetBegin]);
		}

		set<MemIntrinsic *>::iterator itMemSetBegin = this->IPD->StartEffectMemMapping[*itSetFuncBegin].begin();
		set<MemIntrinsic *>::iterator itMemSetEnd   = this->IPD->StartEffectMemMapping[*itSetFuncBegin].end();

		for(; itMemSetBegin != itMemSetEnd; itMemSetBegin++ )
		{
			Function * pCurrent = (*itMemSetBegin)->getParent()->getParent();
			PrintDependence(*itMemSetBegin, FuncValueDependenceMappingMapping[pCurrent][*itMemSetBegin]);
		}

		set<Instruction *>::iterator itLibrarySetBegin = this->IPD->StartLibraryCallMapping[*itSetFuncBegin].begin();
		set<Instruction *>::iterator itLibrarySetEnd   = this->IPD->StartLibraryCallMapping[*itSetFuncBegin].end();

		for(; itLibrarySetBegin != itLibrarySetEnd; itLibrarySetBegin ++)
		{
			Function * pCurrent = (*itLibrarySetBegin)->getParent()->getParent();
			PrintDependence(*itLibrarySetBegin, FuncValueDependenceMappingMapping[pCurrent][*itLibrarySetBegin]);
		}


		errs() << "***********************************************************\n";
		errs() << "***********************************************************\n";
	}
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
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}


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

	errs() << "Side Effect: \n";
	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
	{
		(*itSetInstBegin)->dump();
	}

	errs() << "******************************\n";
*/
}


void CrossLoopRedundancy::CollectSideEffectInstructionInsideLoop(Loop * pLoop, set<Instruction *> & setSideEffectInst)
{
	set<BasicBlock *> setBlocksInLoop;

	for( Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB )
	{	
		setBlocksInLoop.insert(*BB);
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
				setSideEffectInst.insert(*itSetInstBegin);
			}
		}
	}

/*
	set<Instruction *>::iterator itSetInstBegin = setSideEffectInst.begin();
	set<Instruction *>::iterator itSetInstEnd   = setSideEffectInst.end();

	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
	{
		(*itSetInstBegin)->dump();
	}

	exit(0);
	*/
}

void CrossLoopRedundancy::LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setValueInput, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG)
{
	set<BasicBlock *> setBlocksInLoop;

	Function * pCurrentFunction = (*pLoop->block_begin())->getParent();

	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
	{
		setBlocksInLoop.insert(*BB);
	}

	set<Value *>::iterator itValSetBegin = setValueInput.begin();
	set<Value *>::iterator itValSetEnd   = setValueInput.end();

	set<Value *> setProcessedValue;

	for(; itValSetBegin != itValSetEnd; itValSetBegin ++ )
	{
		if(!isa<Instruction>(*itValSetBegin))
		{
			setDependentValue.insert(*itValSetBegin);
			continue;
		}

		Instruction * pCurrent = cast<Instruction>(*itValSetBegin);

		if(pCurrent->getParent()->getParent() != pCurrentFunction )
		{
			setDependentValue.insert(*itValSetBegin);
			continue;
		}

		if(setBlocksInLoop.find(pCurrent->getParent()) == setBlocksInLoop.end())
		{
			setDependentValue.insert(*itValSetBegin);
			continue;
		}

		vector<Value *> vecDependingValue;
		setProcessedValue.insert(pCurrent);

		//control flow
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
		GetDependingValue(pCurrent, vecTmp);
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
					setDependentValue.insert(pInstruction);
					continue;
				}

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
					setDependentValue.insert(pLoad);
					continue;
				}

				if(MemIntrinsic * pMem = dyn_cast<MemIntrinsic>(pInstruction))
				{
					setDependentValue.insert(pMem);
					continue;
				}

				if(isa<CallInst>(pInstruction) || isa<InvokeInst>(pInstruction))
				{
					CallSite cs(pInstruction);
					Function * pCalledFunction = cs.getCalledFunction();

					if(this->setPureFunctions.find(pCalledFunction->getName()) != this->setPureFunctions.end() || this->setMemoryAllocFunctions.find(pCalledFunction->getName()) != this->setMemoryAllocFunctions.end())
					{
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

						continue;	
					}
					else if(this->setLibraryFunctions.find(pCalledFunction->getName() ) != this->setLibraryFunctions.end())
					{
						setDependentValue.insert(pInstruction);
						continue;
					}

					map<Instruction *, set<Value *> > ValueDependenceMapping = this->IPD->StartFuncValueDependenceMappingMappingMapping[pCalledFunction][pCalledFunction];
					
					set<ReturnInst *> setRetInst;
					GetAllReturnInst(pCalledFunction, setRetInst);

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
								assert(pArg->getParent() == pCalledFunction);	
								if(setProcessedValue.find(pInstruction->getOperand(pArg->getArgNo())) == setProcessedValue.end() )
								{
									setProcessedValue.insert(pInstruction->getOperand(pArg->getArgNo()));
									vecDependingValue.push_back(pInstruction->getOperand(pArg->getArgNo()));
								}
							}
							else
							{
								if(setProcessedValue.find(*itSetValueBegin) == setProcessedValue.end() )
								{
									setProcessedValue.insert(*itSetValueBegin);
									vecDependingValue.push_back(*itSetValueBegin);
								}
							}
						}
					}

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
				setDependentValue.insert(pCurrentValue);
			}
		}
	}
}


void CrossLoopRedundancy::LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setDependentValue, PostDominatorTree * PDT)
{
	Function * pCurrentFunction = (*pLoop->block_begin())->getParent();
	set<Instruction *> setLoopInstruction;
	CollectSideEffectInstructionInsideLoop(pLoop, setLoopInstruction);

	ControlDependenceGraphBase CDG;
	CDG.graphForFunction(*pCurrentFunction, *PDT);

	set<Value *> setInputInstruction;
	set<Instruction *>::iterator itSetInstBegin = setLoopInstruction.begin();
	set<Instruction *>::iterator itSetInstEnd   = setLoopInstruction.end();

	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
	{
		setInputInstruction.insert(*itSetInstBegin);
	}

	LoopDependenceAnalysis(pLoop, setInputInstruction, setDependentValue, CDG);

	
	//exit(0);

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



/*
void CrossLoopRedundancy::LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setDependingValue, PostDominatorTree * PDT)
{
	Function * pCurrentFunction = (*pLoop->block_begin())->getParent();
	set<Instruction *> setLoopInstruction;
	CollectSideEffectInstructionInsideLoop(pLoop, setLoopInstruction);

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
	set<Instruction *>::iterator itSetInstBegin = setLoopInstruction.begin();
	set<Instruction *>::iterator itSetInstEnd   = setLoopInstruction.end();

	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
	{
		Function * pFunction = (*itSetInstBegin)->getParent()->getParent();

		assert(pFunction == pCurrentFunction);

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

				//add call and invoke return here 

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


	set<Function *>::iterator itSetFuncBegin = this->setCallee.begin();
	set<Function *>::iterator itSetFuncEnd   = this->setCallee.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin++ )
	{
		Function * pCurrentCallee = *itSetFuncBegin;
		int iNumStore = this->IPD->StartEffectStoreMapping[pCurrentCallee].size();
		int iNumMem   = this->IPD->StartEffectMemMapping[pCurrentCallee].size();
		int iNumLibrary = this->IPD->StartLibraryCallMapping.size();

		if(iNumStore + iNumMem + iNumLibrary == 0 )
		{
			continue;
		}

		vector<Value *> vecDependingValue;
		set<Value *> setProcessedValue;

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
		}


		//Value dependence and replace formal argument to real argument

		//worklist
	}
}

*/



bool CrossLoopRedundancy::runOnModule(Module& M)
{
	InitializeLibraryFunctionSet();

	this->pDL = &getAnalysis<DataLayout>();
	char pPath[1000];

	Function * pInnerFunction = SearchFunctionByName(M, strInnerFileName, strInnerFuncName, uInnerSrcLine);
	if(pInnerFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return false;
	}

	PostDominatorTree * PDT = &getAnalysis<PostDominatorTree>(*pInnerFunction);
	LoopInfo * pInnerLI = &(getAnalysis<LoopInfo>(*pInnerFunction));
	Loop * pInnerLoop = SearchLoopByLineNo(pInnerFunction, pInnerLI, uInnerSrcLine);
	//pInnerLoop->dump();
	if(pInnerLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}

	CollectCalleeInsideInnerLoop(pInnerLoop);

	//errs() << "Callee Size: "<< this->setCallee.size() << "\n";

	this->IPD = &getAnalysis<InterProcDep>();
	this->IPD->InitlizeStartFunctionSet(this->setCallee);
	this->IPD->InterProcDependenceAnalysis();

	//errs() << "after inter procedural dependence analysis\n";

	
	set<Value *> setValue;

	LoopDependenceAnalysis(pInnerLoop, setValue, PDT);

	set<Value *>::iterator itSetBegin = setValue.begin();
	set<Value *>::iterator itSetEnd   = setValue.end();

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

