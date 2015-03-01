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

static cl::opt<std::string> strLoopHeader("strLoopHeader",
					cl::desc("Block Name for Inner Loop"), cl::Optional,
					cl::value_desc("strLoopHeader"));

static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));

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

char CrossLoopRedundancy::ID = 0;

void CrossLoopRedundancy::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<InterProcDep>();
	AU.addRequired<ScalarEvolution>();
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
					setSideEffectInsts.insert(II);
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
						setSideEffectInsts.insert(II);
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

	MAPBlockBeforeAfterPair mapBeforeAndAfter;
	PreciseLiveAnalysis(mapBeforeAndAfter, pFunction);

	set<Edge> setEdges;
	SearchExitEdgesForLoop(setEdges, pLoop);

	set<Edge>::iterator itEdgeBegin = setEdges.begin();
	set<Edge>::iterator itEdgeEnd = setEdges.end();

	for(; itEdgeBegin != itEdgeEnd; itEdgeBegin++)
	{
		SETBefore::iterator itSetInstBegin = mapBeforeAndAfter[(*itEdgeBegin).second].first[(*itEdgeBegin).first].begin();
		SETBefore::iterator itSetInstEnd = mapBeforeAndAfter[(*itEdgeBegin).second].first[(*itEdgeBegin).first].end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin++)
		{
			if(setBlocksInLoop.find((*itSetInstBegin)->getParent()) != setBlocksInLoop.end() )
			{
				setSideEffectInsts.insert(*itSetInstBegin);
			}
		}
	}

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
}

void CrossLoopRedundancy::CalDependenceForSEInst(Loop * pLoop, set<Instruction *> & SEInst, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG)
{
	set<Instruction *>::iterator itInstSetBegin = SEInst.begin();
	set<Instruction *>::iterator itInstSetEnd   = SEInst.end();

	for(; itInstSetBegin != itInstSetEnd; itInstSetBegin ++ )
	{
		if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(*itInstSetBegin))
		{
			setDependentValue.insert(pMem);
			continue;
		}

		vector<Value *> vecValueDependence;
		GetDependingValue(*itInstSetBegin, vecValueDependence);

		if(isa<CallInst>(*itInstSetBegin) || isa<InvokeInst>(*itInstSetBegin) )
		{
			CallSite cs(*itInstSetBegin);
			Function * pCalled = cs.getCalledFunction();

			//assert(this->setCallee.find(pCalled) == this->setCallee.end());
			if(this->setCallee.find(pCalled) != this->setCallee.end())
			{
				setDependentValue.insert(*itInstSetBegin);
				continue;
			}
		}

		vector<Value *>::iterator itVecValueBegin = vecValueDependence.begin();
		vector<Value *>::iterator itVecValueEnd   = vecValueDependence.end();

		if(isa<MemIntrinsic>(*itInstSetBegin))
		{
			itVecValueBegin++;
		}

		for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
		{
			setDependentValue.insert(*itVecValueBegin);
		}

		for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
		{
			if(CDG.influences(*BB, (*itInstSetBegin)->getParent()))
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

//all content are dependence
void CrossLoopRedundancy::LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setValueInput, set<Value *> & setDependentValue, ControlDependenceGraphBase & CDG)
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


void CrossLoopRedundancy::LoopDependenceAnalysis(Loop * pLoop, set<Value *> & setDependentValue, PostDominatorTree * PDT)
{
	Function * pCurrentFunction = pLoop->getHeader()->getParent();
	
	set<Instruction *> setLoopInstruction;
	CollectSideEffectInstructionInsideLoop(pLoop, setLoopInstruction);

	ControlDependenceGraphBase CDG;
	CDG.graphForFunction(*pCurrentFunction, *PDT);

	set<Value *> setSEInstDependence ;
	CalDependenceForSEInst(pLoop, setLoopInstruction, setSEInstDependence, CDG);

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

bool CrossLoopRedundancy::DataDependingOnItself(PHINode * pPHI, Loop * pLoop)
{
	vector<Instruction *> vecWorkList;
	vecWorkList.push_back(pPHI);

	set<Instruction *> setProcessed;
	Function * pCurrentFunction = pLoop->getHeader()->getParent();

	while(vecWorkList.size()>0)
	{
		Instruction * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		if(setProcessed.find(pCurrent) != setProcessed.end() )
		{
			continue;
		}

		setProcessed.insert(pCurrent);
		
		//skip all instrumented site
		if(pCurrent->getParent()->getParent() != pCurrentFunction )
		{
			continue;
		}

		if(!pLoop->contains(pCurrent->getParent()))
		{
			continue;
		}

		if(isa<LoadInst>(pCurrent) || isa<MemTransferInst>(pCurrent))
		{
			continue;
		}

		vector<Value *> vecValueDependence;

		if(isa<CallInst>(pCurrent) || isa<InvokeInst>(pCurrent) )
		{
			CallSite cs(pCurrent);
			Function * pCalled = cs.getCalledFunction();

			if(pCalled == NULL)
			{
				continue;
			}

			if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end())
			{
				if(this->LibraryTypeMapping[pCalled] != LF_TRANSPARENT && this->LibraryTypeMapping[pCalled] != LF_MALLOC )
				{
					continue;
				}
				else
				{
					GetDependingValue(pCurrent, vecValueDependence);
				}
			}
			else if(pCalled->isDeclaration() )
			{
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

		for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
		{
			if(Instruction * pInst = dyn_cast<Instruction>(*itVecValueBegin))
			{
				if(pInst == pPHI)
				{
					return true;
				}

				if(setProcessed.find(pInst) == setProcessed.end())
				{
					vecWorkList.push_back(pInst);
				}
			}
		}
	}

	return false;
}


bool CrossLoopRedundancy::ControlDependingOnItself(PHINode * pPHI, Loop * pLoop, ControlDependenceGraphBase & CDG)
{

	vector<Instruction *> vecWorkList;
	set<Instruction *> setProcessed;

	Function * pCurrentFunction = pLoop->getHeader()->getParent();

	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); ++ BB)
	{
		if(CDG.influences(*BB, pPHI->getParent()))
		{
			TerminatorInst * pTerminator = (*BB)->getTerminator();
			if(pTerminator !=NULL)
			{
				if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
				{
					if(pBranch->isConditional())
					{
						if(Instruction * pInst = dyn_cast<Instruction>(pBranch->getCondition()))
						{
							if(pPHI == pInst)
							{
								return true;
							}

							vecWorkList.push_back(pInst);
						}
					}
				}
				else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
				{
					if(Instruction * pInst = dyn_cast<Instruction>(pSwitch->getCondition()))
					{
						if(pPHI == pInst)
						{
							return true;
						}

						vecWorkList.push_back(pInst);
					}					
				}
			}
		}
	}
				
	while(vecWorkList.size()>0)
	{
		Instruction * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		if(setProcessed.find(pCurrent) != setProcessed.end() )
		{
			continue;
		}

		setProcessed.insert(pCurrent);
		
		//skip all instrumented site
		if(pCurrent->getParent()->getParent() != pCurrentFunction )
		{
			continue;
		}

		if(!pLoop->contains(pCurrent->getParent()))
		{
			continue;
		}

		if(isa<LoadInst>(pCurrent) || isa<MemTransferInst>(pCurrent))
		{
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
				continue;
			}

			if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end())
			{
				if(this->LibraryTypeMapping[pCalled] != LF_TRANSPARENT && this->LibraryTypeMapping[pCalled] != LF_MALLOC )
				{
					continue;
				}
				else
				{
					GetDependingValue(pCurrent, vecValueDependence);
				}
			}
			else if(pCalled->isDeclaration() )
			{
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
			if(Instruction * pInst = dyn_cast<Instruction>(*itVecValueBegin))
			{
				if(pInst == pPHI)
				{
					return true;
				}

				if(setProcessed.find(pInst) == setProcessed.end())
				{
					vecWorkList.push_back(pInst);
				}
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
							if(Instruction * pInst = dyn_cast<Instruction>(pBranch->getCondition()))
							{
								if(pInst == pPHI)
								{
									return true;
								}

								if(setProcessed.find(pInst) == setProcessed.end())
								{
									vecWorkList.push_back(pInst);
								}
							}

						}
					}
					else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
					{
						if(Instruction * pInst = dyn_cast<Instruction>(pSwitch->getCondition()))
						{
							if(pInst == pPHI)
							{
								return true;
							}

							if(setProcessed.find(pInst) == setProcessed.end() )
							{
								vecWorkList.push_back(pInst);
							}
						}
					}
				}
			}
		}
	}

	return false;
}

void CrossLoopRedundancy::AnalyzeValueDefinedOutsideLoop(set<Value *> & setDependentValue, Loop * pLoop , PostDominatorTree * PDT)
{
	set<Value *>::iterator itSetValBegin = setDependentValue.begin();
	set<Value *>::iterator itSetValEnd   = setDependentValue.end();

	BasicBlock * pHeader = pLoop->getHeader();
	Function * pCurrentFunction = pHeader->getParent();

	ControlDependenceGraphBase CDG;
	CDG.graphForFunction(*pCurrentFunction, *PDT);

	for(; itSetValBegin != itSetValEnd; itSetValBegin ++ )
	{
		if(Instruction * pInst = dyn_cast<Instruction>(*itSetValBegin))
		{
			if(pInst->getParent()->getParent() != pCurrentFunction)
			{
				continue;
			}

			if(pLoop->contains(pInst->getParent()))
			{
				continue;
			}
		}
		else if(!isa<Argument>(*itSetValBegin))
		{
			continue;
		}

		Value * pValue = *itSetValBegin;
		set<PHINode *> UseOne;
		set<Instruction *> UseOther;

		CollectAllUsesInsideLoop(pValue, pLoop, UseOne, UseOther);

		if(UseOther.size() > 0)
		{
			this->OutsideValueKindMapping[pValue] = OVK_NotOnlyOne;
			continue;
		}

		set<PHINode *>::iterator itPHIBegin = UseOne.begin();
		set<PHINode *>::iterator itPHIEnd   = UseOne.end();

		bool bControl = false;
		bool bData    = false;

		for(; itPHIBegin != itPHIEnd; itPHIBegin ++ )
		{
			bControl = bControl || ControlDependingOnItself( *itPHIBegin, pLoop, CDG);
			bData    = bData || DataDependingOnItself(*itPHIBegin, pLoop);
		}

		if(!bControl && !bData)
		{
			this->OutsideValueKindMapping[pValue] = OVK_NoDependence;
			continue;
		}

		if(bControl && !bData)
		{
			set<Value *> setOtherValue;

			itPHIBegin = UseOne.begin();
			itPHIEnd   = UseOne.end();

			for(; itPHIBegin != itPHIEnd; itPHIBegin ++ )
			{
				for(unsigned i = 0; i < (*itPHIBegin)->getNumIncomingValues(); i ++ )
				{
					if(pLoop->contains((*itPHIBegin)->getIncomingBlock(i)))
					{
						setOtherValue.insert((*itPHIBegin)->getIncomingValue(i));
					}
				}
			}

			if(setOtherValue.size() == 1)
			{
				this->OutsideValueKindMapping[pValue] = OVK_OnlyControl;
			}
			else
			{
				this->OutsideValueKindMapping[pValue] = OVK_Other;
			}

			continue;
		}

		itPHIBegin = UseOne.begin();
		itPHIEnd   = UseOne.end();

		for(; itPHIBegin != itPHIEnd; itPHIBegin ++ )
		{
			if(IsIterativeVariable(*itPHIBegin, pLoop, this->SE))
			{
				this->OutsideValueKindMapping[pValue] = OVK_Evolve;
				int64_t stride = CalculateStride(*itPHIBegin, pLoop, this->SE, this->pDL);
				
				if(stride != 0 )
				{
					this->IterativePHIMapping[pValue].push_back(*itPHIBegin);
					this->IterativeStrideMapping[pValue].push_back(stride);
				}


			}
		}
	}
}



bool CrossLoopRedundancy::runOnModule(Module& M)
{
	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	this->pDL = &getAnalysis<DataLayout>();

	Function * pInnerFunction = SearchFunctionByName(M, strInnerFileName, strInnerFuncName, uInnerSrcLine);
	if(pInnerFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return false;
	}

	this->SE  = &getAnalysis<ScalarEvolution>(*pInnerFunction);

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

	set<Value *> setValue;

	LoopDependenceAnalysis(pInnerLoop, setValue, PDT);

	map<Value *, OutsideValueKind> OutsideValueKindMapping;

	//AnalyzeValueDefinedOutsideLoop(setValue, pInnerLoop,  PDT);

	set<Value *>::iterator itSetBegin = setValue.begin();
	set<Value *>::iterator itSetEnd   = setValue.end();

	set<Value *> setTripCounter;
	CalCulateLoopTripCounter(pInnerLoop, this->SE, setTripCounter); 

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		if(Instruction * pInst = dyn_cast<Instruction>(*itSetBegin))
		{
			if(isa<AllocaInst>(pInst))
			{
				continue;
			}

			PrintInstructionInfo(pInst);
/*
			if(this->OutsideValueKindMapping.find(pInst) != this->OutsideValueKindMapping.end())
			{
				if(this->OutsideValueKindMapping[pInst] == OVK_NoDependence )
				{
					errs() << "//---No Dependence Skip\n";
				}
				else if(this->OutsideValueKindMapping[pInst] == OVK_OnlyControl)
				{
					errs() << "//---Control Skip\n";
				}
				else if(this->OutsideValueKindMapping[pInst] == OVK_Evolve)
				{
					errs() << "//---Start of Iterative Variable ";

					if(IterativeStrideMapping[pInst].size() >0)
					{
						errs() << "Stride: ";

						for(unsigned i = 0; i < IterativeStrideMapping[pInst].size(); i ++ )
						{
							errs() << IterativeStrideMapping[pInst][i] << " ";
						}
					}

					errs() << "\n";

				}
			}

			if(setTripCounter.find(pInst) != setTripCounter.end())
			{
				errs() << "//---Possible Loop Boundary\n";
			}
*/
		}
		else if(Argument * pArg = dyn_cast<Argument>(*itSetBegin))
		{
			PrintArgumentInfo(pArg);

/*
			if(this->OutsideValueKindMapping.find(pArg) != this->OutsideValueKindMapping.end())
			{
				if(this->OutsideValueKindMapping[pArg] == OVK_NoDependence )
				{
					errs() << "//---No Dependence Skip\n";
				}
				else if(this->OutsideValueKindMapping[pArg] == OVK_OnlyControl)
				{
					errs() << "//---Control Skip\n";
				}
				else if(this->OutsideValueKindMapping[pArg] == OVK_Evolve)
				{
					errs() << "//---Start of Iterative Variable ";

					if(IterativeStrideMapping[pArg].size() >0)
					{
						errs() << "Stride: ";

						for(unsigned i = 0; i < IterativeStrideMapping[pArg].size(); i ++ )
						{
							errs() << IterativeStrideMapping[pArg][i] << " ";
						}
					}

					errs() << "\n";
				}
			}

			if(setTripCounter.find(pArg) != setTripCounter.end())
			{
				errs() << "//---Possible Loop Boundary\n";
			}
*/
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

	

/*
	map<Instruction *, vector<Value * > >::iterator itBoundaryMapBegin = mapBoundary.begin();
	map<Instruction *, vector<Value * > >::iterator itBoundaryMapEnd   = mapBoundary.end();

	for(; itBoundaryMapBegin != itBoundaryMapEnd; itBoundaryMapBegin++ )
	{
		errs() << "//---" << "Interative Variables: ";
		Instruction * pInst = itBoundaryMapBegin->first;
		PrintInstructionInfo(pInst);
		
		vector<Value *>::iterator itVecBegin = itBoundaryMapBegin->second.begin();
		vector<Value *>::iterator itVecEnd   = itBoundaryMapBegin->second.end();

		for(; itVecBegin != itVecEnd; itVecBegin++)
		{
			errs() << "//---Boundary: ";
			if(Instruction * pI = dyn_cast<Instruction>(*itVecBegin))
			{
				PrintInstructionInfo(pI);
			}
			else if(Argument * pArg = dyn_cast<Argument>(*itVecBegin))
			{
				PrintArgumentInfo(pArg);
			}
		}

	
	}

*/
	return false;
}

