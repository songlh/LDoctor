#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "llvm-Commons/Invariant/InvariantAnalysis.h"
#include "llvm-Commons/CFG/CFGUtility.h"
#include "llvm-Commons/Dependence/DependenceUtility.h"
#include "Redundancy/CI-Redundancy/CIRedundancy.h"

#include "llvm/DebugInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

#include "llvm-Commons/Search/Search.h"

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


static RegisterPass<CrossIterationRedundancy> X(
		"cross-iteration-redundancy",
		"cross iteration redundancy analysis",
		false,
		true);

char CrossIterationRedundancy::ID = 0;

void CrossIterationRedundancy::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<DataLayout>();
	AU.addRequired<TargetLibraryInfo>();
	AU.addRequired<AliasAnalysis>();
	AU.addRequired<StructFieldReach>();
	AU.addRequired<PostDominatorTree>();
	
}

CrossIterationRedundancy::CrossIterationRedundancy(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeTargetLibraryInfoPass(Registry);
	initializeAliasAnalysisAnalysisGroup(Registry);
	initializePostDominatorTreePass(Registry);	
}

void CrossIterationRedundancy::print(raw_ostream &O, const Module *M) const
{
	return;
}


bool CmpValueSet(set<Value *> & setA, set<Value *> & setB)
{
	if(setA.size() != setB.size())
	{
		return false;
	}

	set<Value *>::iterator itSetBegin = setA.begin();
	set<Value *>::iterator itSetEnd = setA.end();

	for(; itSetBegin != itSetEnd; itSetBegin++)
	{
		if(setB.find(*itSetBegin) == setB.end() )
		{
			return false;
		}
	}

	return true;
}

void BuildScope(Function * pFunction, set<Function *> & setScope )
{
	vector<Function *> vecWorkList;
	vecWorkList.push_back(pFunction);
	setScope.insert(pFunction);

	while(vecWorkList.size()>0)
	{
		Function * pCurrentFunction = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		for(Function::iterator BB = pCurrentFunction->begin(); BB != pCurrentFunction->end(); BB ++)
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
			{
				if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					if(isa<DbgInfoIntrinsic>(II))
					{
						continue;
					}

					CallSite cs(II);
					Function * pCalledFunction = cs.getCalledFunction();

					if(pCalledFunction == NULL)
					{
						continue;
					}

					if(pCalledFunction->isDeclaration())
					{
						continue;
					}

					if(setScope.find(pCalledFunction) == setScope.end())
					{
						setScope.insert(pCalledFunction);
						vecWorkList.push_back(pCalledFunction);
					}
				}
			}

		}
	}
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

void GetAllCallSite(Function * pFunction, set<Instruction *> & setCallSite )
{
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			if(isa<CallInst>(II) || isa<InvokeInst>(II) )
			{
				setCallSite.insert(II);
			}
		}
	}
}

void AddIntraDependence(Instruction * pValue, Value * pDependence, set<Instruction *> & setProcessedInst, set<Value *> & setDependence, 
						map<Instruction *, set<Instruction *> > & DependenceValueMapping)
{
	if(Instruction * pInstruction = dyn_cast<Instruction>(pDependence))
	{
		if(setProcessedInst.find(pInstruction) != setProcessedInst.end() )
		{
			return;
		}

/*
		if(DependenceValueMapping.find(pInstruction) == DependenceValueMapping.end())
		{
			set<Instruction *> setValueInst;
			DependenceValueMapping[pInstruction] = setValueInst;
		}
*/

		DependenceValueMapping[pInstruction].insert(pValue);
		setProcessedInst.insert(pInstruction);
	}

	setDependence.insert(pDependence);
}


void AddInterDependence(Value * pValue, Value * pDependence, set<Value *> & setProcessedInst, 
						set<Value *> & setDependence, map<Value *, set<Value *> > & DependenceValueMapping)
{
	if(Instruction * pInstruction = dyn_cast<Instruction>(pDependence) )
	{
		if(setProcessedInst.find(pInstruction) != setProcessedInst.end())
		{
			return;
		}
/*
		if(DependenceValueMapping.find(pInstruction) == DependenceValueMapping.end())
		{
			set<Value *> setValue;
			DependenceValueMapping[pInstruction] = setValue;
		}
*/
		DependenceValueMapping[pInstruction].insert(pValue);
		setProcessedInst.insert(pInstruction);
	}
	else if(Argument * pArg = dyn_cast<Argument>(pDependence))
	{
		if(setProcessedInst.find(pArg) != setProcessedInst.end() )
		{
			return;
		}
/*
		if(DependenceValueMapping.find(pArg) == DependenceValueMapping.end() )
		{
			set<Value *> setValue;
			DependenceValueMapping[pArg] = setValue;
		}
*/
		DependenceValueMapping[pArg].insert(pValue);
		setProcessedInst.insert(pArg);
	}

	setDependence.insert(pDependence);
}

void PrintIntraDependence( Instruction * pI, set<Value *> & setDependence )
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

void CrossIterationRedundancy::InitializePureFunctionSet()
{
	this->setPureFunctions.insert("floor_log2");
	this->setPureFunctions.insert("exact_log2");
}

void CrossIterationRedundancy::InitializeMemoryAllocFunctionSet()
{
	this->setMemoryAllocFunctions.insert("ggc_alloc");
	this->setMemoryAllocFunctions.insert("malloc");
	this->setMemoryAllocFunctions.insert("xcalloc");
}

void CrossIterationRedundancy::BuildCallerCalleeMapping(Function * pFunction)
{
	vector<Function *> vecWorkList;
	vecWorkList.push_back(pFunction);

	set<Function *> setEmptyFuncSet;
	this->CalleeCallerMapping[pFunction] = setEmptyFuncSet;
	set<Instruction *> setEmptyCallSite;
	this->CalleeCallSiteMapping[pFunction] = setEmptyCallSite;

	while(vecWorkList.size()>0)
	{
		Function * pCurrentFunction = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		set<Function *> setCalledFunction;
		this->CallerCalleeMapping[pCurrentFunction] = setCalledFunction;

		set<Instruction *> setCallSite;
		this->CallerCallSiteMapping[pCurrentFunction] = setCallSite;

		for(Function::iterator BB = pCurrentFunction->begin(); BB != pCurrentFunction->end(); BB ++ )
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					if(isa<DbgInfoIntrinsic>(II))
					{
						continue;
					}

					CallSite cs(II);
					Function * pCalledFunction = cs.getCalledFunction();

					if(pCalledFunction == NULL)
					{
						continue;
					}

					this->CallerCallSiteMapping[pCurrentFunction].insert(II);
					this->CallerCalleeMapping[pCurrentFunction].insert(pCalledFunction);

					if(pCalledFunction->isDeclaration())
					{
						continue;
					}

					if(this->setMemoryAllocFunctions.find(pCalledFunction->getName()) != this->setMemoryAllocFunctions.end())
					{	
						continue;
					}

					this->CalleeCallerMapping[pCalledFunction].insert(pCurrentFunction);
					this->CalleeCallSiteMapping[pCalledFunction].insert(II);

					if(this->CallerCalleeMapping.find(pCalledFunction) == this->CallerCalleeMapping.end() )
					{
						vecWorkList.push_back(pCalledFunction);
					}
				}
			}
		}
	}


/*
	map<Function *, set<Function *> >::iterator itMapBegin = this->CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itMapEnd = this->CallerCalleeMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		errs() << itMapBegin->first->getName() << "\n";
		
		set<Function *>::iterator itSetBegin = itMapBegin->second.begin();
		set<Function *>::iterator itSetEnd = itMapBegin->second.end();

		for(; itSetBegin != itSetEnd; itSetBegin ++ )
		{
			errs() << (*itSetBegin)->getName() << "\n";
		}	

		errs() << "*********************************\n";
	}
*/

}





void CrossIterationRedundancy::AnalyzeMemReadInst(Function * pFunction)
{
	BuildCallerCalleeMapping(pFunction);

	set<Function *> setScope; 
	BuildScope(pFunction, setScope);

	map<Function *, set<Function *> >::iterator itCallerMapBegin = this->CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd = this->CallerCalleeMapping.end();

	set<Value *> setInvariantGlobal;

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin ++ )
	{
		set<Value *> setInvariantGlobalVariable;
		set<Value *> setInvariantArray;

		IndentifyInvariantGlobalVariable(itCallerMapBegin->first, setInvariantGlobalVariable, setScope);
		IndentifyInvariantArray(itCallerMapBegin->first, setInvariantArray, setScope);

		setInvariantGlobal.insert(setInvariantGlobalVariable.begin(), setInvariantGlobalVariable.end());
		setInvariantGlobal.insert(setInvariantArray.begin(), setInvariantArray.end());
	}

	itCallerMapBegin = this->CallerCalleeMapping.begin();

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin ++ )
	{
		Function * pCurrentFunction = itCallerMapBegin->first;

		for(Function::iterator BB = pCurrentFunction->begin(); BB != pCurrentFunction->end(); BB ++ )
		{
			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
				{
					Value * pPointer = pLoad->getPointerOperand();
					Value * pBase = GetUnderlyingObject(pPointer, this->pDL);

					if(BeLocalObject(pBase))
					{
						this->LoadTypeMapping[pLoad] = MO_LOCAL;
						continue;
					}

					if(BeInputArgument(pBase))
					{
						this->LoadTypeMapping[pLoad] = MO_INPUT;
						continue;
					}

					if(setInvariantGlobal.find(pBase) != setInvariantGlobal.end())
					{
						this->LoadTypeMapping[pLoad] = MO_INVARIANT;
						continue;
					}

					this->LoadTypeMapping[pLoad] = MO_OTHER;
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
				{
					pair<MemoryObjectType, MemoryObjectType> pairTmp;

					Value * pDestPointer = pMem->getRawDest();
					Value * pDestBase = GetUnderlyingObject(pDestPointer, this->pDL);

					if(BeLocalObject(pDestBase))
					{
						pairTmp.first = MO_LOCAL;
					}
					else if(BeInputArgument(pDestBase))
					{
						pairTmp.first = MO_INPUT;
					}
					else if(setInvariantGlobal.find(pDestBase) != setInvariantGlobal.end())
					{
						pairTmp.first = MO_INVARIANT;
					}
					else
					{
						pairTmp.first = MO_OTHER;
					}

					Value * pSrcPointer = pMem->getRawSource();
					Value * pSrcBase = GetUnderlyingObject(pSrcPointer, this->pDL);

					if(BeLocalObject(pSrcBase))
					{
						pairTmp.second = MO_LOCAL;
					}
					else if(BeInputArgument(pSrcBase))
					{
						pairTmp.second = MO_INPUT;
					}
					else if(setInvariantGlobal.find(pSrcBase) != setInvariantGlobal.end())
					{
						pairTmp.second = MO_INVARIANT;
					}
					else
					{
						pairTmp.second = MO_OTHER;
					}

					this->MemTypeMapping[pMem] = pairTmp;
				}
			}
		}
	}

}

int CrossIterationRedundancy::CountLocalLoad()
{
	int iLocal = 0;
	int iInput = 0;

	map<LoadInst *, MemoryObjectType>::iterator itMapLoadBegin = this->LoadTypeMapping.begin();
	map<LoadInst *, MemoryObjectType>::iterator itMapLoadEnd = this->LoadTypeMapping.end();

	for(; itMapLoadBegin != itMapLoadEnd; itMapLoadBegin ++)
	{
		if(itMapLoadBegin->second == MO_LOCAL)
		{
			iLocal ++;
		}
		else if(itMapLoadBegin->second == MO_INPUT)
		{
			iInput ++;
		}
	}


	map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> >::iterator itMapMemBegin = this->MemTypeMapping.begin();
	map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> >::iterator itMapMemEnd = this->MemTypeMapping.end();

	for(; itMapMemBegin != itMapMemEnd; itMapMemBegin ++)
	{
		if(itMapMemBegin->second.second == MO_LOCAL)
		{
			iLocal++;
		}
		else if(itMapMemBegin->second.second == MO_INPUT)
		{
			iInput++;
		}
	}

	return iLocal;
}

void CrossIterationRedundancy::DumpInstructionInfo(Function * pFunction, unsigned uLine)
{
	StoreInst * pStore = NULL;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			if(StoreInst * pS = dyn_cast<StoreInst>(II) )
			{
				if( MDNode * N = pS->getMetadata("dbg") )
				{
					DILocation Loc(N);                       
					if(Loc.getLineNumber() == uLine)
					{
						pStore = pS;
					}
				}
			}
		}
	}

	if(pStore == NULL)
	{
		return;
	}

	PrintIntraDependence(pStore, this->FuncValueDependenceMappingMapping[pFunction][pStore]);

}

void CrossIterationRedundancy::CollectSideEffectInst(set<Instruction *> & setCallSite, set<StoreInst *> & setStore, set<MemIntrinsic *> & setMemIntrics)
{
	map<Function *, set<Function *> >::iterator itCallerMapBegin = this->CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd = this->CallerCalleeMapping.end();

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin ++ )
	{
		Function * pCurrentFunction = itCallerMapBegin->first;
		for(Function::iterator BB = pCurrentFunction->begin(); BB != pCurrentFunction->end(); BB ++)
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
						setStore.insert(pStore);
					}
				}
				else if(MemIntrinsic * pMem = dyn_cast<MemIntrinsic>(II))
				{
					Value * pPointer = pMem->getRawDest();
					Value * pBase = GetUnderlyingObject(pPointer, this->pDL);
					if(!BeLocalObject(pBase))
					{
						setMemIntrics.insert(pMem);
					}
				}
				else if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					if(isa<DbgInfoIntrinsic>(II))
					{
						continue;
					}

					CallSite cs(II);
					Function * pCalledFunction = cs.getCalledFunction();

					if(pCalledFunction == NULL)
					{
						continue;
					}

					if(this->setPureFunctions.find(pCalledFunction->getName()) != this->setPureFunctions.end())
					{
						continue;
					}

					if(this->setMemoryAllocFunctions.find(pCalledFunction->getName()) != this->setMemoryAllocFunctions.end() )
					{
						setCallSite.insert(II);
						continue;
					}

					if(pCalledFunction->isDeclaration())
					{
						setCallSite.insert(II);
						continue;
					}
				}
			}
		}
	}
}



void CrossIterationRedundancy::DependenceAnalysisInfeasiblePath(Function * pFunction)
{
	set<ReturnInst *> setRetInst;
	set<Instruction *> setCallSite;
	set<StoreInst *> setStore;
	set<MemIntrinsic *> setMemIntrics;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			if(ReturnInst * pRet = dyn_cast<ReturnInst>(II))
			{
				Value * pReturnValue = pRet->getReturnValue();
				if(pReturnValue != NULL )
				{
					setRetInst.insert(pRet);
				}
			}
		}
	}

	CollectSideEffectInst(setCallSite, setStore, setMemIntrics);
	
	errs() << "Store:" << setStore.size() << "\n";
	errs() << "MemIntrinsic: " << setMemIntrics.size() << "\n";
	errs() << "Library Call Sites: " << setCallSite.size() << "\n";

	char  pPath[1000];

	vector<Value *> vecWorkList;
	map<Value *, set<Value *> > mapProcessedInstruction;

	map<Function *, set<Value *> > FunctionControlDepMapping;

	map<Function *, set<Function *> >::iterator itCallerMapBegin = this->CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd   = this->CallerCalleeMapping.end();

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin++ )
	{
		Function * pF = itCallerMapBegin->first;
		ControlDependenceGraphBase CDG;
		PostDominatorTree & PDT = getAnalysis<PostDominatorTree>(*pF);

		CDG.graphForFunction(*pF, PDT);

		for(Function::iterator b = pF->begin(); b != pF->end(); b ++)
		{
			if(isa<UnreachableInst>(b->getTerminator()))
			{
				continue;
			}


			//collect control flow dependence 
			vector<Value *> CFGDependentValue;
			for(Function::iterator btmp = pF->begin(), betmp=pF->end(); btmp != betmp; btmp++ )
			{
				if(btmp == b)
				{
					continue;
				}

				if(CDG.controls(btmp, b))
				{
					TerminatorInst * pTerminator = btmp->getTerminator();
					if(pTerminator !=NULL)
					{
						if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
						{
							if(pBranch->isConditional())
							{
								CFGDependentValue.push_back(pBranch->getCondition());
							}
						}
						else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
						{
							CFGDependentValue.push_back(pSwitch->getCondition());
						}
					}
				}
			}

			for(BasicBlock::iterator i = b->begin(); i != b->end(); i ++ )
			{
				vector<Value *>::iterator itVecValueBegin = CFGDependentValue.begin();
				vector<Value *>::iterator itVecValueEnd = CFGDependentValue.end();

				set<Value *> setDependence;
				set<Value *> setProcessedInst;
				setProcessedInst.insert(i);

				//add control flow dependence
				for(; itVecValueBegin != itVecValueEnd; itVecValueBegin++ )
				{
					AddInterDependence(i, *itVecValueBegin, setProcessedInst, setDependence, this->DependenceValueMapping);
				}

				if(isa<CallInst>(i) || isa<InvokeInst>(i))
				{
					CallSite cs(i);
					Function * pCalledFunction = cs.getCalledFunction();

					if(this->CallerCalleeMapping.find(pCalledFunction) != this->CallerCalleeMapping.end() )
					{
						if(FunctionControlDepMapping.find(pCalledFunction) == FunctionControlDepMapping.end() )
						{
							set<Value *> setFuncControlDep;
							FunctionControlDepMapping[pCalledFunction] = setFuncControlDep;
						}

						itVecValueBegin = CFGDependentValue.begin();
						itVecValueEnd = CFGDependentValue.end();

						for(; itVecValueBegin != itVecValueEnd; itVecValueBegin++)
						{
							FunctionControlDepMapping[pCalledFunction].insert(*itVecValueBegin);
						}


						//add return dependence
						set<ReturnInst *> setRet;
						GetAllReturnInst(pCalledFunction, setRet);

						set<ReturnInst *>::iterator itRetBegin = setRet.begin();
						set<ReturnInst *>::iterator itRetEnd = setRet.end();

						for(; itRetBegin != itRetEnd; itRetBegin++ )
						{
							AddInterDependence(i, *itRetBegin, setProcessedInst, setDependence, this->DependenceValueMapping);
						}

						//add formal and real argument dependence
						unsigned uIndex = 0;
						for(Function::arg_iterator argBegin = pCalledFunction->arg_begin(); argBegin != pCalledFunction->arg_end(); argBegin ++ )
						{
							if(this->ValueDependenceMapping.find(argBegin) == this->ValueDependenceMapping.end())
							{
								set<Value *> setArgDependence;
								this->ValueDependenceMapping[argBegin] = setArgDependence;
							}

							if(mapProcessedInstruction.find(argBegin) == mapProcessedInstruction.end() )
							{
								set<Value *> setArgProcessInst;
								setArgProcessInst.insert(argBegin);
								mapProcessedInstruction[argBegin] = setArgProcessInst;
							}

							this->ValueDependenceMapping[argBegin].insert(i->getOperand(uIndex));

							if(this->DependenceValueMapping.find(i->getOperand(uIndex)) == this->DependenceValueMapping.end() )
							{
								set<Value *> setArgValue;
								this->DependenceValueMapping[i->getOperand(uIndex)] = setArgValue;
							}

							this->DependenceValueMapping[i->getOperand(uIndex)].insert(argBegin);

							vecWorkList.push_back(argBegin);

							uIndex ++;
						}
					}
					else 
					{

						//library call
						vector<Value *> vecOperator;
						GetDependingValue(i, vecOperator);

						itVecValueBegin = vecOperator.begin();
						itVecValueEnd = vecOperator.end();

						for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
						{
							AddInterDependence(i, *itVecValueBegin, setProcessedInst, setDependence, this->DependenceValueMapping);
						}
					}
				}
				else
				{
					vector<Value *> vecOperator;
					GetDependingValue(i, vecOperator);

					itVecValueBegin = vecOperator.begin();
					itVecValueEnd = vecOperator.end();

					for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
					{
						AddInterDependence(i, *itVecValueBegin, setProcessedInst, setDependence, this->DependenceValueMapping);
					}

					if(LoadInst * pLoad = dyn_cast<LoadInst>(i))
					{
						//if(this->LoadTypeMapping[pLoad] == MO_LOCAL || this->LoadTypeMapping[pLoad] == MO_INPUT)
						if(this->LoadTypeMapping[pLoad] == MO_LOCAL)
						{
							set<Instruction *>::iterator itSetInstBegin = this->LoadDependentInstMapping[pLoad].begin();
							set<Instruction *>::iterator itSetInstEnd = this->LoadDependentInstMapping[pLoad].end();

							for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
							{
								AddInterDependence(i, *itSetInstBegin, setProcessedInst, setDependence, this->DependenceValueMapping);
							}
						}
					}
					else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(i))
					{
						//if(this->MemTypeMapping[pMem].second == MO_LOCAL || this->MemTypeMapping[pMem].second == MO_INPUT)
						if(this->MemTypeMapping[pMem].second == MO_LOCAL)
						{
							set<Instruction *>::iterator itSetInstBegin = this->MemInstDependentInstMapping[pMem].begin();
							set<Instruction *>::iterator itSetInstEnd = this->MemInstDependentInstMapping[pMem].end();

							for(; itSetInstBegin != itSetInstEnd ; itSetInstBegin ++)
							{
								AddInterDependence(i, *itSetInstBegin, setProcessedInst, setDependence, this->DependenceValueMapping);
							}
						}
					}

				}

				mapProcessedInstruction[i] = setProcessedInst;
				this->ValueDependenceMapping[i] = setDependence;
				vecWorkList.push_back(i);

			}
		}
	}

	map<Function *, set<Value *> >::iterator itMapFuncDepBegin = FunctionControlDepMapping.begin();
	map<Function *, set<Value *> >::iterator itMapFuncDepEnd = FunctionControlDepMapping.end();

	for(; itMapFuncDepBegin != itMapFuncDepEnd; itMapFuncDepBegin ++)
	{
		Function * pCurrent = itMapFuncDepBegin->first;

		if(pCurrent->getName() == "tree_cons" )
		{

			for(Function::arg_iterator argBegin = pCurrent->arg_begin(); argBegin != pCurrent->arg_end(); argBegin ++ )
			{
				errs() << this->ValueDependenceMapping[argBegin].size() << "\n";
			}
		}

		for(Function::iterator BB = pCurrent->begin(); BB != pCurrent->end(); BB ++ )
		{
			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				set<Value *>::iterator itVecValueBegin = itMapFuncDepBegin->second.begin();
				set<Value *>::iterator itVecValueEnd = itMapFuncDepBegin->second.end();

				for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
				{
					AddDependence(II, *itVecValueBegin, mapProcessedInstruction[II], this->ValueDependenceMapping[II]);
				}
			}
		}
	}


	while(vecWorkList.size() > 0)
	{
		Value * pCurrentValue = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		set<Value *> setNewDependentValue;
		set<Value *>::iterator itSetBegin = this->ValueDependenceMapping[pCurrentValue].begin();
		set<Value *>::iterator itSetEnd = this->ValueDependenceMapping[pCurrentValue].end();

/*
		if(StoreInst * pStore = dyn_cast<StoreInst>(pCurrentValue))
		{
			if(MDNode * N = pStore->getMetadata("dbg"))
			{
				DILocation Loc(N);
				if(Loc.getLineNumber() == 1057 )
				{
					set<Value *>::iterator itSetDepBegin = this->ValueDependenceMapping[pCurrentValue].begin();
					set<Value *>::iterator itSetDepEnd = this->ValueDependenceMapping[pCurrentValue].end();

					for(;itSetDepBegin != itSetDepEnd; itSetDepBegin++)
					{
						if(Instruction * pI = dyn_cast<Instruction>(*itSetDepBegin)) 
						{
							pI->dump();

							if(MDNode * pN = pI->getMetadata("dbg"))
							{
								DILocation Loc2(pN);
								string sFileNameForInstruction = Loc2.getDirectory().str() + "/" + Loc2.getFilename().str();    
								realpath( sFileNameForInstruction.c_str() , pPath);
								sFileNameForInstruction = string(pPath);                        
								unsigned int uLineNoForInstruction = Loc2.getLineNumber();
								errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";

							}
						}
					}

					errs() << "***********************************************************\n";
				}
			}
		}
*/
		for(; itSetBegin != itSetEnd; itSetBegin ++ )
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetBegin) )
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction) )
				{
					if(this->LoadTypeMapping[pLoad] != MO_LOCAL)
					{
						setNewDependentValue.insert(pLoad);
						continue;
					}
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInstruction))
				{
					if(this->MemTypeMapping[pMem].first != MO_LOCAL)
					{
						setNewDependentValue.insert(pMem);
						continue;
					}
				}

				set<Value *>::iterator itSetTmpBegin = this->ValueDependenceMapping[pInstruction].begin();
				set<Value *>::iterator itSetTmpEnd = this->ValueDependenceMapping[pInstruction].end();

				for(; itSetTmpBegin != itSetTmpEnd; itSetTmpBegin ++ )
				{
					if(isa<Instruction>(*itSetTmpBegin) || isa<Argument>(*itSetTmpBegin))
					{
						if(mapProcessedInstruction[pCurrentValue].find(*itSetTmpBegin) != mapProcessedInstruction[pCurrentValue].end() )
						{
							continue;
						}

						mapProcessedInstruction[pCurrentValue].insert(*itSetTmpBegin);
					}

					setNewDependentValue.insert(*itSetTmpBegin);
				}
			}
			else if(Argument * pArg = dyn_cast<Argument>(*itSetBegin))
			{
				if(this->ValueDependenceMapping.find(pArg) == this->ValueDependenceMapping.end() )
				{
					setNewDependentValue.insert(pArg);
					continue;
				} 

				set<Value *>::iterator itSetTmpBegin = this->ValueDependenceMapping[pArg].begin();
				set<Value *>::iterator itSetTmpEnd = this->ValueDependenceMapping[pArg].end();

				for(; itSetTmpBegin != itSetTmpEnd; itSetTmpBegin ++ )
				{
					if(isa<Instruction>(*itSetTmpBegin) || isa<Argument>(*itSetTmpBegin))
					{
						if(mapProcessedInstruction[pCurrentValue].find(*itSetTmpBegin) != mapProcessedInstruction[pCurrentValue].end() )
						{
							continue;
						}

						mapProcessedInstruction[pCurrentValue].insert(*itSetTmpBegin);
					}

					setNewDependentValue.insert(*itSetTmpBegin);
				}

			}
			else
			{
				setNewDependentValue.insert(*itSetBegin);
			}
		}

		if(!CmpValueSet(setNewDependentValue, this->ValueDependenceMapping[pCurrentValue]))
		{
			this->ValueDependenceMapping[pCurrentValue] = setNewDependentValue;

			if(LoadInst * pLoad = dyn_cast<LoadInst>(pCurrentValue))
			{
				if(this->LoadTypeMapping[pLoad] != MO_LOCAL)
				{
					continue;
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pCurrentValue) )
			{
				if(this->MemTypeMapping[pMem].first != MO_LOCAL)
				{
					continue;
				}
			}

			set<Value *>::iterator itSetBegin = this->DependenceValueMapping[pCurrentValue].begin();
			set<Value *>::iterator itSetEnd = this->DependenceValueMapping[pCurrentValue].end();

			for(; itSetBegin != itSetEnd; itSetBegin ++)
			{
				vecWorkList.push_back(*itSetBegin);
			}
		}
	}

	set<StoreInst *>::iterator itSetBegin = setStore.begin();
	set<StoreInst *>::iterator itSetEnd = setStore.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		(*itSetBegin)->dump();

		if( MDNode * N = (*itSetBegin)->getMetadata("dbg") )
		{
			DILocation Loc(N);
			string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
			realpath( sFileNameForInstruction.c_str() , pPath);
			sFileNameForInstruction = string(pPath);                        
			unsigned int uLineNoForInstruction = Loc.getLineNumber();
			errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
		}

		set<Value *>::iterator itSetValueBegin = this->ValueDependenceMapping[*itSetBegin].begin();
		set<Value *>::iterator itSetValueEnd = this->ValueDependenceMapping[*itSetBegin].end();

		for(; itSetValueBegin != itSetValueEnd; itSetValueBegin++ )
		{
			(*itSetValueBegin)->dump();
			
			if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetValueBegin))
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
		errs() << "***********************************************\n";
	}
}

void CrossIterationRedundancy::IntraProcedureDependenceAnalysis(Function * pFunction)
{
	if(this->FuncValueDependenceMappingMapping.find(pFunction) != this->FuncValueDependenceMappingMapping.end() )
	{
		return;
	}

	map<Instruction *, set<Value *> > ValueDependenceMapping;
	map<Instruction *, set<Instruction *> > DependenceValueMapping;
	map<Instruction *, set<Instruction *> > mapInstProcessedInst;
	map<Instruction *, set<Value *> > CallSiteCDependenceMapping;

	ControlDependenceGraphBase CDG;
	PostDominatorTree & PDT = getAnalysis<PostDominatorTree>(*pFunction);
	CDG.graphForFunction(*pFunction, PDT);

	vector<Instruction *> vecWorkList;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++)
	{
		if(isa<UnreachableInst>(BB->getTerminator()))
		{
			continue;
		}

	    //collect control flow dependence 
		vector<Value *> CFGDependentValue;
		for(Function::iterator BBtmp = pFunction->begin(); BBtmp != pFunction->end(); BBtmp++ )
		{	
			if(BBtmp == BB)
			{
				continue;
			}
		
			if(CDG.influences(BBtmp, BB))
			{
				TerminatorInst * pTerminator = BBtmp->getTerminator();
				if(pTerminator !=NULL)
				{
					if(BranchInst * pBranch = dyn_cast<BranchInst>(pTerminator))
					{
						if(pBranch->isConditional())
						{
							CFGDependentValue.push_back(pBranch->getCondition());
						}
					}
					else if(SwitchInst * pSwitch = dyn_cast<SwitchInst>(pTerminator))
					{
						CFGDependentValue.push_back(pSwitch->getCondition());
					}
				}
			}
		}

		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			vector<Value *>::iterator itVecValueBegin = CFGDependentValue.begin();
			vector<Value *>::iterator itVecValueEnd = CFGDependentValue.end();

			set<Value *> setDependence;
			set<Instruction *> setProcessedInst;
			setProcessedInst.insert(II);

			//add control flow dependence
			for(; itVecValueBegin != itVecValueEnd; itVecValueBegin++ )
			{
				AddIntraDependence(II, *itVecValueBegin, setProcessedInst, setDependence, DependenceValueMapping);
			}

			if(isa<CallInst>(II) || isa<InvokeInst>(II) )
			{
				if(!isa<DbgInfoIntrinsic>(II))
				{
					/*
					set<Value *> setControlDep;
					CallSiteCDependenceMapping[II] = setControlDep;
					*/

					itVecValueBegin = CFGDependentValue.begin();
					itVecValueEnd = CFGDependentValue.end();

					for(; itVecValueBegin != itVecValueEnd; itVecValueBegin++ )
					{
						CallSiteCDependenceMapping[II].insert(*itVecValueBegin);
					}
				}
			}

			vector<Value *> vecOperator;
			GetDependingValue(II, vecOperator);

			itVecValueBegin = vecOperator.begin();
			itVecValueEnd = vecOperator.end();
			
			for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
			{
				AddIntraDependence(II, *itVecValueBegin, setProcessedInst, setDependence, DependenceValueMapping);
			}

			if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
			{
				if(this->LoadTypeMapping[pLoad] == MO_LOCAL)
				{
					set<Instruction *>::iterator itSetInstBegin = this->LoadDependentInstMapping[pLoad].begin();
					set<Instruction *>::iterator itSetInstEnd = this->LoadDependentInstMapping[pLoad].end();

					for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
					{
						AddIntraDependence(II, *itSetInstBegin, setProcessedInst, setDependence, DependenceValueMapping);
					}
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
			{
				if(this->MemTypeMapping[pMem].second == MO_LOCAL)
				{
					set<Instruction *>::iterator itSetInstBegin = this->MemInstDependentInstMapping[pMem].begin();
					set<Instruction *>::iterator itSetInstEnd = this->MemInstDependentInstMapping[pMem].end();

					for(; itSetInstBegin != itSetInstEnd ; itSetInstBegin ++)
					{
						AddIntraDependence(II, *itSetInstBegin, setProcessedInst, setDependence, DependenceValueMapping);
					}
				}
			}

			mapInstProcessedInst[II] = setProcessedInst;
			ValueDependenceMapping[II] = setDependence;
			vecWorkList.push_back(II);
		}
	}


	while(vecWorkList.size() > 0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		set<Value *> setNewDependentValue;

		set<Value *>::iterator itSetBegin = ValueDependenceMapping[pCurrent].begin();
		set<Value *>::iterator itSetEnd = ValueDependenceMapping[pCurrent].end();

		for(; itSetBegin != itSetEnd; itSetBegin ++ )
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetBegin))
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction) )
				{
					if(this->LoadTypeMapping[pLoad] != MO_LOCAL)
					{
						setNewDependentValue.insert(pLoad);
						continue;
					}
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInstruction) )
				{
					if(this->MemTypeMapping[pMem].first != MO_LOCAL)
					{
						setNewDependentValue.insert(pMem);
						continue;
					}
				}
				else if(isa<CallInst>(pInstruction) || isa<InvokeInst>(pInstruction))
				{
					CallSite cs(pInstruction);
					Function * pCalled = cs.getCalledFunction();

					if(this->CallerCalleeMapping.find(pCalled) != this->CallerCalleeMapping.end() )
					{
						setNewDependentValue.insert(pInstruction);
						continue;
					}
				}

				if(ValueDependenceMapping.find(pInstruction) == ValueDependenceMapping.end())
				{
					setNewDependentValue.insert(pInstruction);
					continue;
				}

				set<Value *>::iterator itSetTmpBegin = ValueDependenceMapping[pInstruction].begin();
				set<Value *>::iterator itSetTmpEnd = ValueDependenceMapping[pInstruction].end();
				for(; itSetTmpBegin != itSetTmpEnd; itSetTmpBegin ++ )
				{
					if(Instruction * pDependentInst = dyn_cast<Instruction>(*itSetTmpBegin))
					{
						if(mapInstProcessedInst[pCurrent].find(pDependentInst) != mapInstProcessedInst[pCurrent].end() )
						{
							continue;
						}

						mapInstProcessedInst[pCurrent].insert(pDependentInst);
					}

					setNewDependentValue.insert(*itSetTmpBegin);
				}

			}
			else
			{
				setNewDependentValue.insert(*itSetBegin);
			}
		}

		if(!CmpValueSet(setNewDependentValue, ValueDependenceMapping[pCurrent]))
		{
			ValueDependenceMapping[pCurrent] = setNewDependentValue;
			
			if(pCurrent->getParent()->getParent() != pFunction)
			{
				continue;
			}

			if(LoadInst * pLoad = dyn_cast<LoadInst>(pCurrent))
			{
				if(this->LoadTypeMapping[pLoad] != MO_LOCAL)
				{
					continue;
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pCurrent))
			{
				if(this->MemTypeMapping[pMem].first != MO_LOCAL)
				{
					continue;
				}
			}
			else if(isa<CallInst>(pCurrent) || isa<InvokeInst>(pCurrent) )
			{
				CallSite cs(pCurrent);
				Function * pCalled = cs.getCalledFunction();

				if(this->CallerCalleeMapping.find(pCalled) != this->CallerCalleeMapping.end() )
				{
					continue;
				}

			}

			set<Instruction *>::iterator itSetInstBegin = DependenceValueMapping[pCurrent].begin();
			set<Instruction *>::iterator itSetInstEnd =   DependenceValueMapping[pCurrent].end();

			for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
			{
				vecWorkList.push_back(*itSetInstBegin);
			}

		}
	}

	this->FuncValueDependenceMappingMapping[pFunction] = ValueDependenceMapping;
	this->FuncDependenceValueMappingMapping[pFunction] = DependenceValueMapping;
	this->FuncInstProcessedInstMappingMapping[pFunction] = mapInstProcessedInst;
	this->FuncCallSiteCDependenceMappingMapping[pFunction] = CallSiteCDependenceMapping;
}

void CrossIterationRedundancy::BottomUpDependenceAnalysis(Function * pFunction)
{
	set<Instruction *> setCallSite;
	GetAllCallSite(pFunction, setCallSite);

	vector<Instruction *> vecWorkList;
	set<Instruction *>::iterator itSetBegin = setCallSite.begin();
	set<Instruction *>::iterator itSetEnd = setCallSite.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		CallSite cs(*itSetBegin);
		Function * pCalledFunction = cs.getCalledFunction();

		if(this->CallerCalleeMapping.find(pCalledFunction) != this->CallerCalleeMapping.end() )
		{
			set<ReturnInst *> setRetInst;
			GetAllReturnInst(pCalledFunction, setRetInst);

			set<ReturnInst *>::iterator itSetRetBegin = setRetInst.begin();
			set<ReturnInst *>::iterator itSetRetEnd = setRetInst.end();

			for(; itSetRetBegin != itSetRetEnd; itSetRetBegin ++ )
			{
				set<Value *>::iterator itSetDepBegin = this->FuncValueDependenceMappingMapping[pCalledFunction][*itSetRetBegin].begin();
				set<Value *>::iterator itSetDepEnd = this->FuncValueDependenceMappingMapping[pCalledFunction][*itSetRetBegin].end();

				for(; itSetDepBegin != itSetDepEnd; itSetDepBegin ++ )
				{
					if(Argument * pArg = dyn_cast<Argument>(*itSetDepBegin))
					{
						unsigned uIndex = pArg->getArgNo();
						Value * pRealPara = (*itSetBegin)->getOperand(uIndex);

						if(Instruction * pInst = dyn_cast<Instruction>(pRealPara))
						{
							set<Value *>::iterator itParaDepBegin = this->FuncValueDependenceMappingMapping[pFunction][pInst].begin();
							set<Value *>::iterator itParaDepEnd   = this->FuncValueDependenceMappingMapping[pFunction][pInst].end();

							for(; itParaDepBegin != itParaDepEnd; itParaDepBegin ++)
							{
								this->FuncValueDependenceMappingMapping[pFunction][*itSetBegin].insert(*itParaDepBegin);
							}
						}
						else
						{
							this->FuncValueDependenceMappingMapping[pFunction][*itSetBegin].insert(pRealPara);
						}

					}
					else
					{	
						this->FuncValueDependenceMappingMapping[pFunction][*itSetBegin].insert(*itSetDepBegin);
					}
				}
			}

			set<Instruction *>::iterator itSetInstBegin = this->FuncDependenceValueMappingMapping[pFunction][*itSetBegin].begin();
			set<Instruction *>::iterator itSetInstEnd   = this->FuncDependenceValueMappingMapping[pFunction][*itSetBegin].end();

			for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
			{
				vecWorkList.push_back(*itSetInstBegin);
			}
		}
	}

	while(vecWorkList.size() > 0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		set<Value *> setNewDependentValue;

		set<Value *>::iterator itSetBegin = this->FuncValueDependenceMappingMapping[pFunction][pCurrent].begin();
		set<Value *>::iterator itSetEnd = this->FuncValueDependenceMappingMapping[pFunction][pCurrent].end();

		for(; itSetBegin != itSetEnd; itSetBegin ++ )
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetBegin))
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction) )
				{
					if(this->LoadTypeMapping[pLoad] != MO_LOCAL)
					{
						setNewDependentValue.insert(pLoad);
						continue;
					}
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInstruction) )
				{
					if(this->MemTypeMapping[pMem].first != MO_LOCAL)
					{
						setNewDependentValue.insert(pMem);
						continue;
					}
				}

				if(this->FuncValueDependenceMappingMapping[pFunction].find(pInstruction) == this->FuncValueDependenceMappingMapping[pFunction].end())
				{
					setNewDependentValue.insert(pInstruction);
					continue;
				}

				set<Value *>::iterator itSetTmpBegin = this->FuncValueDependenceMappingMapping[pFunction][pInstruction].begin();
				set<Value *>::iterator itSetTmpEnd = this->FuncValueDependenceMappingMapping[pFunction][pInstruction].end();

				for(; itSetTmpBegin != itSetTmpEnd; itSetTmpBegin ++ )
				{
					if(Instruction * pDependentInst = dyn_cast<Instruction>(*itSetTmpBegin))
					{
						if(this->FuncInstProcessedInstMappingMapping[pFunction][pCurrent].find(pDependentInst) != 
							this->FuncInstProcessedInstMappingMapping[pFunction][pCurrent].end() )
						{
							continue;
						}

						this->FuncInstProcessedInstMappingMapping[pFunction][pCurrent].insert(pDependentInst);
					}

					setNewDependentValue.insert(*itSetTmpBegin);
				}

			}
			else
			{
				setNewDependentValue.insert(*itSetBegin);
			}
		}

		if(!CmpValueSet(setNewDependentValue, this->FuncValueDependenceMappingMapping[pFunction][pCurrent]))
		{
			this->FuncValueDependenceMappingMapping[pFunction][pCurrent] = setNewDependentValue;
			
			if(pCurrent->getParent()->getParent() != pFunction)
			{
				continue;
			}

			if(LoadInst * pLoad = dyn_cast<LoadInst>(pCurrent))
			{
				if(this->LoadTypeMapping[pLoad] != MO_LOCAL)
				{
					continue;
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pCurrent))
			{
				if(this->MemTypeMapping[pMem].first != MO_LOCAL)
				{
					continue;
				}
			}

			set<Instruction *>::iterator itSetInstBegin = this->FuncDependenceValueMappingMapping[pFunction][pCurrent].begin();
			set<Instruction *>::iterator itSetInstEnd =   this->FuncDependenceValueMappingMapping[pFunction][pCurrent].end();

			for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
			{
				vecWorkList.push_back(*itSetInstBegin);
			}
		}
	}
}


void CrossIterationRedundancy::TopDownDependenceAnalysis(Function * pFunction)
{
	set<Instruction *>::iterator itInstBegin;
	set<Instruction *>::iterator itInstEnd;
	//add real-formal parameter
	vector< set<Value *> > vecArgDValues;
	for(size_t i = 0; i < pFunction->arg_size(); i ++ )
	{
		set<Value *> setArgValues;
		vecArgDValues.push_back(setArgValues);
	}

	itInstBegin = this->CalleeCallSiteMapping[pFunction].begin();
	itInstEnd   = this->CalleeCallSiteMapping[pFunction].end();

	for(; itInstBegin != itInstEnd; itInstBegin ++)
	{
		Function * pCaller = (*itInstBegin)->getParent()->getParent();

		for(size_t i = 0; i < pFunction->arg_size(); i ++ )
		{
			Value * pOperand = (*itInstBegin)->getOperand(i);

			if(Instruction * pInstruction = dyn_cast<Instruction>(pOperand))
			{
				Function * pContainedFunction = pInstruction->getParent()->getParent();

				if(pContainedFunction != pCaller)
				{
					vecArgDValues[i].insert(pInstruction);
				}
				else
				{
					vecArgDValues[i].insert(this->FuncValueDependenceMappingMapping[pCaller][pInstruction].begin(), this->FuncValueDependenceMappingMapping[pCaller][pInstruction].end());
				}
			}
			else
			{
				vecArgDValues[i].insert(pOperand);
			}
		}
	}

	size_t index = 0;
	for(Function::arg_iterator argBegin = pFunction->arg_begin(); argBegin != pFunction->arg_end(); argBegin ++ )
	{
		FuncArgDependenceMappingMapping[pFunction][argBegin] = vecArgDValues[index];
		index ++;
	}

	//add control flow dependence
	set<Value *> setCDValues;
	itInstBegin = this->CalleeCallSiteMapping[pFunction].begin();
	itInstEnd   = this->CalleeCallSiteMapping[pFunction].end();

	for(; itInstBegin != itInstEnd; itInstBegin ++)
	{
		Function * pCaller = (*itInstBegin)->getParent()->getParent();

		set<Value *>::iterator itCDValBegin = this->FuncCallSiteCDependenceMappingMapping[pCaller][*itInstBegin].begin();
		set<Value *>::iterator itCDValEnd   = this->FuncCallSiteCDependenceMappingMapping[pCaller][*itInstBegin].end();

		for(; itCDValBegin != itCDValEnd; itCDValBegin ++ )
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(*itCDValBegin))
			{
				Function * pContainedFunction = pInstruction->getParent()->getParent();
				if(pContainedFunction != pCaller)
				{
					setCDValues.insert(pInstruction);
				}
				else
				{
					setCDValues.insert(this->FuncValueDependenceMappingMapping[pCaller][pInstruction].begin(), this->FuncValueDependenceMappingMapping[pCaller][pInstruction].end());
				}
			}
			else 
			{
				setCDValues.insert(*itCDValBegin);
			}
		}
	}

	

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			set<Value *> newValueSet;

			set<Value *>::iterator itValSetBegin = this->FuncValueDependenceMappingMapping[pFunction][II].begin();
			set<Value *>::iterator itValSetEnd   = this->FuncValueDependenceMappingMapping[pFunction][II].end();

			for(; itValSetBegin != itValSetEnd; itValSetBegin ++ )
			{
				if(Argument * pArg = dyn_cast<Argument>(*itValSetBegin))
				{
					if(pArg->getParent() == pFunction)
					{
						newValueSet.insert(vecArgDValues[pArg->getArgNo()].begin(), vecArgDValues[pArg->getArgNo()].end());
					}
				}
				else
				{
					newValueSet.insert(*itValSetBegin);
				}
			}

			newValueSet.insert(setCDValues.begin(), setCDValues.end());

			this->FuncValueDependenceMappingMapping[pFunction][II] = newValueSet;
		}
	}
}

/*
void CrossIterationRedundancy::TopDownDependenceAnalysis()
{	
	vector<Argument *> vecWorkList;
	vector<Function *> vecFuncWorkList;

	map<Argument *, set<Value *> > ArgDependenceMapping;
	map<Argument *, set<Argument *> > ArgProcessedArg;
	map<Argument *, set<Argument *> > DependenceArgMapping;

	map<Function *, set<Function *> >::iterator itFuncMapBegin = this->CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itFuncMapEnd   = this->CallerCalleeMapping.end();

	map<Function *, set<Value *> > FuncCDependenceMapping;

	for(; itFuncMapBegin != itFuncMapEnd; itFuncMapBegin ++ )
	{
		Function * pCurrent = itFuncMapBegin->first;
		vecFuncWorkList.push_back(pCurrent);

		set<Value *> setControlDep;
		FuncCDependenceMapping[pCurrent] = setControlDep;

		for(Function::arg_iterator argBegin = pCurrent->arg_begin(); argBegin != pCurrent->arg_end(); argBegin ++ )
		{
			set<Argument *> setArg;
			DependenceArgMapping[argBegin] = setArg;

			set<Argument *> setProcessedArg;
			setProcessedArg.insert(argBegin);
			ArgProcessedArg[argBegin] = setProcessedArg;
			
			set<Value *> setValue;
			ArgDependenceMapping[argBegin] = setValue;
			
			vecWorkList.push_back(argBegin);
		}

	}

	itFuncMapBegin = this->CallerCalleeMapping.begin();
	for(; itFuncMapBegin != itFuncMapEnd; itFuncMapBegin ++ )
	{
		Function * pCurrent = itFuncMapBegin->first;
		
		set<Instruction *>::iterator itCallSiteBegin = this->CallerCallSiteMapping[pCurrent].begin();
		set<Instruction *>::iterator itCallSiteEnd   = this->CallerCallSiteMapping[pCurrent].end();

		for(; itCallSiteBegin != itCallSiteEnd; itCallSiteBegin ++ )
		{
			CallSite cs(*itCallSiteBegin);
			Function * pCalled = cs.getCalledFunction();

			if(this->CallerCalleeMapping.find(pCalled) == this->CallerCalleeMapping.end() )
			{
				continue;
			}

			unsigned uIndex = 0;
			for(Function::arg_iterator argBegin = pCalled->arg_begin(); argBegin != pCalled->arg_end(); argBegin ++, uIndex ++ )
			{
				Value * pValue = (*itCallSiteBegin)->getOperand(uIndex);

				if(Instruction * pInst = dyn_cast<Instruction>(pValue))
				{
					if(LoadInst * pLoad = dyn_cast<LoadInst>(pInst))
					{
						if(this->LoadTypeMapping[pLoad] != MO_LOCAL)
						{
							ArgDependenceMapping[argBegin].insert(pLoad);
							continue;
						}
					}
					else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInst))
					{
						if(this->MemTypeMapping[pMem].first != MO_LOCAL)
						{
							ArgDependenceMapping[argBegin].insert(pMem);
							continue;
						}
					}

					Function * pParent = pInst->getParent()->getParent();
					set<Value *>::iterator itSetValueBegin = this->FuncValueDependenceMappingMapping[pParent][pInst].begin();
					set<Value *>::iterator itSetValueEnd = this->FuncValueDependenceMappingMapping[pParent][pInst].end();

					for(; itSetValueBegin != itSetValueEnd; itSetValueBegin ++ )
					{
						if(Argument * pArg = dyn_cast<Argument>(*itSetValueBegin))
						{
							if(ArgProcessedArg[argBegin].find(pArg) != ArgProcessedArg[argBegin].end() )
							{
								continue;
							}

							DependenceArgMapping[pArg].insert(argBegin);
							ArgProcessedArg[argBegin].insert(pArg);
						}

						ArgDependenceMapping[argBegin].insert(*itSetValueBegin);
					}
				}
				else if(Argument * pArg = dyn_cast<Argument>(pValue))
				{
					if(ArgProcessedArg[argBegin].find(pArg) != ArgProcessedArg[argBegin].end() )
					{
						continue;
					}

					DependenceArgMapping[pArg].insert(argBegin);
					ArgDependenceMapping[argBegin].insert(pArg);
					ArgProcessedArg[argBegin].insert(pArg);
				}
				else
				{
					ArgDependenceMapping[argBegin].insert(pValue);
				}
			}
		}
	}



	while(vecWorkList.size() > 0)
	{
		Argument * pCurrentArg = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		set<Value *> newDependence;
		set<Value *>::iterator itSetValueBegin = ArgDependenceMapping[pCurrentArg].begin();
		set<Value *>::iterator itSetValueEnd   = ArgDependenceMapping[pCurrentArg].end();

		for(; itSetValueBegin != itSetValueEnd; itSetValueBegin ++ )
		{
			if(Argument * pArg = dyn_cast<Argument>(*itSetValueBegin))
			{
				if(ArgDependenceMapping[pArg].size() == 0 )
				{
					newDependence.insert(pArg);
					continue;
				}

				set<Value *>::iterator itArgDepBegin = ArgDependenceMapping[pArg].begin();
				set<Value *>::iterator itArgDepEnd   = ArgDependenceMapping[pArg].end();

				for(; itArgDepBegin != itArgDepEnd; itArgDepBegin ++ )
				{
					if(Argument * pArgTmp = dyn_cast<Argument>(*itArgDepBegin))
					{
						if(ArgProcessedArg[pCurrentArg].find(pArgTmp) != ArgProcessedArg[pCurrentArg].end())
						{
							continue;
						}

						ArgProcessedArg[pCurrentArg].insert(pArgTmp);
						
					}

					newDependence.insert(*itArgDepBegin);
				}
			}
			else
			{
				newDependence.insert(*itSetValueBegin);
			}
		}

		if(!CmpValueSet(newDependence, ArgDependenceMapping[pCurrentArg]))
		{
			ArgDependenceMapping[pCurrentArg] = newDependence;

			set<Argument *>::iterator itSetArgBegin = DependenceArgMapping[pCurrentArg].begin();
			set<Argument *>::iterator itSetArgEnd = DependenceArgMapping[pCurrentArg].end();

			for(; itSetArgBegin != itSetArgEnd; itSetArgBegin ++ )
			{
				vecWorkList.push_back(*itSetArgBegin);
			}
		}
	}


	map<Function *, set<Instruction *> >::iterator itMapCallerBegin = this->CallerCallSiteMapping.begin();
	map<Function *, set<Instruction *> >::iterator itMapCallerEnd   = this->CallerCallSiteMapping.end();

	for(; itMapCallerBegin != itMapCallerEnd; itMapCallerBegin ++)
	{
		set<Instruction *>::iterator itSetInstBegin = itMapCallerBegin->second.begin();
		set<Instruction *>::iterator itSetInstEnd   = itMapCallerBegin->second.end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
		{
			CallSite cs(*itSetInstBegin);
			Function * pCalled = cs.getCalledFunction();
		
			if(this->CallerCallSiteMapping.find(pCalled) != this->CallerCallSiteMapping.end() )
			{
				if(this->CalleeCallSiteMapping.find(pCalled) == this->CalleeCallSiteMapping.end())
				{
					set<Instruction *> setCallSites;
					this->CalleeCallSiteMapping[pCalled] = setCallSites;
				}

				this->CalleeCallSiteMapping[pCalled].insert(*itSetInstBegin);
			}
		}
	}


	while(vecFuncWorkList.size()>0)
	{
		Function * pCurrent = vecFuncWorkList[vecFuncWorkList.size()-1];
		vecFuncWorkList.pop_back();

		if(this->CallerCalleeMapping.find(pCurrent) == this->CallerCalleeMapping.end())
		{
			continue;
		}

		set<Value *> setControlDep;
		set<Instruction *>::iterator itSetInstBegin = this->CalleeCallSiteMapping[pCurrent].begin();
		set<Instruction *>::iterator itSetInstEnd   = this->CalleeCallSiteMapping[pCurrent].end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
		{
			Function * pParent = (*itSetInstBegin)->getParent()->getParent();
			setControlDep.insert(FuncCDependenceMapping[pParent].begin(), FuncCDependenceMapping[pParent].end());
			setControlDep.insert(FuncCallSiteCDependenceMappingMapping[pParent][*itSetInstBegin].begin(), FuncCallSiteCDependenceMappingMapping[pParent][*itSetInstBegin].end());
		}

		if(!CmpValueSet(setControlDep, FuncCDependenceMapping[pCurrent]))
		{
			FuncCDependenceMapping[pCurrent] = setControlDep;
			set<Function *>::iterator itFuncBegin = this->CallerCalleeMapping[pCurrent].begin();
			set<Function *>::iterator itFuncEnd   = this->CallerCalleeMapping[pCurrent].end();
			for(; itFuncBegin != itFuncEnd; itFuncBegin ++)
			{
				vecFuncWorkList.push_back(*itFuncBegin);
			}
		}
	}



	map<Argument *, set<Value *> >::iterator itArgMapBegin = ArgDependenceMapping.begin();
	map<Argument *, set<Value *> >::iterator itArgMapEnd   = ArgDependenceMapping.end();

	char pPath[1000];

	for(; itArgMapBegin != itArgMapEnd; itArgMapBegin ++)
	{
		itArgMapBegin->first->dump();
		errs() << itArgMapBegin->first->getParent()->getName() << "\n";

		set<Value *>::iterator itSetBegin = itArgMapBegin->second.begin();
		set<Value *>::iterator itSetEnd = itArgMapBegin->second.end();

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

		errs() << "************************************\n" ;
	}

}
*/




/*
void CrossIterationRedundancy::TopDownDependenceAnalysis()
{
	map<Function *, set<Function *> >::iterator itMapBegin = CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itMapEnd   = CallerCalleeMapping.end();

	map<Function *, set<Value *> > FuncCDependenceMapping;
	map<Argument *, set<Value *> > ArgDependenceMapping;

	map<Argument *, set<Instruction *> > ArgInstMapping;
	vector<Function *> vecWorkList;

	for(; itMapBegin != itMapEnd; itMapBegin++ )
	{
		Function * pCurrent = itMapBegin->first;
		
		set<Value *> setControlDep;
		FuncCDependenceMapping[pCurrent] = setControlDep;

		for(Function::arg_iterator argBegin = pCurrent->arg_begin(); argBegin != pCurrent->arg_end(); argBegin ++ )
		{
			set<Instruction *> setInst;
			ArgInstMapping[argBegin] = setInst;

			set<Value *> setArgDep;
			ArgDependenceMapping[argBegin] = setArgDep;

			map<Instruction *, set<Value *> >::iterator itMapInstBegin = this->FuncValueDependenceMappingMapping[pCurrent].begin();
			map<Instruction *, set<Value *> >::iterator itMapInstEnd = this->FuncValueDependenceMappingMapping[pCurrent].end();

			for(; itMapInstBegin != itMapInstEnd; itMapInstBegin ++)
			{
				if(itMapInstBegin->second.find(argBegin) != itMapInstBegin->second.end())
				{
					ArgInstMapping[argBegin].insert(itMapInstBegin->first);
				}
			}
		}

		vecWorkList.push_back(pCurrent);
	}

	while(vecWorkList.size() > 0)
	{
		Function * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		map<Instruction *, set<Value *> >::iterator itInstMapBegin = this->FuncCallSiteCDependenceMappingMapping[pCurrent].begin();
		map<Instruction *, set<Value *> >::iterator itInstMapEnd = this->FuncCallSiteCDependenceMappingMapping[pCurrent].end();

		for(; itInstMapBegin != itInstMapEnd; itInstMapBegin ++)
		{
			CallSite cs(itInstMapBegin->first);
			Function * pCalledFunction = cs.getCalledFunction();

			if(this->CallerCalleeMapping.find(pCalledFunction) == this->CallerCalleeMapping.end() )
			{
				continue;
			}


			set<Value *> setNewControlDep;
			setNewControlDep.insert(FuncCDependenceMapping[pCurrent].begin(), FuncCDependenceMapping[pCurrent].end());

			set<Value *>::iterator itSetValueBegin = itInstMapBegin->second.begin();
			set<Value *>::iterator itSetValueEnd = itInstMapBegin->second.end();

			for(; itSetValueBegin != itSetValueEnd; itSetValueBegin ++)
			{
				if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetValueBegin) )
				{
					set<Value *>::iterator itInstDepBegin = this->FuncValueDependenceMappingMapping[pInstruction->getParent()->getParent()][pInstruction].begin();
					set<Value *>::iterator itInstDepEnd   = this->FuncValueDependenceMappingMapping[pInstruction->getParent()->getParent()][pInstruction].end();

					for(; itInstDepBegin != itInstDepEnd; itInstDepBegin ++ )
					{
						if(Argument * pArg = dyn_cast<Argument>(*itInstDepBegin))
						{
							setNewControlDep.insert(ArgDependenceMapping[pArg].begin(), ArgDependenceMapping.end() );
						}
						else
						{
							setNewControlDep.insert(*itInstMapBegin);
						}
					}
				}
				else if(Argument * pArg = dyn_cast<Argument>(*itSetValueBegin))
				{
					setNewControlDep.insert(ArgDependenceMapping[pArg].begin(), ArgDependenceMapping[pArg].end());
				}
				else
				{
					setNewControlDep.insert(*itSetValueBegin);
				}
			}

		}

	}
}
*/

void CrossIterationRedundancy::DependenceAnalysis(Function * pFunction)
{
	set<ReturnInst *> setRetInst;
	set<Instruction *> setCallSite;
	set<StoreInst *> setStore;
	set<MemIntrinsic *> setMemIntrics;

	GetAllReturnInst(pFunction, setRetInst);
	CollectSideEffectInst(setCallSite, setStore, setMemIntrics);
	
	errs() << "Return: "       << setRetInst.size() << "\n";
	errs() << "Store:"         << setStore.size() << "\n";
	errs() << "MemIntrinsic: " << setMemIntrics.size() << "\n";
	errs() << "Library Call Sites: " << setCallSite.size() << "\n";

	map<Function *, set<Function *> >::iterator itCallerMapBegin = this->CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd   = this->CallerCalleeMapping.end();

	set<Function *> setProcessedFunc;
	map<Function *, set<Function * > > CallGraphMapping;

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin ++ )
	{
		Function * pCurrentFunction = itCallerMapBegin->first;
		IntraProcedureDependenceAnalysis(pCurrentFunction);
		CallGraphMapping[itCallerMapBegin->first] = itCallerMapBegin->second;
	}

	//bottom-up
	while(setProcessedFunc.size() < CallGraphMapping.size())
	{
		//update setProcessedFunc
		itCallerMapBegin = CallGraphMapping.begin();
		itCallerMapEnd = CallGraphMapping.end();

		for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin ++)
		{
			if(itCallerMapBegin->second.size() == 0 )
			{
				setProcessedFunc.insert(itCallerMapBegin->first);
			}
		}

		//update CallGraphMapping
		//pick up to be processed
		vector<Function *> vecToDo;
		itCallerMapBegin = CallGraphMapping.begin();
		for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin++)
		{
			if(itCallerMapBegin->second.size() == 0 )
			{
				continue;
			}

			set<Function *> newFuncSet;
			set<Function *>::iterator itFuncSetBegin = itCallerMapBegin->second.begin();
			set<Function *>::iterator itFuncSetEnd = itCallerMapBegin->second.end();

			for(; itFuncSetBegin != itFuncSetEnd; itFuncSetBegin ++ )
			{
				if(setProcessedFunc.find(*itFuncSetBegin) == setProcessedFunc.end() && CallGraphMapping.find(*itFuncSetBegin) != CallGraphMapping.end() )
				{
					newFuncSet.insert(*itFuncSetBegin);
				}
			}

			if(newFuncSet.size() == 0)
			{
				vecToDo.push_back(itCallerMapBegin->first);
			}

			CallGraphMapping[itCallerMapBegin->first] = newFuncSet;
		}

		vector<Function *>::iterator itVecBegin = vecToDo.begin();
		vector<Function *>::iterator itVecEnd   = vecToDo.end();


		//do bottom-up
		for(; itVecBegin != itVecEnd; itVecBegin ++ )
		{
			BottomUpDependenceAnalysis(*itVecBegin);
		}	
	}


	map<Function *, set<Function *> >  CalleeCallerGraph = this->CalleeCallerMapping;
	setProcessedFunc.clear();

	while(setProcessedFunc.size() < CalleeCallerGraph.size())
	{
		map<Function *, set<Function *> >::iterator itCalleeCallerBegin = CalleeCallerGraph.begin();
		map<Function *, set<Function *> >::iterator itCalleeCallerEnd   = CalleeCallerGraph.end();

		for(; itCalleeCallerBegin != itCalleeCallerEnd; itCalleeCallerBegin ++)
		{
			if(itCalleeCallerBegin->second.size() == 0 )
			{
				setProcessedFunc.insert(itCalleeCallerBegin->first);
			}
		}

		vector<Function *> vecToDo;
		itCalleeCallerBegin = CalleeCallerGraph.begin();

		for(; itCalleeCallerBegin != itCalleeCallerEnd; itCalleeCallerBegin ++ )
		{
			if(itCalleeCallerBegin->second.size() == 0 )
			{
				continue;
			}

			set<Function *> setNewCaller;

			set<Function *>::iterator itSetBegin = itCalleeCallerBegin->second.begin();
			set<Function *>::iterator itSetEnd   = itCalleeCallerBegin->second.end();

			for(; itSetBegin != itSetEnd; itSetBegin ++)
			{
				if(setProcessedFunc.find(*itSetBegin) == setProcessedFunc.end() && CalleeCallerGraph.find(*itSetBegin) != CalleeCallerGraph.end() )
				{
					setNewCaller.insert(*itSetBegin);
				}
			}

			if(setNewCaller.size() == 0 )
			{
				vecToDo.push_back(itCalleeCallerBegin->first);
			}

			CalleeCallerGraph[itCalleeCallerBegin->first] = setNewCaller;
		}

		vector<Function *>::iterator itVecBegin = vecToDo.begin();
		vector<Function *>::iterator itVecEnd   = vecToDo.end();

		for(; itVecBegin != itVecEnd; itVecBegin ++)
		{
			TopDownDependenceAnalysis(*itVecBegin);
		}
	}





	

	//top-down

	set<StoreInst *>::iterator itSetStoreBegin = setStore.begin();
	set<StoreInst *>::iterator itSetStoreEnd   = setStore.end();

	for(; itSetStoreBegin != itSetStoreEnd; itSetStoreBegin ++)
	{
		Function * pCurrentFunction = (*itSetStoreBegin)->getParent()->getParent();
		PrintIntraDependence(*itSetStoreBegin, this->FuncValueDependenceMappingMapping[pCurrentFunction][*itSetStoreBegin]);
	}

	

}

bool CrossIterationRedundancy::runOnModule(Module& M)
{
	Function * pFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);
	
	if(pFunction == NULL)
	{
		errs() << "Cannot find the input Function\n" ;
		return false;
	}

	this->pDL = &getAnalysis<DataLayout>();

	//Initialization
	InitializePureFunctionSet();
	InitializeMemoryAllocFunctionSet();

	AnalyzeMemReadInst(pFunction);
	int iLocal = CountLocalLoad();


	if(iLocal > 0)
	{
		this->pSFReach = &getAnalysis<StructFieldReach>();
		this->pSFReach->visit(pFunction);
		this->LoadDependentInstMapping = this->pSFReach->LoadDependentInstMapping;
		this->MemInstDependentInstMapping = this->pSFReach->MemInstDependentInstMapping;
	}

	DependenceAnalysis(pFunction);

	return false;
}

