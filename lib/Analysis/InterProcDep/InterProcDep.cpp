
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/DebugInfo.h"

#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/SFReach/SFReach.h"
#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "llvm-Commons/Invariant/InvariantAnalysis.h"
#include "llvm-Commons/CFG/CFGUtility.h"
#include "llvm-Commons/Dependence/DependenceUtility.h"


#include "Analysis/InterProcDep/InterProcDep.h"

using namespace llvm;
using namespace llvm_Commons;


static RegisterPass<InterProcDep> X("inter-procedure-dep",
                                "Inter Procedure Dependence Analysis",
                                false,
                                true);


void AddIntraDependence(Instruction * pValue, Value * pDependence, set<Instruction *> & setProcessedInst, set<Value *> & setDependence, 
						map<Instruction *, set<Instruction *> > & DependenceValueMapping)
{
	if(Instruction * pInstruction = dyn_cast<Instruction>(pDependence))
	{
		if(setProcessedInst.find(pInstruction) != setProcessedInst.end() )
		{
			return;
		}

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

		DependenceValueMapping[pInstruction].insert(pValue);
		setProcessedInst.insert(pInstruction);
	}
	else if(Argument * pArg = dyn_cast<Argument>(pDependence))
	{
		if(setProcessedInst.find(pArg) != setProcessedInst.end() )
		{
			return;
		}

		DependenceValueMapping[pArg].insert(pValue);
		setProcessedInst.insert(pArg);
	}

	setDependence.insert(pDependence);
}


void DumpDependence(set<Value *>  & setDependence)
{
	char pPath[1000];
	set<Value *>::iterator itSetBegin = setDependence.begin();
	set<Value *>::iterator itSetEnd   = setDependence.end();

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
}


char InterProcDep::ID = 0;

InterProcDep::InterProcDep(): ModulePass(ID) {
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeAliasAnalysisAnalysisGroup(Registry);

}

void InterProcDep::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesCFG();
	AU.addRequired<DataLayout>();
	AU.addRequired<AliasAnalysis>();
	AU.addRequired<StructFieldReach>();
	AU.addRequired<PostDominatorTree>();
}

void InterProcDep::print(raw_ostream &O, const Module *M) const
{
	return;
}

bool InterProcDep::runOnModule(Module &M) 
{
	this->pDL = &getAnalysis<DataLayout>();
	this->pSFR = &getAnalysis<StructFieldReach>();

	this->pModule = &M;

	return false;
}


void InterProcDep::InitlizeStartFunctionSet(set<Function *> & StartingSet)
{
	this->StartFunctionSet = StartingSet;
}

void InterProcDep::IsRecursiveFunction(Function * pFunction, map<Function *, int> & FuncMarkMapping, vector<pair<Function *, Function *> > & vecBackEdge )
{
	if(FuncMarkMapping.find(pFunction) == FuncMarkMapping.end())
	{
		FuncMarkMapping[pFunction] = 0;

		for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				if(isa<DbgInfoIntrinsic>(II))
				{
					continue;
				}
				else if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					CallSite cs(II);
					Function * pCalled = cs.getCalledFunction();

					if(pCalled == NULL)
					{
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
					{
						continue;
					}

					if(FuncMarkMapping.find(pCalled) != FuncMarkMapping.end())
					{
						if(FuncMarkMapping[pCalled] == 0)
						{
							pair<Function *, Function *> BackEdge;
							BackEdge.first = pFunction;
							BackEdge.second = pCalled;

							vecBackEdge.push_back(BackEdge);
							continue;
						}
						else if(FuncMarkMapping[pCalled] == 1)
						{
							continue;
						}
					}
					else
					{
						IsRecursiveFunction(pCalled, FuncMarkMapping, vecBackEdge);
					}
				}
			}
		}

		FuncMarkMapping[pFunction] = 1;
	}
	else
	{
		assert(0);
	}
}

void InterProcDep::DetectRecursiveFunctionCall(set<Function *> & RecursiveCalls, set<Function *> & nonRecursiveCalls)
{
	set<Function *>::iterator itSetFuncBegin = this->StartFunctionSet.begin();
	set<Function *>::iterator itSetFuncEnd   = this->StartFunctionSet.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++)
	{
		map<Function *, int> FuncMarkMapping;
		vector<pair<Function *, Function *> > vecBackEdge;

		IsRecursiveFunction(*itSetFuncBegin, FuncMarkMapping, vecBackEdge);

		if(vecBackEdge.size() > 0)
		{
			RecursiveCalls.insert(*itSetFuncBegin);
		}
		else
		{
			nonRecursiveCalls.insert(*itSetFuncBegin);
		}
	}
}


void InterProcDep::BuildCallerCalleeMapping(Function * pFunction)
{
	map<Function *, set<Function *> > CallerCalleeMapping;
	map<Function *, set<Instruction *> > CallerCallSiteMapping;
	
	map<Function *, set<Function *> >    CalleeCallerMapping;
	map<Function *, set<Instruction *> > CalleeCallSiteMapping;

	set<Function *> setEmptyFuncSet;
	CalleeCallerMapping[pFunction] = setEmptyFuncSet;
	set<Instruction *> setEmptyCallSite;
	CalleeCallSiteMapping[pFunction] = setEmptyCallSite;

	vector<Function *> vecWorkList;
	vecWorkList.push_back(pFunction);

	while(vecWorkList.size() > 0)
	{
		Function * pCurrentFunction = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		set<Function *> setCalledFunction;
		CallerCalleeMapping[pCurrentFunction] = setCalledFunction;

		set<Instruction *> setCallSite;
		CallerCallSiteMapping[pCurrentFunction] = setCallSite;

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

					CallerCallSiteMapping[pCurrentFunction].insert(II);
					CallerCalleeMapping[pCurrentFunction].insert(pCalledFunction);

					if(pCalledFunction->isDeclaration())
					{
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalledFunction) != this->LibraryTypeMapping.end() )
					{
						continue;
					}

					CalleeCallerMapping[pCalledFunction].insert(pCurrentFunction);
					CalleeCallSiteMapping[pCalledFunction].insert(II);

					if(CallerCalleeMapping.find(pCalledFunction) == CallerCalleeMapping.end() )
					{
						vecWorkList.push_back(pCalledFunction);
					}
				}
			}
		}
	}
 
	this->StartCallerCalleeMappingMapping[pFunction] = CallerCalleeMapping;
	this->StartCallerCallSiteMappingMapping[pFunction] = CallerCallSiteMapping;
	this->StartCalleeCallerMappingMapping[pFunction] = CalleeCallerMapping;
	this->StartCalleeCallSiteMappingMapping[pFunction] = CalleeCallSiteMapping;
}

void InterProcDep::DumpCallerCalleeMapping(Function * pFunction)
{
	map<Function *, set<Function *> > CallerCalleeMapping = this->StartCallerCalleeMappingMapping[pFunction];
	map<Function *, set<Function *> > CalleeCallerMapping = this->StartCalleeCallerMappingMapping[pFunction];


	map<Function *, set<Function *> >::iterator itMapBegin  = CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itMapEnd    = CallerCalleeMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		errs() << itMapBegin->first->getName() << "-> ";

		set<Function *>::iterator itSetFuncBegin = itMapBegin->second.begin();
		set<Function *>::iterator itSetFuncEnd   = itMapBegin->second.end();

		for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
		{
			errs() << (*itSetFuncBegin)->getName() << " ";
		}
		errs() << "\n";
	}

	errs() << "\n\n";

	itMapBegin  = CalleeCallerMapping.begin();
	itMapEnd    = CalleeCallerMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		

		set<Function *>::iterator itSetFuncBegin = itMapBegin->second.begin();
		set<Function *>::iterator itSetFuncEnd   = itMapBegin->second.end();

		for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
		{
			errs() << (*itSetFuncBegin)->getName() << " ";
		}

		errs() << "-> " << itMapBegin->first->getName() ;
		errs() << "\n";
	}


	errs() << "\n\n";
}


void InterProcDep::AnalyzeMemReadInst(Function * pFunction)
{
	
	map<LoadInst *, MemoryObjectType> LoadTypeMapping;
	map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> > MemTypeMapping;

	BuildCallerCalleeMapping(pFunction);

	map<Function *, set<Function *> >::iterator itCallerMapBegin = this->StartCallerCalleeMappingMapping[pFunction].begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd = this->StartCallerCalleeMappingMapping[pFunction].end();

	itCallerMapBegin = this->StartCallerCalleeMappingMapping[pFunction].begin();

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin ++ )
	{
		Function * pCurrentFunction = itCallerMapBegin->first;

		for(Function::iterator BB = pCurrentFunction->begin(); BB != pCurrentFunction->end(); BB ++ )
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
				{
					Value * pPointer = pLoad->getPointerOperand();
					Value * pBase = GetUnderlyingObject(pPointer, this->pDL);

					if(BeLocalObject(pBase))
					{
						LoadTypeMapping[pLoad] = MO_LOCAL;
						continue;
					}

					if(BeInputArgument(pBase))
					{
						LoadTypeMapping[pLoad] = MO_INPUT;
						continue;
					}

					LoadTypeMapping[pLoad] = MO_OTHER;
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
					else
					{
						pairTmp.second = MO_OTHER;
					}

					MemTypeMapping[pMem] = pairTmp;					
				}
			}
		}
	}

	this->StartLoadTypeMappingMapping[pFunction] = LoadTypeMapping;
	this->StartMemTypeMappingMapping[pFunction]  = MemTypeMapping;	
}

int InterProcDep::CountLocalLoad(Function * pFunction, set<Function *> & setFunctions )
{
	int iLocal = 0;
	int iInput = 0;

	map<LoadInst *, MemoryObjectType>::iterator itMapLoadBegin = this->StartLoadTypeMappingMapping[pFunction].begin();
	map<LoadInst *, MemoryObjectType>::iterator itMapLoadEnd = this->StartLoadTypeMappingMapping[pFunction].end();

	for(; itMapLoadBegin != itMapLoadEnd; itMapLoadBegin ++)
	{
		if(itMapLoadBegin->second == MO_LOCAL)
		{
			setFunctions.insert(itMapLoadBegin->first->getParent()->getParent());
			iLocal ++;
		}
		else if(itMapLoadBegin->second == MO_INPUT)
		{
			iInput ++;
		}
	}

	map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> >::iterator itMapMemBegin = this->StartMemTypeMappingMapping[pFunction].begin();
	map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> >::iterator itMapMemEnd = this->StartMemTypeMappingMapping[pFunction].end();

	for(; itMapMemBegin != itMapMemEnd; itMapMemBegin ++)
	{
		if(itMapMemBegin->second.second == MO_LOCAL)
		{
			setFunctions.insert(itMapMemBegin->first->getParent()->getParent());
			iLocal++;
		}
		else if(itMapMemBegin->second.second == MO_INPUT)
		{
			iInput++;
		}
	}

	return iLocal;
}

void InterProcDep::NoneIntraProcedureDependenceAnalysis(Function * pFunction, Function * pStart)
{
	if(this->StartFuncValueDependenceMappingMappingMapping[pStart].find(pFunction) != this->StartFuncValueDependenceMappingMappingMapping[pStart].end() )
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
			if(isa<UnreachableInst>(BBtmp->getTerminator()))
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

			//add control dependence
			for(; itVecValueBegin != itVecValueEnd; itVecValueBegin++ )
			{
				AddIntraDependence(II, *itVecValueBegin, setProcessedInst, setDependence, DependenceValueMapping);
			}

			vector<Value *> vecOperator;
			GetDependingValue(II, vecOperator);

			if(isa<CallInst>(II) || isa<InvokeInst>(II) )
			{
				if(!isa<DbgInfoIntrinsic>(II))
				{
					CallSiteCDependenceMapping[II].insert(CFGDependentValue.begin(), CFGDependentValue.end());
				}

				CallSite cs(II);
				Function * pCalled = cs.getCalledFunction();

				if(this->StartCallerCalleeMappingMapping[pStart].find(pCalled) != this->StartCallerCalleeMappingMapping[pStart].end() )
				{
					mapInstProcessedInst[II] = setProcessedInst;
					ValueDependenceMapping[II] = setDependence;
					vecWorkList.push_back(II);
					continue;
				}
			}
			
			itVecValueBegin = vecOperator.begin();
			itVecValueEnd = vecOperator.end();

			if(isa<MemIntrinsic>(II) )
			{
				itVecValueBegin ++;
			}
			
			for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
			{
				AddIntraDependence(II, *itVecValueBegin, setProcessedInst, setDependence, DependenceValueMapping);
			}

			if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
			{
				if(this->StartLoadTypeMappingMapping[pStart][pLoad] == MO_LOCAL)
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
				if(this->StartMemTypeMappingMapping[pStart][pMem].second == MO_LOCAL)
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
					if(this->StartLoadTypeMappingMapping[pStart][pLoad] != MO_LOCAL)
					{
						setNewDependentValue.insert(pLoad);
						continue;
					}
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInstruction) )
				{
					if(this->StartMemTypeMappingMapping[pStart][pMem].second != MO_LOCAL)
					{
						setNewDependentValue.insert(pMem);
						continue;
					}
				}
				else if(isa<CallInst>(pInstruction) || isa<InvokeInst>(pInstruction))
				{
					CallSite cs(pInstruction);
					Function * pCalled = cs.getCalledFunction();

					if(pCalled == NULL)
					{
						setNewDependentValue.insert(pInstruction);
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalled) == this->LibraryTypeMapping.end() )
					{
						setNewDependentValue.insert(pInstruction);
						continue;
					}

					if(this->LibraryTypeMapping[pCalled] == LF_PURE || this->LibraryTypeMapping[pCalled] == LF_IO || this->LibraryTypeMapping[pCalled] == LF_OTHER)
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
				if(this->StartLoadTypeMappingMapping[pStart][pLoad] != MO_LOCAL)
				{
					continue;
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pCurrent))
			{
				if(this->StartMemTypeMappingMapping[pStart][pMem].first != MO_LOCAL)
				{
					continue;
				}
			}
			else if(isa<CallInst>(pCurrent) || isa<InvokeInst>(pCurrent) )
			{
				CallSite cs(pCurrent);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				if(this->StartCallerCalleeMappingMapping[pStart].find(pCalled) != this->StartCallerCalleeMappingMapping[pStart].end() )
				{
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalled) == this->LibraryTypeMapping.end() || this->LibraryTypeMapping[pCalled] == LF_PURE 
					|| this->LibraryTypeMapping[pCalled] == LF_IO || this->LibraryTypeMapping[pCalled] == LF_OTHER)
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

	this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction] = ValueDependenceMapping;
	this->StartFuncDependenceValueMappingMappingMapping[pStart][pFunction] = DependenceValueMapping;
	this->StartFuncInstProcessedInstMappingMappingMapping[pStart][pFunction] = mapInstProcessedInst;
	this->StartFuncCallSiteCDependenceMappingMappingMapping[pStart][pFunction] = CallSiteCDependenceMapping;
}

void InterProcDep::CollectSideEffectInst(Function * pStart, set<Instruction *> & setCallSite, set<StoreInst *> & setStore, set<MemIntrinsic *> & setMemIntrics)
{
	map<Function *, set<Function *> >::iterator itCallerMapBegin = this->StartCallerCalleeMappingMapping[pStart].begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd = this->StartCallerCalleeMappingMapping[pStart].end();

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
						setCallSite.insert(II);
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalledFunction) != this->LibraryTypeMapping.end() )
					{
						if(this->LibraryTypeMapping[pCalledFunction] == LF_TRANSPARENT)
						{
							continue;
						}
						else if(this->LibraryTypeMapping[pCalledFunction] == LF_PURE)
						{
							continue;
						}

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

void InterProcDep::BottomUpDependenceAnalysis(Function * pFunction, Function * pStart)
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

		if(this->StartCallerCalleeMappingMapping[pStart].find(pCalledFunction) != this->StartCallerCalleeMappingMapping[pStart].end() )
		{
			set<ReturnInst *> setRetInst;
			GetAllReturnInst(pCalledFunction, setRetInst);

			set<ReturnInst *>::iterator itSetRetBegin = setRetInst.begin();
			set<ReturnInst *>::iterator itSetRetEnd = setRetInst.end();

			for(; itSetRetBegin != itSetRetEnd; itSetRetBegin ++ )
			{
				set<Value *>::iterator itSetDepBegin = this->StartFuncValueDependenceMappingMappingMapping[pStart][pCalledFunction][*itSetRetBegin].begin();
				set<Value *>::iterator itSetDepEnd = this->StartFuncValueDependenceMappingMappingMapping[pStart][pCalledFunction][*itSetRetBegin].end();

				for(; itSetDepBegin != itSetDepEnd; itSetDepBegin ++ )
				{
					if(Argument * pArg = dyn_cast<Argument>(*itSetDepBegin))
					{
						if(pArg->getParent() != pCalledFunction )
						{
							this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(*itSetDepBegin);
							continue;
						}

						unsigned uIndex = pArg->getArgNo();
						Value * pRealPara = (*itSetBegin)->getOperand(uIndex);

						if(Instruction * pInst = dyn_cast<Instruction>(pRealPara))
						{
							if(LoadInst * pLoad = dyn_cast<LoadInst>(pInst))
							{
								if(this->StartLoadTypeMappingMapping[pStart][pLoad] != MO_LOCAL)
								{
									this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(pLoad);
									continue;
								}
							}
							else if(isa<CallInst>(pInst) || isa<InvokeInst>(pInst))
							{
								CallSite cs(pInst);
								Function * pCalled = cs.getCalledFunction();

								if(pCalled == NULL)
								{
									this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(pInst);
									continue;
								}

								if(this->LibraryTypeMapping.find(pCalled) == this->LibraryTypeMapping.end() )
								{
									this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(pInst);
									continue;
								}

								if(this->LibraryTypeMapping[pCalled] == LF_PURE || this->LibraryTypeMapping[pCalled] == LF_IO || this->LibraryTypeMapping[pCalled] == LF_OTHER)
								{
									this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(pInst);
									continue;
								}

							}

							set<Value *>::iterator itParaDepBegin = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pInst].begin();
							set<Value *>::iterator itParaDepEnd   = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pInst].end();
							
							this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(itParaDepBegin, itParaDepEnd);
						}
						else
						{
							this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(pRealPara);
						}

					}
					else
					{	
						this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][*itSetBegin].insert(*itSetDepBegin);
					}
				}
			}

			vecWorkList.push_back(*itSetBegin);

			set<Instruction *>::iterator itSetInstBegin = this->StartFuncDependenceValueMappingMappingMapping[pStart][pFunction][*itSetBegin].begin();
			set<Instruction *>::iterator itSetInstEnd   = this->StartFuncDependenceValueMappingMappingMapping[pStart][pFunction][*itSetBegin].end();

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

		set<Value *>::iterator itSetBegin = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pCurrent].begin();
		set<Value *>::iterator itSetEnd = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pCurrent].end();

		for(; itSetBegin != itSetEnd; itSetBegin ++ )
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetBegin))
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction) )
				{
					if(this->StartLoadTypeMappingMapping[pStart][pLoad] != MO_LOCAL)
					{
						setNewDependentValue.insert(pLoad);
						continue;
					}
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInstruction) )
				{
					if(this->StartMemTypeMappingMapping[pStart][pMem].second != MO_LOCAL)
					{
						setNewDependentValue.insert(pMem);
						continue;
					}
				}
				else if(isa<CallInst>(pInstruction) || isa<InvokeInst>(pInstruction))
				{
					CallSite cs(pInstruction);
					Function * pCalled = cs.getCalledFunction();

					if(pCalled == NULL)
					{
						setNewDependentValue.insert(pInstruction);
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
					{
						if(this->LibraryTypeMapping[pCalled] == LF_PURE)
						{
							setNewDependentValue.insert(pInstruction);
							continue;
						}
						else if(this->LibraryTypeMapping[pCalled] == LF_IO)
						{
							setNewDependentValue.insert(pInstruction);
							continue;
						}
						else if(this->LibraryTypeMapping[pCalled] == LF_OTHER)
						{
							setNewDependentValue.insert(pInstruction);
							continue;
						}
					}
					else if(pCalled->isDeclaration() )
					{
						setNewDependentValue.insert(pInstruction);
						continue;
					}
				}

				if(this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction].find(pInstruction) == this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction].end())
				{
					setNewDependentValue.insert(pInstruction);
					continue;
				}

				set<Value *>::iterator itSetTmpBegin = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pInstruction].begin();
				set<Value *>::iterator itSetTmpEnd = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pInstruction].end();

				for(; itSetTmpBegin != itSetTmpEnd; itSetTmpBegin ++ )
				{
					if(Instruction * pDependentInst = dyn_cast<Instruction>(*itSetTmpBegin))
					{
						if(this->StartFuncInstProcessedInstMappingMappingMapping[pStart][pFunction][pCurrent].find(pDependentInst) != 
							this->StartFuncInstProcessedInstMappingMappingMapping[pStart][pFunction][pCurrent].end() )
						{
							continue;
						}

						this->StartFuncInstProcessedInstMappingMappingMapping[pStart][pFunction][pCurrent].insert(pDependentInst);
					}

					setNewDependentValue.insert(*itSetTmpBegin);
				}

			}
			else
			{
				setNewDependentValue.insert(*itSetBegin);
			}
		}

		if(!CmpValueSet(setNewDependentValue, this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pCurrent]))
		{
			this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][pCurrent] = setNewDependentValue;
			
			if(pCurrent->getParent()->getParent() != pFunction)
			{
				continue;
			}

			if(LoadInst * pLoad = dyn_cast<LoadInst>(pCurrent))
			{
				if(this->StartLoadTypeMappingMapping[pStart][pLoad] != MO_LOCAL)
				{
					continue;
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pCurrent))
			{
				if(this->StartMemTypeMappingMapping[pStart][pMem].first != MO_LOCAL)
				{
					continue;
				}
			}
			else if(isa<CallInst>(pCurrent) || isa<InvokeInst>(pCurrent))
			{
				CallSite cs(pCurrent);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
				{
					if(this->LibraryTypeMapping[pCalled] == LF_PURE)
					{
						continue;
					}
					else if(this->LibraryTypeMapping[pCalled] == LF_IO)
					{
						continue;
					}
					else if(this->LibraryTypeMapping[pCalled] == LF_OTHER)
					{
						continue;
					}
				}
				else if(pCalled->isDeclaration() )
				{
					continue;
				}
			}

			set<Instruction *>::iterator itSetInstBegin = this->StartFuncDependenceValueMappingMappingMapping[pStart][pFunction][pCurrent].begin();
			set<Instruction *>::iterator itSetInstEnd =   this->StartFuncDependenceValueMappingMappingMapping[pStart][pFunction][pCurrent].end();

			for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
			{
				vecWorkList.push_back(*itSetInstBegin);
			}
		}
	}

}

void InterProcDep::TopDownDependenceAnalysis(Function * pFunction, Function * pStart)
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
	
	if(pFunction == pStart)
	{
		size_t index = 0;
		for(Function::arg_iterator argBegin = pFunction->arg_begin(); argBegin != pFunction->arg_end(); argBegin ++ )
		{
			vecArgDValues[index].insert(argBegin);
			this->StartFuncArgDependenceMappingMappingMapping[pStart][pFunction][argBegin] = vecArgDValues[index];
			index ++;
		}
	}
	else
	{
		itInstBegin = this->StartCalleeCallSiteMappingMapping[pStart][pFunction].begin();
		itInstEnd   = this->StartCalleeCallSiteMappingMapping[pStart][pFunction].end();

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

						if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction) )
						{
							if(this->StartLoadTypeMappingMapping[pStart][pLoad] != MO_LOCAL)
							{
								vecArgDValues[i].insert(pLoad);
								continue;
							}
						}
						/*
						else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInstruction))
						{
							if(this->StartMemTypeMappingMapping[pStart][pMem].first != MO_LOCAL)
							{
								vecArgDValues[i].insert(pMem);
								continue;
							}
						}
						*/
						else if(isa<CallInst>(pInstruction) || isa<InvokeInst>(pInstruction))
						{
							CallSite cs(pInstruction);
							Function * pCalled = cs.getCalledFunction();

							if(pCalled == NULL)
							{
								vecArgDValues[i].insert(pInstruction);
								continue;
							}

							if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
							{
								if(this->LibraryTypeMapping[pCalled] == LF_PURE)
								{
									vecArgDValues[i].insert(pInstruction);
									continue;
								}
								else if(this->LibraryTypeMapping[pCalled] == LF_IO)
								{
									vecArgDValues[i].insert(pInstruction);
									continue;
								}
								else if(this->LibraryTypeMapping[pCalled] == LF_OTHER)
								{
									vecArgDValues[i].insert(pInstruction);
									continue;
								}
							}
							else if(pCalled->isDeclaration() )
							{
								vecArgDValues[i].insert(pInstruction);
								continue;
							}
						}

						vecArgDValues[i].insert(this->StartFuncValueDependenceMappingMappingMapping[pStart][pCaller][pInstruction].begin(), 
							this->StartFuncValueDependenceMappingMappingMapping[pStart][pCaller][pInstruction].end());
					}
				}
				else if(Argument * pArg = dyn_cast<Argument>(pOperand))
				{

					vecArgDValues[i].insert(this->StartFuncArgDependenceMappingMappingMapping[pStart][pArg->getParent()][pArg].begin(), 
						this->StartFuncArgDependenceMappingMappingMapping[pStart][pArg->getParent()][pArg].end());
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
			this->StartFuncArgDependenceMappingMappingMapping[pStart][pFunction][argBegin] = vecArgDValues[index];
			index ++;
		}
	}

	

	//add control flow dependence
	set<Value *> setCDValues;
	itInstBegin = this->StartCalleeCallSiteMappingMapping[pStart][pFunction].begin();
	itInstEnd   = this->StartCalleeCallSiteMappingMapping[pStart][pFunction].end();

	for(; itInstBegin != itInstEnd; itInstBegin ++)
	{
		Function * pCaller = (*itInstBegin)->getParent()->getParent();

		set<Value *>::iterator itCDValBegin = this->StartFuncCallSiteCDependenceMappingMappingMapping[pStart][pCaller][*itInstBegin].begin();
		set<Value *>::iterator itCDValEnd   = this->StartFuncCallSiteCDependenceMappingMappingMapping[pStart][pCaller][*itInstBegin].end();

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
					setCDValues.insert(this->StartFuncValueDependenceMappingMappingMapping[pStart][pCaller][pInstruction].begin(), 
						this->StartFuncValueDependenceMappingMappingMapping[pStart][pCaller][pInstruction].end());
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

		if(isa<UnreachableInst>(BB->getTerminator()))
		{
			continue;
		}


		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			set<Value *> newValueSet;

			set<Value *>::iterator itValSetBegin = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][II].begin();
			set<Value *>::iterator itValSetEnd   = this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][II].end();

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

			this->StartFuncValueDependenceMappingMappingMapping[pStart][pFunction][II] = newValueSet;
		}
	}
}


void InterProcDep::NoneRecursiveDependenceAnalysis(Function * pFunction )
{
	AnalyzeMemReadInst(pFunction);
	set<Function *> setLocalLoadFunctions;
	int iLocal = CountLocalLoad(pFunction, setLocalLoadFunctions);
	
	if(iLocal > 0)
	{

		this->pSFR->InitToDoSet(setLocalLoadFunctions);
		this->pSFR->runAnalysis();
		this->LoadDependentInstMapping = this->pSFR->LoadDependentInstMapping;
		this->MemInstDependentInstMapping = this->pSFR->MemInstDependentInstMapping;

		this->pSFR->LoadDependentInstMapping.clear();
		this->pSFR->MemInstDependentInstMapping.clear();

	}


	set<Instruction *> setCallSite;
	set<StoreInst *> setStore;
	set<MemIntrinsic *> setMemIntrics;

	CollectSideEffectInst(pFunction, setCallSite, setStore, setMemIntrics);

	//errs() << "In InterProcDep: " << setCallSite.size() << " " << setStore.size() << " " << setMemIntrics.size() << "\n";

	this->StartEffectStoreMapping[pFunction] = setStore;
	this->StartEffectMemMapping[pFunction] = setMemIntrics;
	this->StartLibraryCallMapping[pFunction] = setCallSite;


	map<Function *, set<Function *> >::iterator itCallerMapBegin = this->StartCallerCalleeMappingMapping[pFunction].begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd   = this->StartCallerCalleeMappingMapping[pFunction].end();

	map<Function *, set<Function * > > CallGraphMapping;

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin ++ )
	{
		Function * pCurrentFunction = itCallerMapBegin->first;
		NoneIntraProcedureDependenceAnalysis(pCurrentFunction, pFunction);
		CallGraphMapping[itCallerMapBegin->first] = itCallerMapBegin->second;
	}


	set<Function *> setProcessedFunc;

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
			BottomUpDependenceAnalysis(*itVecBegin, pFunction);
		}	
	}



	map<Function *, set<Function *> >  CalleeCallerGraph = this->StartCalleeCallerMappingMapping[pFunction];
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
			TopDownDependenceAnalysis(*itVecBegin, pFunction);
		}
	}
}


void InterProcDep::InfeasiblePathDependenceAnalysis(Function * pFunction)
{
	AnalyzeMemReadInst(pFunction);

	set<Function *> setLocalLoadFunctions;
	int iLocal = CountLocalLoad(pFunction, setLocalLoadFunctions);
	
	if(iLocal > 0)
	{
		this->pSFR->InitToDoSet(setLocalLoadFunctions);
		this->pSFR->runAnalysis();
		this->LoadDependentInstMapping = this->pSFR->LoadDependentInstMapping;
		this->MemInstDependentInstMapping = this->pSFR->MemInstDependentInstMapping;

		this->pSFR->LoadDependentInstMapping.clear();
		this->pSFR->MemInstDependentInstMapping.clear();
	}

	set<Instruction *> setCallSite;
	set<StoreInst *> setStore;
	set<MemIntrinsic *> setMemIntrics;

	CollectSideEffectInst(pFunction, setCallSite, setStore, setMemIntrics);

	this->StartEffectStoreMapping[pFunction] = setStore;
	this->StartEffectMemMapping[pFunction] = setMemIntrics;
	this->StartLibraryCallMapping[pFunction] = setCallSite;

	vector<Value *> vecWorkList;
	map<Value *, set<Value *> > mapProcessedInstruction;
	map<Function *, set<Value *> > FunctionControlDepMapping;

	map<Value *, set<Value *> > ValueDependenceMapping;
	map<Value *, set<Value *> > DependenceValueMapping;

	map<Function *, set<Function *> > CallerCalleeMapping = this->StartCallerCalleeMappingMapping[pFunction];

	map<Function *, set<Function *> >::iterator itCallerMapBegin = CallerCalleeMapping.begin();
	map<Function *, set<Function *> >::iterator itCallerMapEnd   = CallerCalleeMapping.end();

	map<LoadInst *, MemoryObjectType> LoadTypeMapping = this->StartLoadTypeMappingMapping[pFunction];
	map<MemTransferInst *, pair<MemoryObjectType, MemoryObjectType> > MemTypeMapping = this->StartMemTypeMappingMapping[pFunction];

	for(; itCallerMapBegin != itCallerMapEnd; itCallerMapBegin++ )
	{
		Function * pF = itCallerMapBegin->first;
		ControlDependenceGraphBase CDG;
		PostDominatorTree & PDT = getAnalysis<PostDominatorTree>(*pF);

		CDG.graphForFunction(*pF, PDT);

		for(Function::iterator BB = pF->begin(); BB != pF->end(); BB ++)
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			vector<Value *> CFGDependentValue;
			for(Function::iterator btmp = pF->begin(), betmp=pF->end(); btmp != betmp; btmp++ )
			{
				if(isa<UnreachableInst>(btmp->getTerminator()))
				{
					continue;
				}

				if(CDG.influences(btmp, BB))
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

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				vector<Value *>::iterator itVecValueBegin = CFGDependentValue.begin();
				vector<Value *>::iterator itVecValueEnd = CFGDependentValue.end();

				set<Value *> setDependence;
				set<Value *> setProcessedInst;

				setProcessedInst.insert(II);

				for(; itVecValueBegin != itVecValueEnd; itVecValueBegin++ )
				{
					AddInterDependence(II, *itVecValueBegin, setProcessedInst, setDependence, DependenceValueMapping);
				}

				if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					CallSite cs(II);
					Function * pCalled = cs.getCalledFunction();

					if(CallerCalleeMapping.find(pCalled) != CallerCalleeMapping.end() )
					{
						//add control dependence
						FunctionControlDepMapping[pCalled].insert(CFGDependentValue.begin(), CFGDependentValue.end());

						//add return dependence
						set<ReturnInst *> setRet;
						GetAllReturnInst(pCalled, setRet);

						set<ReturnInst *>::iterator itRetBegin = setRet.begin();
						set<ReturnInst *>::iterator itRetEnd = setRet.end();

						for(; itRetBegin != itRetEnd; itRetBegin++ )
						{
							AddInterDependence(II, *itRetBegin, setProcessedInst, setDependence, DependenceValueMapping);
						}

						//add formal-real dependence
						unsigned uIndex = 0;
						for(Function::arg_iterator argBegin = pCalled->arg_begin(); argBegin != pCalled->arg_end(); argBegin ++ )
						{
							AddInterDependence(argBegin, II->getOperand(uIndex), mapProcessedInstruction[argBegin], 
								ValueDependenceMapping[argBegin], DependenceValueMapping);

							vecWorkList.push_back(argBegin);
							uIndex ++;
						}
					}
					/*
					else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
					{
						if(MemTypeMapping[pMem].second == MO_LOCAL)
						{
							set<Instruction *>::iterator itSetInstBegin = this->MemInstDependentInstMapping[pMem].begin();
							set<Instruction *>::iterator itSetInstEnd = this->MemInstDependentInstMapping[pMem].end();

							for(; itSetInstBegin != itSetInstEnd ; itSetInstBegin ++)
							{
								AddInterDependence(II, *itSetInstBegin, setProcessedInst, setDependence, DependenceValueMapping);
							}
						}

					}
					*/
					else
					{
						vector<Value *> vecOperator;
						GetDependingValue(II, vecOperator);

						itVecValueBegin = vecOperator.begin();
						itVecValueEnd = vecOperator.end();

						if(isa<MemIntrinsic>(II) )
						{
							itVecValueBegin ++;
						}
						
						for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
						{
							AddInterDependence(II, *itVecValueBegin, setProcessedInst, setDependence, DependenceValueMapping);
						}
						
						if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
						{
							if(MemTypeMapping[pMem].second == MO_LOCAL)
							{
								set<Instruction *>::iterator itSetInstBegin = this->MemInstDependentInstMapping[pMem].begin();
								set<Instruction *>::iterator itSetInstEnd = this->MemInstDependentInstMapping[pMem].end();

								for(; itSetInstBegin != itSetInstEnd ; itSetInstBegin ++)
								{
									AddInterDependence(II, *itSetInstBegin, setProcessedInst, setDependence, DependenceValueMapping);
								}
							}

						}
					}
				}
				else
				{
					vector<Value *> vecOperator;
					GetDependingValue(II, vecOperator);

					itVecValueBegin = vecOperator.begin();
					itVecValueEnd = vecOperator.end();

					for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
					{
						AddInterDependence(II, *itVecValueBegin, setProcessedInst, setDependence, DependenceValueMapping);
					}

					if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
					{
						if(LoadTypeMapping[pLoad] == MO_LOCAL)
						{
							set<Instruction *>::iterator itSetInstBegin = this->LoadDependentInstMapping[pLoad].begin();
							set<Instruction *>::iterator itSetInstEnd = this->LoadDependentInstMapping[pLoad].end();

							for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
							{
								AddInterDependence(II, *itSetInstBegin, setProcessedInst, setDependence, DependenceValueMapping);
							}
						}
					}
				}

				mapProcessedInstruction[II] = setProcessedInst;
				ValueDependenceMapping[II] = setDependence;
				vecWorkList.push_back(II);
			}
		}
	}

	map<Function *, set<Value *> >::iterator itMapFuncDepBegin = FunctionControlDepMapping.begin();
	map<Function *, set<Value *> >::iterator itMapFuncDepEnd = FunctionControlDepMapping.end();

	for(; itMapFuncDepBegin != itMapFuncDepEnd; itMapFuncDepBegin ++)
	{
		Function * pCurrent = itMapFuncDepBegin->first;

		for(Function::iterator BB = pCurrent->begin(); BB != pCurrent->end(); BB ++ )
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				set<Value *>::iterator itVecValueBegin = itMapFuncDepBegin->second.begin();
				set<Value *>::iterator itVecValueEnd = itMapFuncDepBegin->second.end();

				for(; itVecValueBegin != itVecValueEnd; itVecValueBegin ++ )
				{
					AddInterDependence(II, *itVecValueBegin, mapProcessedInstruction[II], ValueDependenceMapping[II], DependenceValueMapping);
				}
			}
		}
	}

	while(vecWorkList.size() > 0)
	{
		Value * pCurrentValue = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		set<Value *> setNewDependentValue;
		set<Value *>::iterator itSetBegin = ValueDependenceMapping[pCurrentValue].begin();
		set<Value *>::iterator itSetEnd = ValueDependenceMapping[pCurrentValue].end();

		for(; itSetBegin != itSetEnd; itSetBegin ++ )
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(*itSetBegin) )
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction) )
				{
					if(LoadTypeMapping[pLoad] != MO_LOCAL)
					{
						setNewDependentValue.insert(pLoad);
						continue;
					}
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pInstruction))
				{
					if(MemTypeMapping[pMem].second != MO_LOCAL)
					{
						setNewDependentValue.insert(pMem);
						continue;
					}
				}
				else if(isa<CallInst>(pInstruction) || isa<InvokeInst>(pInstruction))
				{
					CallSite cs(pInstruction);
					Function * pCalled = cs.getCalledFunction();

					if(pCalled == NULL)
					{
						setNewDependentValue.insert(pInstruction);
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
					{
						if(this->LibraryTypeMapping[pCalled] == LF_PURE)
						{
							setNewDependentValue.insert(pInstruction);
							continue;
						}
						else if(this->LibraryTypeMapping[pCalled] == LF_IO)
						{
							setNewDependentValue.insert(pInstruction);
							continue;
						}
						else if(this->LibraryTypeMapping[pCalled] == LF_OTHER)
						{
							setNewDependentValue.insert(pInstruction);
							continue;
						}
						// for malloc and transpare function, we add all dependence to new set
					}
					else if(pCalled->isDeclaration())
					{
						setNewDependentValue.insert(pInstruction);
						continue;
					}
				}

				set<Value *>::iterator itSetTmpBegin = ValueDependenceMapping[pInstruction].begin();
				set<Value *>::iterator itSetTmpEnd = ValueDependenceMapping[pInstruction].end();

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
				if(ValueDependenceMapping.find(pArg) == ValueDependenceMapping.end() )
				{
					setNewDependentValue.insert(pArg);
					continue;
				} 

				set<Value *>::iterator itSetTmpBegin = ValueDependenceMapping[pArg].begin();
				set<Value *>::iterator itSetTmpEnd = ValueDependenceMapping[pArg].end();

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

				if(pArg->getParent() == pFunction)
				{
					setNewDependentValue.insert(pArg); //add for cases where function calls functions
				}

			}
			else
			{
				setNewDependentValue.insert(*itSetBegin);
			}
		}

		if(!CmpValueSet(setNewDependentValue, ValueDependenceMapping[pCurrentValue]))
		{
			ValueDependenceMapping[pCurrentValue] = setNewDependentValue;

			if(LoadInst * pLoad = dyn_cast<LoadInst>(pCurrentValue))
			{
				if(LoadTypeMapping[pLoad] != MO_LOCAL)
				{
					continue;
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(pCurrentValue) )
			{
				if(MemTypeMapping[pMem].first != MO_LOCAL)
				{
					continue;
				}
			}
			else if(isa<CallInst>(pCurrentValue) || isa<InvokeInst>(pCurrentValue))
			{
				CallSite cs(pCurrentValue);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
				{
					if(this->LibraryTypeMapping[pCalled] == LF_PURE)
					{
						continue;
					}
					else if(this->LibraryTypeMapping[pCalled] == LF_IO)
					{						
						continue;
					}
					else if(this->LibraryTypeMapping[pCalled] == LF_OTHER)
					{
						continue;
					}
				}
				else if(pCalled->isDeclaration() )
				{
					continue;
				}
			}

			set<Value *>::iterator itSetBegin = DependenceValueMapping[pCurrentValue].begin();
			set<Value *>::iterator itSetEnd = DependenceValueMapping[pCurrentValue].end();

			for(; itSetBegin != itSetEnd; itSetBegin ++)
			{
				vecWorkList.push_back(*itSetBegin);
			}
		}
	}

	map<Value *, set<Value *> >::iterator itValueDependenceBegin = ValueDependenceMapping.begin();
	map<Value *, set<Value *> >::iterator itValueDependenceEnd   = ValueDependenceMapping.end();

	for(; itValueDependenceBegin != itValueDependenceEnd; itValueDependenceBegin++)
	{
		if(Instruction * pInstruction = dyn_cast<Instruction>(itValueDependenceBegin->first) )
		{
			this->StartFuncValueDependenceMappingMappingMapping[pFunction][pInstruction->getParent()->getParent()][pInstruction] = itValueDependenceBegin->second;
		}
	}
}


void InterProcDep::InterProcDependenceAnalysis()
{
	set<Function *> RecursiveCalls;
	set<Function *> nonRecursiveCalls;

	DetectRecursiveFunctionCall(RecursiveCalls, nonRecursiveCalls);

	set<Function *>::iterator itSetFuncBegin = nonRecursiveCalls.begin();
	set<Function *>::iterator itSetFuncEnd   = nonRecursiveCalls.end();


	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
	{
		errs() << (*itSetFuncBegin)->getName() << "\n";
		NoneRecursiveDependenceAnalysis(*itSetFuncBegin);
	}

	itSetFuncBegin = RecursiveCalls.begin();
	itSetFuncEnd   = RecursiveCalls.end();


	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
	{
		errs() << (*itSetFuncBegin)->getName() << "\n";
		InfeasiblePathDependenceAnalysis(*itSetFuncBegin);
	}
}

