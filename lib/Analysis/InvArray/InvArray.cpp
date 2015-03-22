
#include <queue>
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/DebugInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "Analysis/InvArray/InvArray.h"
#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Array/Array.h"
#include "llvm-Commons/Config/Config.h"
#include "llvm-Commons/SEWrapper/SEWrapper.h"
#include "llvm-Commons/Invariant/InvariantAnalysis.h"
#include "llvm-Commons/CFG/CFGUtility.h"

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


static RegisterPass<InvArray> X("inv-array",
                                "array invariant analysis",
								false,
								true);



void PrintCS(vector<Instruction *> & vecCS)
{
	if(vecCS.size() == 0)
	{
		return;
	}

	unsigned i = vecCS.size() - 1;

	while(true)
	{
		PrintInstructionInfo(vecCS[i]);

		if(i==0)
		{
			break;
		}

		i --;
	}

}



char InvArray::ID = 0;

InvArray::InvArray(): ModulePass(ID) {
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeAliasAnalysisAnalysisGroup(Registry);
	initializeDominatorTreePass(Registry);
	initializePostDominatorTreePass(Registry);
	

}

void InvArray::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesCFG();
	AU.addRequired<AliasAnalysis>();
	AU.addRequired<DominatorTree>();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<ScalarEvolution>();
	AU.addRequired<DataLayout>();

}

void InvArray::print(raw_ostream &O, const Module *M) const
{
	return;
}

bool InvArray::SearchInnerLoop()
{
	this->pInnerFunction = SearchFunctionByName(*(this->pModule), strInnerFileName, strInnerFuncName, uInnerSrcLine);

	if(this->pInnerFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return false;
	}

	this->SE = &(getAnalysis<ScalarEvolution>(*(this->pInnerFunction)));
	LoopInfo * pInnerLI = &(getAnalysis<LoopInfo>(*(this->pInnerFunction)));

	Loop * pInnerLoop = NULL;

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

	this->pInnerHeader = pInnerLoop->getHeader();

	return true;
}

bool InvArray::SearchOuterLoop()
{
	this->pOuterFunction = SearchFunctionByName(*(this->pModule), strOuterFileName, strOuterFuncName, uOuterSrcLine);

	if(this->pOuterFunction == NULL)
	{
		errs() << "Cannot find the function containing the outer loop!\n";
		return false;
	}

	LoopInfo * pOuterLI = &(getAnalysis<LoopInfo>(*(this->pOuterFunction)));

	Loop * pOuterLoop = SearchLoopByLineNo(this->pOuterFunction, pOuterLI, uOuterSrcLine);

	if(pOuterLoop == NULL)
	{
		errs() << "Cannot find the outer loop!\n" ;
		return false;
	}

	this->pOuterHeader = pOuterLoop->getHeader();

	return true;
}

bool InvArray::IsArrayAccessLoop(BasicBlock * pHeader, set<LoadInst *> & setArrayLoad)
{

	Function * pFunction = pHeader->getParent();
	LoopInfo * pLI = &(getAnalysis<LoopInfo>(*pFunction));

	Loop * pLoop = pLI->getLoopFor(pHeader);

	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); BB++ )
	{	
		for(BasicBlock::iterator II = (*BB)->begin(); II != (*BB)->end(); II ++ )
		{
			if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
			{
				Loop * pCurrentLoop = pLI->getLoopFor(*BB);

				if(BeArrayAccess(pCurrentLoop, pLoad, this->SE, this->DL))
				{
					setArrayLoad.insert(pLoad);
				}
			}
		}
	}

	if(setArrayLoad.size() > 0)
	{
		return true;
	}

	return false;
}

void InvArray::AnalyzeLoopAccess(set<LoadInst *> & setArrayLoad)
{
	set<LoadInst *>::iterator itSetLoadBegin = setArrayLoad.begin();
	set<LoadInst *>::iterator itSetLoadEnd   = setArrayLoad.end();

	map<Value *, set<LoadInst *> > BaseValueMapping;

	LoopInfo * pLI = &(getAnalysis<LoopInfo>(*(this->pInnerFunction)));

	for(; itSetLoadBegin != itSetLoadEnd; itSetLoadBegin ++ )
	{
		LoadInst * pLoad = *itSetLoadBegin;
		Loop * pCurrentLoop = pLI->getLoopFor(pLoad->getParent());

		vector<set<Value *> >  vecResult;
		AnalyzeArrayAccess(pLoad, pCurrentLoop, this->SE, this->DL, vecResult);

		set<Value *>::iterator itSetBegin = vecResult[0].begin();
		set<Value *>::iterator itSetEnd   = vecResult[0].end();

		//pLoad->dump();

		
		for(; itSetBegin != itSetEnd; itSetBegin ++ )
		{
			(*itSetBegin)->dump();
		}
		
	}
}


void InvArray::CollectCallee(set<Function *> & setCallees)
{
	LoopInfo * pOuterLI = &(getAnalysis<LoopInfo>(*(this->pOuterFunction)));
	Loop * pOuterLoop = pOuterLI->getLoopFor(this->pOuterHeader);

	vector<Function *> vecWorkList;

	for(Loop::block_iterator BB = pOuterLoop->block_begin(); BB != pOuterLoop->block_end(); BB++ )
	{	
		if(isa<UnreachableInst>((*BB)->getTerminator()))
		{
			continue;
		}

		for(BasicBlock::iterator II = (*BB)->begin(); II != (*BB)->end(); II ++ )
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

				if(this->LibraryTypeMapping.find(pCalledFunction) != this->LibraryTypeMapping.end())
				{
					continue;
				}

				if(setCallees.find(pCalledFunction) == setCallees.end())
				{
					vecWorkList.push_back(pCalledFunction);
					setCallees.insert(pCalledFunction);
				}
			}
		}
	}

	while(vecWorkList.size() > 0)
	{
		Function * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		for(Function::iterator BB = pCurrent->begin(); BB != pCurrent->end(); BB ++ )
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

					if(pCalledFunction->isDeclaration())
					{
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalledFunction) != this->LibraryTypeMapping.end())
					{
						continue;
					}

					if(setCallees.find(pCalledFunction) == setCallees.end())
					{
						vecWorkList.push_back(pCalledFunction);
						setCallees.insert(pCalledFunction);
					}
				}
			}
		}
	}
}


/*
void InvArray::CollectCallSite(map<Function *, set<Instruction *> > & FuncCSMapping)
{
	vector<Function *> vecWorkList;

	LoopInfo * pOuterLI = &(getAnalysis<LoopInfo>(*(this->pOuterFunction)));
	Loop * pOuterLoop = pOuterLI->getLoopFor(this->pOuterHeader);

	set<Function *> setProcessedFunction;

	for(Loop::block_iterator BB = pOuterLoop->block_begin(); BB != pOuterLoop->block_end(); BB++ )
	{	
		if(isa<UnreachableInst>((*BB)->getTerminator()))
		{
			continue;
		}

		for(BasicBlock::iterator II = (*BB)->begin(); II != (*BB)->end(); II ++ )
		{
			if(isa<CallInst>(II) || isa<InvokeInst>(II))
			{
				if(isa<DbgInfoIntrinsic>(II))
				{
					continue;
				}


				if(pCalledFunction == NULL)
				{
					continue;
				}

				if(pCalledFunction->isDeclaration())
				{
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalledFunction) != this->LibraryTypeMapping.end())
				{
					continue;
				}

				FuncCSMapping[pCa]

			}

		}

}

*/


void InvArray::BuildPossibleCallStack(vector<vector<Instruction *> > & vecCallStack)
{
	vector<Function *> vecWorkList;
	queue< vector<Instruction *> > queueCS;
	map<Function *, vector<Instruction *> > FuncCallSiteMapping;

	LoopInfo * pOuterLI = &(getAnalysis<LoopInfo>(*(this->pOuterFunction)));
	Loop * pOuterLoop = pOuterLI->getLoopFor(this->pOuterHeader);

	for(Loop::block_iterator BB = pOuterLoop->block_begin(); BB != pOuterLoop->block_end(); BB++ )
	{	
		if(isa<UnreachableInst>((*BB)->getTerminator()))
		{
			continue;
		}

		for(BasicBlock::iterator II = (*BB)->begin(); II != (*BB)->end(); II ++ )
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

				if(this->LibraryTypeMapping.find(pCalledFunction) != this->LibraryTypeMapping.end())
				{
					continue;
				}

				vecWorkList.push_back(pCalledFunction);
				vector<Instruction *> vecTmp;
				vecTmp.push_back(II);

				queueCS.push(vecTmp);

			}
		}
	}

	set<Function *> setProcessedFunction;

	while(vecWorkList.size() > 0)
	{
		Function * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		if(setProcessedFunction.find(pCurrent) != setProcessedFunction.end())
		{
			continue;
		}

		setProcessedFunction.insert(pCurrent);

		for(Function::iterator BB = pCurrent->begin(); BB != pCurrent->end(); BB ++)
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

					if(pCalledFunction->isDeclaration())
					{
						continue;
					}

					if(this->LibraryTypeMapping.find(pCalledFunction) != this->LibraryTypeMapping.end())
					{
						continue;
					}

					FuncCallSiteMapping[pCurrent].push_back(II);
					vecWorkList.push_back(pCalledFunction);
				}
			}
		}
	}
	
	while(queueCS.size() > 0)
	{
		vector<Instruction *> vecCurrentCS = queueCS.front();
		queueCS.pop();

		CallSite cs(vecCurrentCS.back());
		Function * pCurrentFunction = cs.getCalledFunction();
		
		vector<Instruction *>::iterator itVecBegin = FuncCallSiteMapping[pCurrentFunction].begin();
		vector<Instruction *>::iterator itVecEnd   = FuncCallSiteMapping[pCurrentFunction].end();

		for(; itVecBegin != itVecEnd; itVecBegin ++)
		{
			CallSite csTmp(*itVecBegin);
			Function * pCallee = csTmp.getCalledFunction();

			vector<Instruction *> vecTmp = vecCurrentCS;
			vecTmp.push_back(*itVecBegin);

			if(pCallee == pInnerFunction)
			{
				vecCallStack.push_back(vecTmp);
			}	
			else
			{	
				queueCS.push(vecTmp);
			}
		}
	}
}

void InvArray::CollectOtherLoops(map<Function *, vector<BasicBlock * > > & FuncHeaderMapping, set<Function *> & setCallees)
{
	 LoopInfo * pOuterLI = &(getAnalysis<LoopInfo>(*(this->pOuterFunction)));
	 Loop * pOuter = pOuterLI->getLoopFor(this->pOuterHeader);

	 for(Loop::iterator LL = pOuter->begin(); LL != pOuter->end(); LL ++ )
	 {
	 	if((*LL)->getHeader() != this->pInnerHeader)
	 	{
	 		FuncHeaderMapping[this->pOuterFunction].push_back((*LL)->getHeader());
	 	}
	 }

	 set<Function *>::iterator itSetBegin = setCallees.begin();
	 set<Function *>::iterator itSetEnd   = setCallees.end();

	 for(; itSetBegin != itSetEnd; itSetBegin ++ )
	 {
	 	Function * pFunction = * itSetBegin;
	 	LoopInfo * pLI = &(getAnalysis<LoopInfo>(*pFunction));

	 	for(Loop::iterator LL = pLI->begin(); LL != pLI->end(); LL ++ )
	 	{
	 		if((*LL)->getHeader() != this->pInnerHeader)
	 		{
	 			FuncHeaderMapping[pFunction].push_back((*LL)->getHeader());
	 		}
	 	}
	}
}

bool InvArray::ControlPrune(BasicBlock * pHeader, DominatorTree * DT , PostDominatorTree * PDT, ControlDependenceGraphBase & CDG)
{
	errs() << "Header: " << pHeader->getName() << "\n";

	Function * pFunction = pHeader->getParent();

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		if(CDG.influences(BB, pHeader) && DT->dominates(BB, pHeader))
		{
			errs() << BB->getName() << "\n";

			if(BranchInst * pBranch = dyn_cast<BranchInst>(BB->getTerminator()))
			{
				if(CmpInst * pCmp = dyn_cast<CmpInst>(pBranch->getCondition()))
				{
					errs() << pCmp->getPredicate() << "\n";
				}
			}

		}
	}

	exit(0);
	return false;


}


void InvArray::PruneLoop(map<Function *, vector<BasicBlock * > > & FuncHeaderMapping )
{
	int count = 0;

	map<Function *, vector<BasicBlock * > >::iterator itMapBegin = FuncHeaderMapping.begin();
	map<Function *, vector<BasicBlock * > >::iterator itMapEnd   = FuncHeaderMapping.end();

	set<BasicBlock *> setToPruned;

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		vector<BasicBlock *>::iterator itVecBegin = itMapBegin->second.begin();
		vector<BasicBlock *>::iterator itVecEnd = itMapBegin->second.end();

		Function * pCurrent = itMapBegin->first;

		LoopInfo * pLI = &(getAnalysis<LoopInfo>(*pCurrent));
		ScalarEvolution * pSE = &(getAnalysis<ScalarEvolution>(*pCurrent));

		ControlDependenceGraphBase CDG;
		PostDominatorTree & PDT = getAnalysis<PostDominatorTree>(*pCurrent);
		DominatorTree & DT = getAnalysis<DominatorTree>(*pCurrent);

		CDG.graphForFunction(*pCurrent, PDT);

		for(; itVecBegin != itVecEnd; itVecBegin ++ )
		{
			BasicBlock * pBB = *itVecBegin;
			Loop * pLoop = pLI->getLoopFor(pBB);

			Value * pValue = CalculateLoopTripCounter(pLoop);
			
			if(pValue != NULL)
			{
				if(beNotLargerConstant(pValue))
				{
					setToPruned.insert(pBB);
					continue;
				}
			}

			if(ControlPrune(pBB, &DT, &PDT, CDG))
			{
				setToPruned.insert(pBB);
				continue;
			}
		}
	}
}


bool InvArray::runOnModule(Module &M) 
{
	this->pModule = &M;

	if(!SearchInnerLoop())
	{
		return false;
	}

	set<LoadInst *> setArrayLoad;

	if(!IsArrayAccessLoop(this->pInnerHeader, setArrayLoad))
	{
		return false;
	}

	if(!SearchOuterLoop())
	{
		return false;
	}

	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	vector<vector<Instruction *> > vecCallStack;
	BuildPossibleCallStack(vecCallStack);

	if(vecCallStack.size() == 0)
	{
		errs() << "Failed to build the call stack\n";
	}

	AnalyzeLoopAccess(setArrayLoad);	

	set<Function *> setCallees;
	CollectCallee(setCallees);

	map<Function *, vector<BasicBlock * > > FuncHeaderMapping;
	CollectOtherLoops(FuncHeaderMapping, setCallees);

	PruneLoop(FuncHeaderMapping);


	return false;
}

