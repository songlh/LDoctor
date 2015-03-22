#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/Config/Config.h"
#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"
#include "llvm-Commons/SFReach/MemFootPrintUtility.h"
#include "Analysis/InterProcDep/InterProcDep.h"


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/DebugInfo.h"

#include "Redundancy/SysC-Redundancy/SysCRedundancy.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static cl::opt<unsigned> uSrcLine("noLine", 
					cl::desc("Source Code Line Number"), cl::Optional, 
					cl::value_desc("uSrcLine"));

static cl::opt<std::string> strFileName("strFile", 
					cl::desc("File Name"), cl::Optional, 
					cl::value_desc("strFileName"));

static cl::opt<std::string> strFuncName("strFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strFuncName"));

static cl::opt<std::string> strHeader("strHeader",
					cl::desc("Header Name"), cl::Optional,
					cl::value_desc("strHeader"));


static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));


static RegisterPass<SysCRedundancy> X(
		"sysc-redundancy",
		"system call redundancy analysis",
		false,
		true);


char SysCRedundancy::ID = 0;

void SysCRedundancy::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<DominatorTree>();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<InterProcDep>();
}

SysCRedundancy::SysCRedundancy(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	initializeDominatorTreePass(Registry);
}

void SysCRedundancy::print(raw_ostream &O, const Module *M) const
{
	return;
}

void SysCRedundancy::CollectSEInstInsideLoop(Loop * pLoop, set<Instruction *> & setSideEffectInst)
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

	Function * pFunction = pLoop->getHeader()->getParent();

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

void SysCRedundancy::CollectSEInstForCallee(Function * pFunction, set<Instruction *> & setSideEffectInst)
{
	vector<Function *> vecWorkList;
	set<Function *> setProcessed;
	vecWorkList.push_back(pFunction);

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
				if(StoreInst * pStore = dyn_cast<StoreInst>(II))
				{
					Value * pPointer = pStore->getPointerOperand();
					Value * pBase = GetUnderlyingObject(pPointer, this->pDL);

					if(!BeLocalObject(pBase))
					{
						setSideEffectInst.insert(pStore);
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
							setSideEffectInst.insert(II);
						}
						
						continue;
					}

					CallSite cs(II);
					Function * pCalled = cs.getCalledFunction();

					if(pCalled == NULL)
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

					if(setProcessed.find(pCalled) == setProcessed.end())
					{
						setProcessed.insert(pCalled);
						vecWorkList.push_back(pCalled);
					}
				}
			}
		}
	}
}

void SysCRedundancy::RedundantSystemCallChecking(Loop * pLoop)
{
	set<Instruction *> setSEInst;
	CollectSEInstInsideLoop(pLoop, setSEInst);

	//set<BasicBlock *> setTODO;

	map<BasicBlock *, set<Instruction *> > BlockInstSetMapping;

	set<Instruction *>::iterator itSetInstBegin = setSEInst.begin();
	set<Instruction *>::iterator itSetInstEnd   = setSEInst.end();

	for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++)
	{
		//(*itSetInstBegin)->dump();

		if(!(isa<CallInst>(*itSetInstBegin) || isa<InvokeInst>(*itSetInstBegin))) 
		{
			return;
		}

		if(isa<MemIntrinsic>(*itSetInstBegin))
		{
			return;
		}

		CallSite cs(*itSetInstBegin);

		Function * pCalled = cs.getCalledFunction();

		if(pCalled == NULL)
		{
			continue;
		}

		if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() ) 
		{
			if(LibraryTypeMapping[pCalled] != LF_IO)
			{
				return;
			}

			BlockInstSetMapping[(*itSetInstBegin)->getParent()].insert((*itSetInstBegin));
		}
		else if(pCalled->isDeclaration() )
		{
			return;
		}
	}


	set<Function *>::iterator itSetFuncBegin = this->setCallee.begin();
	set<Function *>::iterator itSetFuncEnd   = this->setCallee.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
	{
		set<Instruction *> setSEInstInCallee;
		CollectSEInstForCallee(*itSetFuncBegin, setSEInstInCallee);

		itSetInstBegin = setSEInstInCallee.begin();
		itSetInstEnd   = setSEInstInCallee.end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
		{	
			if(isa<CallInst>(*itSetInstBegin) || isa<InvokeInst>(*itSetInstBegin ))
			{
				if(isa<MemIntrinsic>(*itSetInstBegin))
				{
					return;
				}

				CallSite cs(*itSetInstBegin);

				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL )
				{
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() ) 
				{	
					if(LibraryTypeMapping[pCalled] != LF_IO)
					{
						return;
					}

					set<Instruction *>::iterator itCSBegin = this->CalleeCallSiteMapping[*itSetFuncBegin].begin();
					set<Instruction *>::iterator itCSEnd   = this->CalleeCallSiteMapping[*itSetFuncBegin].end();

					for(; itCSBegin != itCSEnd; itCSBegin ++ )
					{
						BlockInstSetMapping[(*itCSBegin)->getParent()].insert((*itCSBegin));
					}
				}
				else if(pCalled->isDeclaration() )
				{
					return;
				}
			}
			else
			{
				return;
			}
			
		}
	}



	map<BasicBlock *, set<Instruction *> >::iterator itMapBegin = BlockInstSetMapping.begin();
	map<BasicBlock *, set<Instruction *> >::iterator itMapEnd   = BlockInstSetMapping.end();

	set<BasicBlock *> setBlocksInLoop;
	set<BasicBlock *> setLatches;

	CollectLoopLatches(pLoop, setLatches);

	DominatorTree * pDT = &getAnalysis<DominatorTree>(*(pLoop->getHeader()->getParent()));


	char pPath[100];

	for(; itMapBegin != itMapEnd; itMapBegin++)
	{

		set<BasicBlock *>::iterator itLatchBegin = setLatches.begin();
		set<BasicBlock *>::iterator itLatchEnd   = setLatches.end();

		bool flag = true;

		for(; itLatchBegin != itLatchEnd ; itLatchBegin ++)
		{
			if(!pDT->dominates(itMapBegin->first, *itLatchBegin))
			{
				flag = false;
				break;
			}
		}

		if(flag)
		{
			itSetInstBegin = itMapBegin->second.begin();
			itSetInstEnd   = itMapBegin->second.end();

			for(; itSetInstBegin != itSetInstEnd; itSetInstBegin++)
			{
				(*itSetInstBegin)->dump();

				if( MDNode * N = (*itSetInstBegin)->getMetadata("dbg") )
				{
					DILocation Loc(N);
					string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
					realpath( sFileNameForInstruction.c_str() , pPath);
					sFileNameForInstruction = string(pPath);                        
					unsigned int uLineNoForInstruction = Loc.getLineNumber();
					errs() << "//---"<< sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
				}
			} 
		}

	}
}


bool SysCRedundancy::runOnModule(Module& M)
{
	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	Function * pFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);

	if(pFunction == NULL)
	{
		errs() << "Cannot find the recursive function!\n";
		return false;
	}

	errs() << pFunction->getName() << "\n";

	LoopInfo * pLI = &(getAnalysis<LoopInfo>(*pFunction));
	Loop * pLoop; 

	if(strHeader == "")
	{
		pLoop = SearchLoopByLineNo(pFunction, pLI, uSrcLine);
	}
	else
	{
		BasicBlock * pHeader = SearchBlockByName(pFunction, strHeader);
		
		if(pHeader == NULL)
		{
			errs() << "Cannot find the given loop header!\n";
			return false;
		}
	
		pLoop = pLI->getLoopFor(pHeader);	
	}

	if(pLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}

	this->pDL = &getAnalysis<DataLayout>();

	CollectCalleeInsideLoop(pLoop, this->setCallee, this->CalleeCallSiteMapping, this->LibraryTypeMapping);

	RedundantSystemCallChecking(pLoop);


	return false;
}

