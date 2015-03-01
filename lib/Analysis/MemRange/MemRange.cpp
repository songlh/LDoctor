#include <fstream>
#include <iostream>
#include <string>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sstream>

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/DebugInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/SEWrapper/SEWrapper.h"
#include "llvm-Commons/Array/Array.h"
#include "llvm-Commons/Config/Config.h"
#include "Analysis/MemRange/MemRange.h"

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

static cl::opt<std::string> strMonitorInstFile("strInstFile",
					cl::desc("Monitored Insts File Name"), cl::Optional,
					cl::value_desc("strInstFile"));

static RegisterPass<MemRange> X("memory-range",
                                "memory range analysis",
								false,
								true);

char MemRange::ID = 0;

MemRange::MemRange(): ModulePass(ID) {
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializeAliasAnalysisAnalysisGroup(Registry);

}

void MemRange::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesCFG();
	AU.addRequired<AliasAnalysis>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<ScalarEvolution>();
	AU.addRequired<DataLayout>();
}

void MemRange::print(raw_ostream &O, const Module *M) const
{
	return;
}


void MemRange::DumpInstPaddingInfo()
{
	for(size_t i = 0 ; i < this->MonitorElems.vecFileContent.size(); i ++ )
	{
		vector<string>::iterator itVecBegin = this->MonitorElems.vecFileContent[i].begin();
		vector<string>::iterator itVecEnd   = this->MonitorElems.vecFileContent[i].end();

		for(; itVecBegin != itVecEnd; itVecBegin ++ )
		{
			errs() << (*itVecBegin) << "\n";
		}

		if(this->MonitorElems.ContentIDInstIDMapping.find(i) == this->MonitorElems.ContentIDInstIDMapping.end())
		{
			continue;
		}

		int iInstID = this->MonitorElems.ContentIDInstIDMapping[i];

		if(IndexLoadMapping.find(iInstID) != IndexLoadMapping.end())
		{
			LoadInst * pLoad = IndexLoadMapping[iInstID];

			if(this->LoadArrayAccessMapping.find(pLoad) != this->LoadArrayAccessMapping.end())
			{
				Loop * pCurrentLoop = this->LI->getLoopFor(pLoad->getParent());
				const SCEV * pTripCounter = CalculateLoopTripCounter(pCurrentLoop, this->SE);
				errs() << "//---Array Access: \n";

				if(pTripCounter != NULL)
				{
					errs() << "//---Trip Counter: ";
					pTripCounter->dump();

					set<Value *> setValue;
					SearchContainedValue(pTripCounter, setValue);

					set<Value *>::iterator itValBegin = setValue.begin();
					set<Value *>::iterator itValEnd   = setValue.end();

					for(; itValBegin != itValEnd; itValBegin ++ )
					{
						if(Instruction * pI = dyn_cast<Instruction>(*itValBegin))
						{
							errs() << "//---";
							PrintInstructionInfo(pI);
						}
						else if(Argument * pArg = dyn_cast<Argument>(*itValBegin))
						{
							errs() << "//---";
							PrintArgumentInfo(pArg);
						}
					}
				}

				if(this->LoadStrideMapping.find(pLoad) != this->LoadStrideMapping.end() )
				{
					errs() << "//---Stride: " << this->LoadStrideMapping[pLoad] << "\n";
				}
	
				set<Value *>::iterator itValBegin = LoadArrayAccessMapping[pLoad][0].begin();
				set<Value *>::iterator itValEnd   = LoadArrayAccessMapping[pLoad][0].end();

				errs() << "//---Base: " << LoadArrayAccessMapping[pLoad][0].size() << "\n";
				for(; itValBegin != itValEnd; itValBegin ++ )
				{
					if(Instruction * pI = dyn_cast<Instruction>(*itValBegin))
					{
						errs() << "//---";
						PrintInstructionInfo(pI);
					}
					else if(Argument * pArg = dyn_cast<Argument>(*itValBegin))
					{
						errs() << "//---";
						PrintArgumentInfo(pArg);
					}
				}

				itValBegin = LoadArrayAccessMapping[pLoad][1].begin();
				itValEnd   = LoadArrayAccessMapping[pLoad][1].end();

				errs() << "//---Init: " << LoadArrayAccessMapping[pLoad][1].size() << "\n";
				for(; itValBegin != itValEnd; itValBegin ++ )
				{
					if(Instruction * pI = dyn_cast<Instruction>(*itValBegin))
					{
						errs() << "//---";
						PrintInstructionInfo(pI);
					}
					else if(Argument * pArg = dyn_cast<Argument>(*itValBegin))
					{
						errs() << "//---";
						PrintArgumentInfo(pArg);
					}
				}

				itValBegin = LoadArrayAccessMapping[pLoad][2].begin();
				itValEnd   = LoadArrayAccessMapping[pLoad][2].end();

				errs() << "//---Index: " << LoadArrayAccessMapping[pLoad][2].size() << "\n";
				for(; itValBegin != itValEnd; itValBegin ++ )
				{
					if(Instruction * pI = dyn_cast<Instruction>(*itValBegin))
					{
						errs() << "//---";
						PrintInstructionInfo(pI);
					}
					else if(Argument * pArg = dyn_cast<Argument>(*itValBegin))
					{
						errs() << "//---";
						PrintArgumentInfo(pArg);
					}
				}
			}
		}
	}
}


void MemRange::AnalyzeMonitoredLoad(Loop * pLoop)
{	
	set<LoadInst *> setLoadInst;

	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); BB++ )
	{	
		for(BasicBlock::iterator II = (*BB)->begin(); II != (*BB)->end(); II ++ )
		{
			MDNode *Node = II->getMetadata("ins_id");
			if(!Node)
			{
				continue;
			}

			assert(Node->getNumOperands() == 1);
			ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
			assert(CI);

			if(this->MonitorElems.MonitoredInst.find(CI->getZExtValue()) != this->MonitorElems.MonitoredInst.end())
			{
				this->IndexLoadMapping[CI->getZExtValue()] = cast<LoadInst>(II);
				setLoadInst.insert(cast<LoadInst>(II));
			}
		}
	}

	set<LoadInst *>::iterator itLoadBegin = setLoadInst.begin();
	set<LoadInst *>::iterator itLoadEnd   = setLoadInst.end();
	
	for(; itLoadBegin != itLoadEnd; itLoadBegin ++)
	{
		Loop * pCurrentLoop = this->LI->getLoopFor((*itLoadBegin)->getParent());

		if(BeArrayAccess(pCurrentLoop, *itLoadBegin, this->SE, this->DL))
		{
			vector<set<Value *> >  vecResult;
			AnalyzeArrayAccess(*itLoadBegin, pCurrentLoop, this->SE, this->DL, vecResult);
			int64_t stride = CalculateStride((*itLoadBegin)->getPointerOperand(), pCurrentLoop, this->SE, this->DL);

			if(stride != 0)
			{
				this->LoadStrideMapping[*itLoadBegin] = stride;
			}

			this->LoadArrayAccessMapping[*itLoadBegin] = vecResult;

		}
	}
}


bool MemRange::runOnModule(Module &M) 
{
	Function * pInnerFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);
	
	if(pInnerFunction == NULL)
	{
		errs() << "Cannot Find the Input Function\n";
		return false;
	}

	this->LI = &(getAnalysis<LoopInfo>(*pInnerFunction));
	this->SE = &(getAnalysis<ScalarEvolution>(*pInnerFunction));
	this->DL = &(getAnalysis<DataLayout>());

	Loop * pInnerLoop = SearchLoopByLineNo(pInnerFunction, this->LI, uSrcLine);

	if(pInnerLoop == NULL)
	{
		errs() << "Cannot Find the Input Loop\n";
		return false;
	} 

	ParseFeaturedInstFile(strMonitorInstFile, &M, this->MonitorElems);

	AnalyzeMonitoredLoad(pInnerLoop);

	DumpInstPaddingInfo();

	return false;
}

