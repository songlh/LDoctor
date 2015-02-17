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

#include "llvm-Commons/Search/Search.h"
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
}

void MemRange::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesCFG();
	AU.addRequired<LoopInfo>();
	AU.addRequired<ScalarEvolution>();
}

void MemRange::print(raw_ostream &O, const Module *M) const
{
	return;
}

void MemRange::ParseMonitoredInstFile(string & sFileName, Module * pModule)
{
	string line;
	ifstream iFile(sFileName.c_str());

	if(iFile.is_open())
	{
		while (getline(iFile,line))
		{
			if(line.find("//--") == 0)
			{
				continue;
			}
			else if(line.find("Func") == 0 )
			{
				if(line.find(':') == string::npos )
				{
					continue;
				}

				string sIndex = line.substr(0, line.find(':'));
				string buf; 
				stringstream ss(sIndex); 

    			vector<string> tokens; 

				while (ss >> buf)
					tokens.push_back(buf);

				Function * pFunction = pModule->getFunction(tokens[1].c_str());
				
				int iParaID = atoi(tokens[3].c_str());
				pair<Function *, int> pairTmp;
				pairTmp.first = pFunction;
				pairTmp.second = iParaID;
				vecParaIndex.push_back(pairTmp);
				
			}
			else if(line.find("Inst") == 0)
			{
				if(line.find(':') == string::npos)
				{
					continue;
				}

				string sIndex = line.substr(5, line.find(':'));
				int iIndex = atoi(sIndex.c_str());
				this->setInstIndex.insert(iIndex);
			}
			else
			{

			}
			
		}

		iFile.close();
	}
	else
	{
		errs() << "Failed to open the inst-monitor-file\n";
	}
}


void MemRange::IndentifyMonitoredLoad(Loop * pLoop)
{
	for(Loop::block_iterator BB = pLoop->block_begin() ; BB != pLoop->block_end(); BB ++)
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

			if(this->setInstIndex.find(CI->getZExtValue()) != this->setInstIndex.end())
			{
				this->setLoadInst.insert(cast<LoadInst>(II));
			}
		}
	}
}

void MemRange::AnalyzeMonitoredLoad()
{
	set<LoadInst *>::iterator itLoadBegin = this->setLoadInst.begin();
	set<LoadInst *>::iterator itLoadEnd   = this->setLoadInst.end();

	for(; itLoadBegin != itLoadEnd; itLoadBegin ++)
	{
		Value * pointer = (*itLoadBegin)->getPointerOperand();
		const SCEV *S = SE->getSCEV(pointer);
		
		S->dump();
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

	Loop * pInnerLoop = SearchLoopByLineNo(pInnerFunction, this->LI, uSrcLine);

	if(pInnerLoop == NULL)
	{
		errs() << "Cannot Find the Input Loop\n";
		return false;
	} 

	ParseMonitoredInstFile(strMonitorInstFile, &M);
	IndentifyMonitoredLoad(pInnerLoop);

	this->SE->getBackedgeTakenCount(pInnerLoop)->dump();
	AnalyzeMonitoredLoad();
	return false;
}

