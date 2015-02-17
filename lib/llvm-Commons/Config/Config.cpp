
#include <fstream>
#include <sstream>

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DebugInfo.h"
#include "llvm-Commons/Config/Config.h"

using namespace llvm;
using namespace std;


namespace llvm_Commons
{

void ParseLibraryFunctionFile(string & sFileName,  Module * pM, map<Function *, LibraryFunctionType> & LibraryTypeMapping)
{
	string line;
	ifstream ifile(sFileName.c_str());
	if (ifile.is_open())
	{
		LibraryFunctionType CurrentType;

		while(getline(ifile, line))
		{
			if(line.substr(0, 2) == "//")
			{
				string sType = line.substr(2, line.length()-2);

				if(sType == "Transparent")
				{
					CurrentType = LF_TRANSPARENT;
				}	
				else if(sType == "Pure" )
				{
					CurrentType = LF_PURE;
				}
				else if(sType == "Malloc")
				{
					CurrentType = LF_MALLOC;
				}
				else if(sType == "IO")
				{
					CurrentType = LF_IO;
				}
				else if(sType == "Other")
				{
					CurrentType = LF_OTHER;
				}
				else
				{
					assert(0);
				}

				continue;
			}

			Function * pFunction = pM->getFunction(line.c_str());

			if(pFunction != NULL)
			{
				LibraryTypeMapping[pFunction] = CurrentType;
				
			}
			
		}

		ifile.close();
	}
}

void ParseMonitoredInstFile(string & sFileName, Module * pModule, set<int> & setInstID, vector<pair<Function *, int> > & vecParaIndex) 
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
				setInstID.insert(iIndex);
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

void PrintInstructionInfo(Instruction * pInst)
{
	char pPath[100];

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

void PrintArgumentInfo(Argument * pArg)
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


}

