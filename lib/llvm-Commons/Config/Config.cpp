
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


bool PossibleArrayAccess(vector<string> & vecFeatures, vector< vector<pair<int, int > > > & vecIndex)
{
	bool bArray = false;
	int iNum = 0;

	vector<pair<int, int> > vecTmp;
	pair<int, int> pairTmp;

	for(size_t i = 0; i < vecFeatures.size(); i ++ )
	{
		//errs() << vecFeatures[i] << "\n";
		if(vecFeatures[i].find("//---Array Access") == 0 )
		{
			bArray = true;
			continue;
		}

		if(!bArray)
		{
			continue;
		}

		if(vecFeatures[i].find("//---Base:") == 0 || vecFeatures[i].find("//---Init:") == 0 || vecFeatures[i].find("//---Index:") == 0)
		{
			string sIndex = vecFeatures[i].substr(vecFeatures[i].find(':') + 1 , vecFeatures[i].length() - vecFeatures[i].find(':') - 1);
			string buf; 
			stringstream ss(sIndex); 

    		vector<string> tokens; 

			while (ss >> buf)
				tokens.push_back(buf);

			iNum = atoi(tokens[0].c_str());

			if(iNum == 0)
			{
				vecIndex.push_back(vecTmp);
				vecTmp.clear();
			}
		}

		if(vecFeatures[i].find("//---Inst") == 0)
		{
			iNum --;

			if(iNum >=0 )
			{
				pairTmp.first = i;
				pairTmp.second = 0;

				vecTmp.push_back(pairTmp);

				if(iNum == 0)
				{
					vecIndex.push_back(vecTmp);
					vecTmp.clear();
				}
			}

			continue;
		}

		if(vecFeatures[i].find("//---Func") == 0 )
		{
			iNum --;

			if(iNum >= 0 )
			{
				pairTmp.first = i;
				pairTmp.second = 1;

				vecTmp.push_back(pairTmp);

				if(iNum == 0)
				{
					vecIndex.push_back(vecTmp);
					vecTmp.clear();
				}
			}
		}
	}

	return bArray;
}

Value * SearchLineValue(string & sLine, Function * pFunc )
{

	if(sLine.find("Inst") != string::npos)
	{
		if(sLine.find(':') == string::npos)
		{
			return NULL;
		}

		string sIndex = sLine.substr(sLine.find("Inst") + 5, sLine.find(':'));
		uint64_t iIndex = atoi(sIndex.c_str());

		for(Function::iterator BB = pFunc->begin(); BB != pFunc->end(); BB ++)
		{
			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				MDNode *Node = II->getMetadata("ins_id");
				if(Node!=NULL)
				{
					assert(Node->getNumOperands() == 1);
					ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
					assert(CI);

					if(CI->getZExtValue() == iIndex)
					{
						return II;
					}
				}
			}
		}

		return NULL;
	}
	else if(sLine.find("Func") != string::npos)
	{
		if(sLine.find(':') == string::npos)
		{
			return NULL;
		}

		string sIndex = sLine.substr(0, sLine.find(':'));
		string buf; 
		stringstream ss(sIndex); 

    	vector<string> tokens; 

		while (ss >> buf)
			tokens.push_back(buf);

		int iParaID = atoi(tokens[3].c_str());
		int iIndex = 0;

		for(Function::arg_iterator argBegin = pFunc->arg_begin(); argBegin != pFunc->arg_end(); argBegin ++)
		{
			if(iIndex == iParaID)
			{
				return argBegin;
			}

			iIndex ++;
		}
	}

	return NULL;

}



void DumpMonitoredElement(MonitoredElement & Elements)
{
	for(size_t i = 0 ; i < Elements.vecFileContent.size(); i ++ )
	{
		vector<string>::iterator itVecBegin = Elements.vecFileContent[i].begin();
		vector<string>::iterator itVecEnd   = Elements.vecFileContent[i].end();

		for(; itVecBegin != itVecEnd; itVecBegin ++ )
		{
			errs() << (*itVecBegin) << "\n";
		}
	}
}


void ParseFeaturedInstFile(string & sFileName, Module * pModule, MonitoredElement & Elements)
{
	string line;
	ifstream iFile(sFileName.c_str());

	vector<string> vecTmp;

	if(iFile.is_open())
	{
		while(getline(iFile, line))
		{
			if(line.find("//---") == 0)
			{
				vecTmp.push_back(line);
				continue;
			}
			else if(line.find("Func") == 0)
			{
				if(line.find(':') == string::npos)
				{
					vecTmp.push_back(line);
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

				Elements.setMonitoredPara.insert(iParaID);
				
				if(vecTmp.size() > 0)
				{
					Elements.vecFileContent.push_back(vecTmp);
					vecTmp.clear();			
				}

				vecTmp.push_back(line);

				Elements.ParaIDContentMapping[Elements.MonitoredPara.size()] = Elements.vecFileContent.size();
				Elements.ContentIDParaIDMapping[Elements.vecFileContent.size()] = Elements.MonitoredPara.size();
				Elements.MonitoredPara.push_back(pairTmp);

			}
			else if(line.find("Inst") == 0)
			{
				if(line.find(':') == string::npos)
				{
					vecTmp.push_back(line);
					continue;
				}

				string sIndex = line.substr(5, line.find(':'));
				int iIndex = atoi(sIndex.c_str());
				Elements.MonitoredInst.insert(iIndex);

				if(vecTmp.size() > 0)
				{
					Elements.vecFileContent.push_back(vecTmp);
					vecTmp.clear();	
				}

				vecTmp.push_back(line);

				Elements.InstIDContentMapping[iIndex] = Elements.vecFileContent.size();
				Elements.ContentIDInstIDMapping[Elements.vecFileContent.size()] = iIndex;
			}
			else
			{
				vecTmp.push_back(line);
			}

		}

		iFile.close();
	}
	else
	{
		errs() << "Failed to open the inst-monitor-file\n";
	}

	if(vecTmp.size() > 0)
	{
		Elements.vecFileContent.push_back(vecTmp);
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

int GetValueID(Value * pValue)
{
	if(Argument * pArg = dyn_cast<Argument>(pValue))
	{
		return pArg->getArgNo();
	}
	else if(Instruction * pInst = dyn_cast<Instruction>(pValue))
	{
		MDNode *Node = pInst->getMetadata("ins_id");
		if(Node!=NULL)
		{
			assert(Node->getNumOperands() == 1);
			ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
			assert(CI);
			return CI->getZExtValue() ;
		}
	}


	return -1;
}

}

