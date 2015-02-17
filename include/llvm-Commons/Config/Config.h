#ifndef _H_SONGLH_CONFIG
#define _H_SONGLH_CONFIG

#include <string>
#include <set>
#include <map>
#include <vector>

#include "llvm/Pass.h"



using namespace llvm;
using namespace std;


namespace llvm_Commons {

	enum LibraryFunctionType{
		LF_TRANSPARENT,
		LF_PURE,
		LF_MALLOC,
		LF_IO,
		LF_OTHER
	};

	void ParseLibraryFunctionFile(string & sFileName,  Module * pM, map<Function *, LibraryFunctionType> & LibraryTypeMapping);

	void ParseMonitoredInstFile(string & sFileName, Module * pModule, set<int> & setInstID, vector<pair<Function *, int> > & vecParaIndex);

	void PrintInstructionInfo(Instruction * pInst);

	void PrintArgumentInfo(Argument * pArg);

}


#endif

