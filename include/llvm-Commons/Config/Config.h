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

class MonitoredElement {
public:
	set<int> MonitoredInst;
	set<int> setMonitoredPara;
	vector<pair<Function *, int> > MonitoredPara;

	map<int, int> ParaIDContentMapping;
	map<int, int> ContentIDParaIDMapping;

 	map<int, int> InstIDContentMapping;
 	map<int, int> ContentIDInstIDMapping;

	vector<vector<string> > vecFileContent;

};



	enum LibraryFunctionType{
		LF_TRANSPARENT,
		LF_PURE,
		LF_MALLOC,
		LF_IO,
		LF_OTHER
	};

	void DumpMonitoredElement(MonitoredElement & Elements);

	void ParseFeaturedInstFile(string & sFileName, Module * pModule, MonitoredElement & Elements);

	void ParseLibraryFunctionFile(string & sFileName,  Module * pM, map<Function *, LibraryFunctionType> & LibraryTypeMapping);

	void ParseMonitoredInstFile(string & sFileName, Module * pModule, set<int> & setInstID, vector<pair<Function *, int> > & vecParaIndex);

	void PrintInstructionInfo(Instruction * pInst);

	void PrintArgumentInfo(Argument * pArg);

	bool PossibleArrayAccess(vector<string> & vecFeatures, vector< vector<pair<int, int > > > & vecIndex);

	Value * SearchLineValue(string & sLine, Function * pFunc );

	int GetValueID(Value * pValue);
}


#endif

