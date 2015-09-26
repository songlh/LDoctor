#include "parser.h"

#include <cassert>
#include <errno.h>
#include <iostream>
#include <math.h>
#include <sstream>
#include <stdlib.h>
#include <stdio.h>
#include <string>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>
#include <vector>
#include <map>
#include <set>

using namespace std;

template <typename Type>
Type minimun( Type a, Type b, Type c)
{
	if(a > b)
	{
		if(b > c)
		{
			return c;
		}
		else
		{
			return b;
		}
	}
	else
	{
		if(a > c)
		{
			return c;
		}
		else
		{
			return a;
		}
	}
}

template <typename Type>
Type maximum(Type a, Type b)
{
	if(a>b)
	{
		return a;
	}
	else
	{
		return b;
	}
}

int main(int argc, char ** argv)
{
	if(argc != 2)
	{
		cout << "parameter number is wrong" << endl;
		exit(0);
	}

	string sInput = string(argv[1]);
	LogRecord log;
	long lTotalMemLength = 0;

	FILE * MyLogFile = fopen(sInput.c_str(), "r");

	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{
		if(log.RecordType == LogRecord::Mem)
		{
			lTotalMemLength += log.MR.uLength;
			fseek(MyLogFile, log.MR.uLength, SEEK_CUR);
		}
	}

	char * pMemBuffer = (char *)malloc(sizeof(char) * lTotalMemLength);
	char * pCurrent = pMemBuffer;

	int iTotalInstruction = 0;
	int iTotalLoad = 0;
	int iTotalPara = 0;
	int iTotalMem = 0;
	
	map<long, vector<LogRecord> > IndexRecordMapping;
	map< pair<long, long>, char *> IndexPonterMapping;

	set<long> setInst;
	set<long> setPara;
	fseek(MyLogFile, 0, SEEK_SET);

	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{
		switch(log.RecordType)
		{
			case LogRecord::Load:
				iTotalLoad++;
				IndexRecordMapping[log.LR.uInstance].push_back(log);
				setInst.insert(log.LR.uInstructionID);
				break;
			case LogRecord::Inst:
				iTotalInstruction ++;
				IndexRecordMapping[log.IR.uInstance].push_back(log);
				setInst.insert(log.IR.uInstructionID);
				break;
			case LogRecord::Para:
				iTotalPara ++;
				IndexRecordMapping[log.PR.uInstance].push_back(log);
				setPara.insert(log.PR.uValueID);
				break;
			case LogRecord::Mem:
				iTotalMem ++;
				IndexRecordMapping[log.MR.uInstance].push_back(log);
				long index = IndexRecordMapping[log.MR.uInstance].size() - 1;
				pair<long, long> pairIndex(log.MR.uInstance, index);
				IndexPonterMapping[pairIndex] = pCurrent;
				fread(pCurrent, log.MR.uLength, 1, MyLogFile);
				pCurrent += log.MR.uLength;
				setInst.insert(log.MR.uInstructionID);
				break;
		}
	}

	cout << (long)pMemBuffer << " " << (long)pCurrent << " " << lTotalMemLength << endl;


	cout << "Load: " << iTotalLoad << endl;
	cout << "Inst: " << iTotalInstruction << endl;
	cout << "Para: " << iTotalPara << endl;
	cout << "Mem: "  << iTotalMem << endl;
	cout << "Instance: " << IndexRecordMapping.size() << endl;

	map<long, int> HashValueCountMapping;
	cout << "Distinct Inst: " << setInst.size() << endl;
	cout << "Distinct Para: " << setPara.size() << endl;

	map<long, vector<LogRecord> >::iterator itMapBegin = IndexRecordMapping.begin();
	map<long, vector<LogRecord> >::iterator itMapEnd   = IndexRecordMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		long ret = 0;

		cout << itMapBegin->first << ":" << endl;
		for(int i = 0; i < itMapBegin->second.size(); i ++ )
		{
			switch(itMapBegin->second[i].RecordType)
			{
				
				case LogRecord::Load:
					ret = ret * 13 + itMapBegin->second[i].LR.uInstructionID;
					ret = ret * 13 + itMapBegin->second[i].LR.LoadValue;
					cout << "Load: " << itMapBegin->second[i].LR.uInstructionID << " " << itMapBegin->second[i].LR.LoadAddress << " " << itMapBegin->second[i].LR.LoadValue << endl;
					break;
				

				case LogRecord::Para:
					ret = ret * 13 + itMapBegin->second[i].PR.uValueID;
					ret = ret * 13 + itMapBegin->second[i].PR.Value;
					cout << "Para: " << itMapBegin->second[i].PR.uValueID << " " << itMapBegin->second[i].PR.Value  << endl;
					break;
				
				case LogRecord::Inst:
					ret = ret * 13 + itMapBegin->second[i].IR.uInstructionID;
					ret = ret * 13 + itMapBegin->second[i].IR.Value;
					cout << "Inst: " << itMapBegin->second[i].IR.uInstructionID << " " << itMapBegin->second[i].IR.Value  << endl;
					break;
				
				case LogRecord::Mem:
					ret = ret * 13 + itMapBegin->second[i].MR.uInstructionID;
					long uLength = itMapBegin->second[i].MR.uLength;	
					pair<long, long> pairIndex(itMapBegin->first, i);

					for(long j = 0; j < uLength; j ++ )
					{
						ret = ret * 13 + IndexPonterMapping[pairIndex][j];
					}

				
			}

		}

		cout << "***************************************" << endl;

		HashValueCountMapping[ret] ++;
		
	}
	

	cout << "Hash Size: " << HashValueCountMapping.size() << endl;
	cout << "Ratio: " << IndexRecordMapping.size() * 1.0 / HashValueCountMapping.size() << endl;

}