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
	
	map<long, map<long, vector<LogRecord> > > IndexRecordMapping;
	map<pair<long, long>, char *> IndexPonterMapping;

	set<int> setInt;
	set<int> setPara;

	fseek(MyLogFile, 0, SEEK_SET);

	long numExecution = -1;
	long index = -1;

	set<int> setIndex;

	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{
		switch(log.RecordType)
		{
			case LogRecord::Delimiter:
				numExecution = log.DR.numExecution;
				index ++;
				break;
			case LogRecord::Load:
				iTotalLoad++;
				IndexRecordMapping[numExecution][index].push_back(log);
				setInt.insert(log.LR.uInstructionID);
				setIndex.insert(index);
				break;
			case LogRecord::Inst:
				iTotalInstruction ++;
				setInt.insert(log.IR.uInstructionID);
				IndexRecordMapping[numExecution][index].push_back(log);
				setIndex.insert(index);
				break;
			case LogRecord::Para:
				iTotalPara ++;
				setPara.insert(log.PR.uValueID);
				IndexRecordMapping[numExecution][index].push_back(log);
				setIndex.insert(index);
				break;
			case LogRecord::Mem:
				iTotalMem ++;
				setInt.insert(log.MR.uInstructionID);
				IndexRecordMapping[numExecution][index].push_back(log);
				long iTmp = IndexRecordMapping[numExecution][index].size() - 1;
				pair<long, long> pairIndex(index, iTmp);
				IndexPonterMapping[pairIndex] = pCurrent;
				fread(pCurrent, log.MR.uLength, 1, MyLogFile);
				pCurrent += log.MR.uLength;
				setIndex.insert(index);
				break;
		}
	}

	//cout << index << "\n";
	//exit(0);
	//cout << (long)pMemBuffer << " " << (long)pCurrent << " " << lTotalMemLength << endl;


	cout << "Load: " << iTotalLoad << endl;
	cout << "Inst: " << iTotalInstruction << endl;
	cout << "Para: " << iTotalPara << endl;
	cout << "Mem: "  << iTotalMem << endl;
	cout << "Iterations: " << index + 1 << endl;

	cout << "Number of Values: "  << setInt.size() + setPara.size() << endl;

	int iEmptry = 0;
	for(int i = 0; i < index + 1; i ++ )
	{
		if(setIndex.find(i) == setIndex.end() )
		{
			iEmptry++;
		}
	}
	
	map<long, int> HashValueCountMapping;
	map<long, set<long> > IDValueSetMapping;

	map<long, map< long, vector<LogRecord> > >::iterator itMapBegin = IndexRecordMapping.begin();
	map<long, map< long, vector<LogRecord> > >::iterator itMapEnd   = IndexRecordMapping.end();

	long hashCount = 0;

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		map<long, int> HashValueCountMapping;

		map<long, vector<LogRecord> >::iterator itMapMapBegin = itMapBegin->second.begin();
		map<long, vector<LogRecord> >::iterator itMapMapEnd   = itMapBegin->second.end();

		for(; itMapMapBegin != itMapMapEnd; itMapMapBegin ++ )
		{
			long ret = itMapBegin->first;

			for(int i = 0; i < itMapMapBegin->second.size(); i ++ )
			{
				switch(itMapMapBegin->second[i].RecordType)
				{				
					case LogRecord::Load:
						ret = ret * 13 + itMapMapBegin->second[i].LR.uInstructionID;
						ret = ret * 13 + itMapMapBegin->second[i].LR.LoadValue;
						IDValueSetMapping[itMapMapBegin->second[i].LR.uInstructionID].insert(itMapMapBegin->second[i].LR.LoadValue);
						break;
				
					case LogRecord::Para:
						ret = ret * 13 + itMapMapBegin->second[i].PR.uValueID;
						ret = ret * 13 + itMapMapBegin->second[i].PR.Value;
						break;
				
					case LogRecord::Inst:
						ret = ret * 13 + itMapMapBegin->second[i].IR.uInstructionID;
						ret = ret * 13 + itMapMapBegin->second[i].IR.Value;
						IDValueSetMapping[itMapMapBegin->second[i].IR.uInstructionID].insert(itMapMapBegin->second[i].IR.Value);
						break;
				
					case LogRecord::Mem:
						ret = ret * 13 + itMapMapBegin->second[i].MR.uInstructionID;
						long uLength = itMapMapBegin->second[i].MR.uLength;	
						pair<long, long> pairIndex(itMapMapBegin->first, i);

						for(long j = 0; j < uLength; j ++ )
						{
							ret = ret * 13 + IndexPonterMapping[pairIndex][j];
						}
				}
			}

			HashValueCountMapping[ret] ++;
		}

		hashCount += HashValueCountMapping.size();

	}

	cout << "Hash Size: " << hashCount << endl;
	cout << "Empty: " << iEmptry << endl;
	cout << "Ratio: " << (index + 1 - iEmptry) << "/" << hashCount << " = " << (index + 1 - iEmptry) * 1.0 / hashCount << endl;

}