
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

void PrintLoadRecord( LogRecord log)
{
	cout << log.LR.uInstructionID << ": "<< hex << log.LR.LoadAddress << " " << dec << log.LR.LoadValue << endl;
}

void PrintInstRecord(LogRecord log)
{
	cout << log.IR.uInstructionID << ": " << log.IR.Value << endl;
}

bool CmpTwoLoadSequence( vector<pair<long, long> > & vecA, vector<pair<long, long> > & vecB )
{
// pattern 1
	if(vecA.size() <= vecB.size() )
	{
		size_t index2;
		for(index2 = 0; index2 < vecB.size(); index2 ++)
		{
			//if(vecA[0].first == vecB[index2].first && vecA[0].second == vecB[index2].second)
			if(vecA[0].second == vecB[index2].second)
			{
				break;
			}
		}

		size_t index1;
		for(index1 = 0; index1 < vecA.size() && index1 + index2 < vecB.size(); index1 ++ )
		{
			//if(vecA[index1].first != vecB[index1 + index2].first || vecA[index1].second != vecB[index1 + index2].second)
			if(vecA[index1].second != vecB[index1 + index2].second)
			{
				break;
			}
		}

		if(index1 == vecA.size())
		{
			return true;
		}
	}
	else
	{
		size_t index1;
		for(index1 = 0; index1 < vecA.size(); index1 ++ )
		{
			//if(vecA[index1].first == vecB[0].first && vecA[index1].second == vecB[0].second)
			if(vecA[index1].second == vecB[0].second)
			{
				break;
			}
		}

		size_t index2;
		for(index2 = 0 ; index2 < vecB.size() && index1 + index2 < vecA.size(); index2 ++ )
		{
			//if(vecB[index2].first != vecA[index1 + index2].first || vecB[index2].second != vecA[index1 + index2].second)
			if(vecB[index2].second != vecA[index1 + index2].second)
			{
				break;
			}
		}

		if(index2 == vecB.size())
		{
			return true;
		}
	}
}

int LCSLength(vector<pair<long, long> > & vecA, vector<pair<long, long> > & vecB)
{
	int m = vecA.size() + 1;
	int n = vecB.size() + 1;

	int ** C = (int **)malloc(sizeof(int*) * m);
	for(int i = 0; i < m ; i ++)
	{
		C[i] = (int *)malloc(sizeof(int) * n);
		for(int j = 0; j < n; j ++)
		{
			C[i][j] = 0;
		}
	}

	for(int i = 1; i < m ; i ++ )
	{
		for(int j = 1; j < n ; j ++ )
		{
			if(vecA[i-1].second == vecB[j-1].second)
			{
				C[i][j] = C[i-1][j-1] + 1;
			}
			else
			{
				if(C[i][j-1] > C[i-1][j])
				{
					C[i][j] = C[i][j-1];
				}
				else
				{
					C[i][j] = C[i-1][j];
				}
			}
		}
	}

	cout << C[m-1][n-1] << " " << vecA.size() << " " << vecB.size() << endl;
	//exit(0);
}


void CmpTwoConsecutiveSequence(vector<LogRecord> & vecA, vector<LogRecord> & vecB, set<int> & setDifferentPara, set<int> & setDifferentInst )
{
	LogRecord Delimiter1 = vecA[0];
	LogRecord Delimiter2 = vecB[0];

	assert(Delimiter1.RecordType == LogRecord::Delimiter);
	assert(Delimiter2.RecordType == LogRecord::Delimiter);
	assert(Delimiter1.DR.numExecution + 1 == Delimiter2.DR.numExecution);

// compare used input parameter
	size_t index1 = 1;
	size_t index2 = 1;

	map<unsigned, long> ParaValueMapping1;
	map<unsigned, long> ParaValueMapping2;

	for(; index1 < vecA.size(); index1++ )
	{
		if(vecA[index1].RecordType != LogRecord::Para)
		{
			break;
		}

		ParaValueMapping1[vecA[index1].PR.uValueID] = vecA[index1].PR.Value;
	}

	for(; index2 < vecB.size(); index2++)
	{
		if(vecB[index2].RecordType != LogRecord::Para)
		{
			break;
		}

		ParaValueMapping2[vecB[index2].PR.uValueID] = vecB[index2].PR.Value;
	}

	assert(ParaValueMapping1.size() == ParaValueMapping2.size());

	map<unsigned, long>::iterator itMapBegin = ParaValueMapping1.begin();
	map<unsigned, long>::iterator itMapEnd   = ParaValueMapping1.end();


	for(; itMapBegin != itMapEnd; itMapBegin++ )
	{
		if(itMapBegin->second != ParaValueMapping2[itMapBegin->first])
		{
			cout << itMapBegin->first << ": " << itMapBegin->second << " " << ParaValueMapping2[itMapBegin->first] << endl;
			setDifferentPara.insert(itMapBegin->first);
		}
	}

	assert(index1 == index2);

//compare value defined outside the loop
	map<unsigned, long> InstValueMapping1;
	map<unsigned, long> InstValueMapping2;

	for(; index1 < vecA.size(); index1 ++)
	{
		if(vecA[index1].RecordType != LogRecord::Inst)
		{
			break;
		}

		InstValueMapping1[vecA[index1].IR.uInstructionID] = vecA[index1].IR.Value;
	}

	for(; index2 < vecB.size(); index2 ++)
	{
		if(vecB[index2].RecordType != LogRecord::Inst)
		{
			break;
		}

		InstValueMapping2[vecB[index2].IR.uInstructionID] = vecB[index2].IR.Value;
	}

	itMapBegin = InstValueMapping1.begin();
	itMapEnd   = InstValueMapping1.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		if(itMapBegin->second != InstValueMapping2[itMapBegin->first])
		{
			//cout << itMapBegin->first << ": " << itMapBegin->second << " " << InstValueMapping2[itMapBegin->first] << endl;
			setDifferentInst.insert(itMapBegin->first);
		}
	}

	assert(index1 == index2);

// compare memory load inside loop
	map<unsigned, vector<pair< long, long > > > LoadValueMapping1;
	map<unsigned, vector<pair< long, long > > > LoadValueMapping2;

	for(; index1 < vecA.size(); index1++)
	{
		pair<long, long> pairTmp;
		pairTmp.first = vecA[index1].LR.LoadAddress;
		pairTmp.second = vecA[index1].LR.LoadValue;
		//cout << vecA[index1].LR.LoadAddress  << ": " << vecA[index1].LR.LoadValue << "\n";
		LoadValueMapping1[vecA[index1].LR.uInstructionID].push_back(pairTmp);
	}

	//cout << "********************************************\n";

	for(; index2 < vecB.size(); index2++)
	{
		pair<long, long> pairTmp;
		pairTmp.first = vecB[index2].LR.LoadAddress;
		pairTmp.second = vecB[index2].LR.LoadValue;
		//cout << vecB[index2].LR.LoadAddress << ": " << vecB[index2].LR.LoadValue << "\n";
		LoadValueMapping2[vecB[index2].LR.uInstructionID].push_back(pairTmp);
	}
	

	map<unsigned, vector<pair<long, long> > >::iterator itMapLoadBegin = LoadValueMapping1.begin();
	map<unsigned, vector<pair<long, long> > >::iterator itMapLoadEnd   = LoadValueMapping1.end();

	for(; itMapLoadBegin != itMapLoadEnd; itMapLoadBegin ++ )
	{
		/*
		if(!CmpTwoLoadSequence(itMapLoadBegin->second, LoadValueMapping2[itMapLoadBegin->first]))
		{
			cout << "Load: " << itMapLoadBegin->first << endl;
			exit(0);
		}
		*/
		LCSLength(itMapLoadBegin->second, LoadValueMapping2[itMapLoadBegin->first] );
	}

	//exit(0);


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

	FILE * MyLogFile = fopen(sInput.c_str(), "r");

	int iExecution = 0;
	int iTotalInstruction = 0;
	int iTotalLoad = 0;
	int iTotalPara = 0;


	int iLast = 0;
	int iCurrent = 0;

	vector< vector<LogRecord> > vecLogRecord;
	vector<LogRecord> vecTmp;

	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{
		
		switch(log.RecordType)
		{
			case LogRecord::Load:
				iTotalLoad++;
				vecTmp.push_back(log);
				break;
			case LogRecord::Inst:
				iTotalInstruction ++;
				vecTmp.push_back(log);
				break;
			case LogRecord::Para:
				iTotalPara ++;
				vecTmp.push_back(log);
				break;
			case LogRecord::Delimiter:
				iCurrent = log.DR.numExecution;
				//printf("%d \n", iCurrent);
				if(iCurrent != iLast)
				{
					if(vecTmp.size() > 0)
					{
						vecLogRecord.push_back(vecTmp);
						vecTmp.clear();
					}

					iLast = iCurrent;
					iExecution ++ ;
				}
				else
				{
					printf("%d %d", iLast, iCurrent);
				}
				vecTmp.push_back(log);
				break;
		}
	}

	vecLogRecord.push_back(vecTmp);

	fclose(MyLogFile);
	cout << "Total Load: " << iTotalLoad << endl;
	cout << "Total Instruction: " << iTotalInstruction << endl;
	cout << "Total Parameter: " << iTotalPara << endl;
	cout << "Total Exeuction: " << iExecution << endl;
	

	set<int> setDifferentPara;
	set<int> setDifferentInst;

	for(size_t i = 0; i < vecLogRecord.size()/2; i ++ )
	{
		CmpTwoConsecutiveSequence(vecLogRecord[i*2], vecLogRecord[i*2+1], setDifferentPara, setDifferentInst);
	}


	cout << "Different Para Num: " << setDifferentPara.size() << endl;

	cout << "Different Inst Num: " << setDifferentInst.size() << endl; 
}