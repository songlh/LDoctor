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

void PrintLoadRecord( LogRecord log)
{
	cout << log.LR.uInstructionID << ": "<< hex << log.LR.LoadAddress << " " << dec << log.LR.LoadValue << endl;
}

void PrintInstRecord(LogRecord log)
{
	cout << log.IR.uInstructionID << ": " << log.IR.Value << endl;
}


//assume vecA.size() >= vecB.size()
bool SubSequence(vector<long> & vecA, vector<long> & vecB)
{
	int max = vecA.size() - vecB.size();
	long first = vecB[0];
	for(int i = 0; i <= max; i ++)
	{
		if(vecA[i] != first)
		{
			while(++i <= max && vecA[i] != first);
		}

		if(i<=max)
		{
			int j = i + 1;
			int end = j + vecB.size() - 1; 
			for(int k = 1; j < end && vecA[j] == vecB[k]; j ++, k ++ );

			if(j == end)
			{
				return true;
			}
		}
	}

	first = vecB[vecB.size()-1];
	for(int i = 0; i<= max; i ++ )
	{
		if(vecA[i] != first )
		{
			while(++i <= max && vecA[i] != first);
		}

		if(i<=max)
		{
			int j = i + 1;

			int end = j + vecB.size() - 1;  
			
			for(int k = vecB.size() -2 ; j < end && vecA[j] == vecB[k]; j ++, k -- );

			if(j == end)
			{
				return true;
			}
		}

	}

	return false;
}

int rawEditDistance(vector<long> & vecA, vector<long> & vecB)
{
	vector<vector<int> > vecDistance;

	for(int i = 0; i < vecA.size() + 1; i ++ )
	{
		vector<int> tmp;
		
		for(int j = 0; j < vecB.size() + 1; j ++ )
		{
			tmp.push_back(0);
		}

		vecDistance.push_back(tmp);
	}

	for(int i = 1; i < vecA.size() + 1; i ++)
	{
		vecDistance[i][0] = i;
	}

	for(int i = 1; i < vecB.size() + 1; i ++)
	{
		vecDistance[0][i] = i;
	}

	for(int i = 1; i < vecA.size() + 1; i ++ )
	{
		for(int j = 1; j < vecB.size() + 1; j++ )
		{
			if(vecA[i-1] == vecB[j-1])
			{
				vecDistance[i][j] = vecDistance[i-1][j-1];
			}
			else
			{
				vecDistance[i][j] = minimun(vecDistance[i-1][j-1], vecDistance[i-1][j], vecDistance[i][j-1]) + 1;
			}
		}
	}

	return vecDistance[vecA.size()][vecB.size()];
}

int EditDistance(vector<long> & vecA, vector<long> & vecB )
{
	int * d[2];

	d[0] = (int *)malloc(sizeof(int) * (vecB.size()+1 ));
    d[1] = (int *)malloc(sizeof(int) * (vecB.size()+1 ));

    for(int i = 0; i < vecB.size()+1; i ++)
    {
    	d[0][i] = i;
    	d[1][i] = 0;
    }

    int last;
    int index = 0;

    for(int i = 1; i < vecA.size() + 1; i ++ )
    {
    	last = index;
    	index = (index + 1) % 2;

    	for(int j = 1; j < vecB.size() + 1 ; j ++ )
    	{
    		if(vecA[i-1] == vecB[j-1])
    		{

    			if(j==1)
    			{
    				d[index][j] = i - 1;
    			}
    			else
    			{
    				d[index][j] = d[last][j-1];
    			}
    		}
    		else
    		{
    			if(j==1)
    			{
    				d[index][j] = minimun(d[last][j], i - 1, i ) + 1;
    			}
    			else
    			{
    				d[index][j] = minimun(d[last][j], d[last][j-1], d[index][j-1]) + 1;
    			}
    		}
    	}
    }

    return d[index][vecB.size()];
}


void CmpTwoConsecutiveSequence(vector<LogRecord> & vecA, vector<LogRecord> & vecB)
{
	LogRecord Delimiter1 = vecA[0];
	LogRecord Delimiter2 = vecB[0];

	assert(Delimiter1.RecordType == LogRecord::Delimiter);
	assert(Delimiter2.RecordType == LogRecord::Delimiter);
	assert(Delimiter1.DR.numExecution + 1 == Delimiter2.DR.numExecution);

	cout << "Instance " << Delimiter1.DR.numExecution << " " << Delimiter2.DR.numExecution << endl;

//  compare used input parameter
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

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		cout << "Para: " ;

		if(itMapBegin->second != ParaValueMapping2[itMapBegin->first])
		{	
			cout << "D " ;
		}
		else
		{
			cout << "S " ;
		}

		cout << itMapBegin->first << " " << itMapBegin->second << " " << ParaValueMapping2[itMapBegin->first] << endl; 
	}

	assert(index1 == index2);

// compare value defined 
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
		cout << "Inst: " ;
		if(itMapBegin->second != InstValueMapping2[itMapBegin->first])
		{
			cout << "D ";
		}
		else
		{
			cout << "S ";
		}

		cout << itMapBegin->first << " " << itMapBegin->second << " " << InstValueMapping2[itMapBegin->first] << endl;
	}

	assert(index1 == index2);

//compare memory load inside loop
	map<unsigned, pair<vector<long>, vector<long> > > LoadValueMapping1;
	map<unsigned, pair<vector<long>, vector<long> > > LoadValueMapping2;

	map<unsigned, pair<vector<long>, vector<long> > > LoadReverseValueMapping1;
	map<unsigned, pair<vector<long>, vector<long> > > LoadReverseValueMapping2;

	for(; index1 < vecA.size(); index1++)
	{
		LoadValueMapping1[vecA[index1].LR.uInstructionID].first.push_back(vecA[index1].LR.LoadAddress);
		LoadValueMapping1[vecA[index1].LR.uInstructionID].second.push_back(vecA[index1].LR.LoadValue);
	}

	map<unsigned, pair<vector<long>, vector<long> > >::iterator itLoadValueBegin = LoadValueMapping1.begin();
	map<unsigned, pair<vector<long>, vector<long> > >::iterator itLoadValueEnd   = LoadValueMapping1.end();

	for(; itLoadValueBegin != itLoadValueEnd; itLoadValueBegin ++ )
	{
		for(int i = itLoadValueBegin->second.first.size()-1; i >= 0; i -- )
		{
			LoadReverseValueMapping1[itLoadValueBegin->first].first.push_back(itLoadValueBegin->second.first[i]);
		}

		for(int i = itLoadValueBegin->second.second.size()-1; i >= 0; i -- )
		{
			LoadReverseValueMapping1[itLoadValueBegin->first].second.push_back(itLoadValueBegin->second.second[i]);
		}
	}


	for(; index2 < vecB.size(); index2++)
	{
		LoadValueMapping2[vecB[index2].LR.uInstructionID].first.push_back(vecB[index2].LR.LoadAddress);
		LoadValueMapping2[vecB[index2].LR.uInstructionID].second.push_back(vecB[index2].LR.LoadValue);
	}

	itLoadValueBegin = LoadValueMapping2.begin();
	itLoadValueEnd   = LoadValueMapping2.end();

	for(; itLoadValueBegin != itLoadValueEnd; itLoadValueBegin++ )
	{
		for(int i = itLoadValueBegin->second.first.size()-1; i >= 0; i -- )
		{
			LoadReverseValueMapping2[itLoadValueBegin->first].first.push_back(itLoadValueBegin->second.first[i]);
		}

		for(int i = itLoadValueBegin->second.second.size()-1; i >= 0; i -- )
		{
			LoadReverseValueMapping2[itLoadValueBegin->first].second.push_back(itLoadValueBegin->second.second[i]);
		}
	}


	itLoadValueBegin = LoadValueMapping1.begin();
	itLoadValueEnd   = LoadValueMapping1.end();

	set<unsigned> setProcessedLoad;

	for(; itLoadValueBegin != itLoadValueEnd; itLoadValueBegin ++ )
	{
		setProcessedLoad.insert(itLoadValueBegin->first);

		if(LoadValueMapping2.find(itLoadValueBegin->first) == LoadValueMapping2.end())
		{
			cout << "Load: AppearOne " << itLoadValueBegin->first << " " << Delimiter1.DR.numExecution << endl;
			continue;
		}

		
		if(itLoadValueBegin->second.first.size() > LoadValueMapping2[itLoadValueBegin->first].first.size() )
		{
			if(SubSequence(itLoadValueBegin->second.second, LoadValueMapping2[itLoadValueBegin->first].second ) )
			{
				cout << "Load: SubSequence " << itLoadValueBegin->first << " " << itLoadValueBegin->second.second.size() << " " << LoadValueMapping2[itLoadValueBegin->first].second.size() << endl;
				continue;
			}
		}
		else
		{
			if(SubSequence(LoadValueMapping2[itLoadValueBegin->first].second, itLoadValueBegin->second.second ) )
			{
				cout << "Load: SubSequence " << itLoadValueBegin->first << " " << itLoadValueBegin->second.second.size() << " " << LoadValueMapping2[itLoadValueBegin->first].second.size() << endl;
				continue;
			}
		}

		cout << "Load: EditDistance " << itLoadValueBegin->first << " " << itLoadValueBegin->second.second.size() << " " << LoadValueMapping2[itLoadValueBegin->first].second.size() << " " ;

		int ValueDistance = EditDistance(itLoadValueBegin->second.second, LoadValueMapping2[itLoadValueBegin->first].second);
		int AddressDistance = EditDistance(itLoadValueBegin->second.first, LoadValueMapping2[itLoadValueBegin->first].first);

		cout << AddressDistance << " " << ValueDistance << " ";

		int ReverseValue = EditDistance(itLoadValueBegin->second.second, LoadReverseValueMapping2[itLoadValueBegin->first].second);
		int ReverseDistance = EditDistance(itLoadValueBegin->second.first, LoadReverseValueMapping2[itLoadValueBegin->first].first);

		cout << ReverseDistance << " " << ReverseValue << " ";

		cout << endl;

	}

	itLoadValueBegin = LoadValueMapping2.begin();
	itLoadValueEnd   = LoadValueMapping2.end();

	for(; itLoadValueBegin != itLoadValueEnd; itLoadValueBegin ++ )
	{
		if(setProcessedLoad.find(itLoadValueBegin->first) != setProcessedLoad.end() )
		{
			continue;
		}

		cout << "Load: AppearOne " << itLoadValueBegin->first << " " << Delimiter2.DR.numExecution << endl;
		continue;
	}

	cout << "*******************************************************" << endl;
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

	vector<vector<LogRecord> > vecLogRecord;
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
	cout << endl;

	int index = 0;



	while(index + 1 < vecLogRecord.size() )
	{
		CmpTwoConsecutiveSequence(vecLogRecord[index], vecLogRecord[index+1]);
		index += 2;
	}

}