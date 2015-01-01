
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

/*
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
*/

//vecA.size() >= vecB.size()
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

	return false;
}



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
			return b;
		}
	}
} 



int EditDistance(vector<long> & vecA, vector<long> & vecB)
{
	int * d[2];

    d[0] = (int *)malloc(sizeof(int) * (vecB.size()+1 ));
    d[1] = (int *)malloc(sizeof(int) * (vecB.size()+1 ));

    for(int i = 0; i < vecB.size()+1; i ++)
    {
    	d[0][i] = i;
    	d[0][i] = 0;
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
    			d[index][j] = d[last][j-1];
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

    int result = d[index][vecB.size()];
    free(d[0]);
    free(d[1]);

    return result;

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
			//cout << itMapBegin->first << ": " << itMapBegin->second << " " << ParaValueMapping2[itMapBegin->first] << endl;
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
	map<unsigned, pair<vector<long>, vector<long> > > LoadValueMapping1;
	map<unsigned, pair<vector<long>, vector<long> > > LoadValueMapping2;

	for(; index1 < vecA.size(); index1++)
	{
		LoadValueMapping1[vecA[index1].LR.uInstructionID].first.push_back(vecA[index1].LR.LoadAddress);
		LoadValueMapping1[vecA[index1].LR.uInstructionID].second.push_back(vecA[index1].LR.LoadValue);
	}

	//cout << "********************************************\n";

	for(; index2 < vecB.size(); index2++)
	{
		LoadValueMapping2[vecB[index2].LR.uInstructionID].first.push_back(vecB[index2].LR.LoadAddress);
		LoadValueMapping2[vecB[index2].LR.uInstructionID].second.push_back(vecB[index2].LR.LoadValue);
	}
	

	map<unsigned, pair<vector<long>, vector<long> > >::iterator itMapLoadBegin = LoadValueMapping1.begin();
	map<unsigned, pair<vector<long>, vector<long> > >::iterator itMapLoadEnd   = LoadValueMapping1.end();

	for(; itMapLoadBegin != itMapLoadEnd; itMapLoadBegin ++ )
	{
		if(itMapLoadBegin->second.first.size() >= LoadValueMapping2[itMapLoadBegin->first].first.size() )
		{
			if(SubSequence(itMapLoadBegin->second.second, LoadValueMapping2[itMapLoadBegin->first].second))
			{
				continue;
			}
		}
		else
		{
			if(SubSequence(LoadValueMapping2[itMapLoadBegin->first].second, itMapLoadBegin->second.second))
			{
				continue;
			}
		}

		int AddressDistance = EditDistance(itMapLoadBegin->second.first, LoadValueMapping2[itMapLoadBegin->first].first);
		int ValueDistance   = EditDistance(itMapLoadBegin->second.second, LoadValueMapping2[itMapLoadBegin->first].second);

		if(ValueDistance == 1 )
		{
			continue;
		}
		else 
		{
			int sizeDifferent = itMapLoadBegin->second.first.size() - LoadValueMapping2[itMapLoadBegin->first].first.size();
			if(sizeDifferent < 0 )
			{
				sizeDifferent = sizeDifferent * (-1);
			}

			if(sizeDifferent == ValueDistance)
			{
				continue;
			}

			printf("LoadID: %d, AddressDistance: %d, ValueDistance: %d\n", itMapLoadBegin->first, AddressDistance, ValueDistance);
		}
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

	vector<vector<LogRecord> > vecLogRecord;
	vector<LogRecord> vecTmp;

	int count = 0;

	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{
		count ++;
		
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
				//printf("%d %d\n", iLast, iCurrent);
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
	

	set<int> setDifferentPara;
	set<int> setDifferentInst;


	int index = 0;

	while(index < vecLogRecord.size() )
	{
		if(vecLogRecord[index][0].DR.numExecution + 1 == vecLogRecord[index + 1][0].DR.numExecution)
		{
			CmpTwoConsecutiveSequence(vecLogRecord[index], vecLogRecord[index+1], setDifferentPara, setDifferentInst);
			index += 2;
		}
		else if(vecLogRecord[index+1][0].DR.numExecution + 1 == vecLogRecord[index + 2][0].DR.numExecution)
		{
			CmpTwoConsecutiveSequence(vecLogRecord[index+1], vecLogRecord[index+2], setDifferentPara, setDifferentInst);
			index += 3;
		}
		else
		{
			printf("%ld %ld %ld\n", vecLogRecord[index][0].DR.numExecution, vecLogRecord[index+1][0].DR.numExecution, vecLogRecord[index+2][0].DR.numExecution);
			exit(0);
		}

	}

	/*
	for(size_t i = 0; i < vecLogRecord.size()/2; i ++ )
	{
		printf("%ld %ld\n", vecLogRecord[i*2][0].DR.numExecution, vecLogRecord[i*2+1][0].DR.numExecution);
		//CmpTwoConsecutiveSequence(vecLogRecord[i*2], vecLogRecord[i*2+1], setDifferentPara, setDifferentInst);
	}
	*/


	cout << "Different Para Num: " << setDifferentPara.size() << endl;

	

	set<int>::iterator itSetBegin = setDifferentPara.begin();
	set<int>::iterator itSetEnd = setDifferentPara.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		cout << (*itSetBegin) << endl;
	}

	cout << "Different Inst Num: " << setDifferentInst.size() << endl; 

	itSetBegin = setDifferentInst.begin();
	itSetEnd = setDifferentInst.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		cout << (*itSetBegin) << endl;
	}
	
}