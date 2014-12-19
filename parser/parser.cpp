
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

using namespace std;

void PrintLoadRecord( LogRecord log)
{
	cout << log.LR.uInstructionID << ": "<< hex << log.LR.LoadAddress << " " << dec << log.LR.LoadValue << endl;
}

void PrintInstRecord(LogRecord log)
{
	cout << log.IR.uInstructionID << ": " << log.IR.Value << endl;
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
	int iInstruction = 0;
	int iTotalLoad = 0;
	int iLoad = 0;

	vector<int> vecLoad;
	vector<int> vecInstruction;

	int iLast = 0;
	int iCurrent = 0;


	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{
		switch(log.RecordType)
		{
			case LogRecord::Load:
				iLoad ++;
				iTotalLoad++;
				break;
			case LogRecord::Inst:
				iInstruction ++;
				iTotalInstruction ++;
				break;
				
			case LogRecord::Delimiter:
				iExecution++;
				iCurrent = log.DR.numExecution;
				printf("%d %d\n", iCurrent, iLast);
				if(iLast != iCurrent)
				{
					iLast = iCurrent;
					if(vecLoad.size()>0 || iLoad > 0)
					{
						vecLoad.push_back(iLoad);
						iLoad = 0;
						vecInstruction.push_back(iLast);
						iLast = 0;
					}
				}

				break;
		}
	}

	vecLoad.push_back(iLoad);
	vecInstruction.push_back(iLast);

	fclose(MyLogFile);
	cout << "Total Load: " << iTotalLoad << endl;
	cout << "Total Instruction: " << iTotalInstruction << endl;
	cout << "Total Exeuction: " << iExecution << endl;
	cout << vecLoad.size() << endl;
}