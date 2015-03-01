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
#include <algorithm> 
#include <vector>
#include <map>
#include <set>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/CallSite.h"

#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/Loop/Loop.h"
#include "llvm-Commons/SEWrapper/SEWrapper.h"

#include "Cal/CL-Cal/CL-Cal.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

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

void PrintLoadRecord( LogRecord log)
{
	cout << log.LR.uInstructionID << ": "<< hex << log.LR.LoadAddress << " " << dec << log.LR.LoadValue << endl;
}

void PrintInstRecord(LogRecord log)
{
	cout << log.IR.uInstructionID << ": " << log.IR.Value << endl;
}

//assume vecA.size() >= vecB.size()
template <typename Type>
bool SubSequence(vector<Type> & vecA, vector<Type> & vecB)
{
	int max = vecA.size() - vecB.size();
	Type first = vecB[0];
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

template <typename Type>
unsigned long rawEditDistance(vector<Type> & vecA, vector<Type> & vecB)
{
	vector<vector<unsigned long> > vecDistance;

	for(unsigned long i = 0; i < vecA.size() + 1; i ++ )
	{
		vector<unsigned long> tmp;
		
		for(unsigned long j = 0; j < vecB.size() + 1; j ++ )
		{
			tmp.push_back(0);
		}

		vecDistance.push_back(tmp);
	}

	for(unsigned long i = 1; i < vecA.size() + 1; i ++)
	{
		vecDistance[i][0] = i;
	}

	for(unsigned long i = 1; i < vecB.size() + 1; i ++)
	{
		vecDistance[0][i] = i;
	}

	for(unsigned long i = 1; i < vecA.size() + 1; i ++ )
	{
		for(unsigned long j = 1; j < vecB.size() + 1; j++ )
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

template <typename Type>
unsigned long EditDistance(vector<Type> & vecA, vector<Type> & vecB )
{
	unsigned long * d[2];

	d[0] = (unsigned long *)malloc(sizeof(unsigned long) * (vecB.size()+1 ));
    d[1] = (unsigned long *)malloc(sizeof(unsigned long) * (vecB.size()+1 ));

    for(unsigned long i = 0; i < vecB.size()+1; i ++)
    {
    	d[0][i] = i;
    	d[1][i] = 0;
	}

	int last;
	int index = 0;

	for(unsigned long i = 1; i < vecA.size() + 1; i ++ )
	{
		last = index;
		index = (index + 1) % 2;

		for(unsigned long j = 1; j < vecB.size() + 1 ; j ++ )
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

template <typename Type>
double CompTwoSequence(vector<Type> & SeqA, vector<Type> & SeqB)
{
	assert(SeqA.size() != 0 || SeqB.size() != 0);

	if(SeqA.size() == 0 || SeqB.size() == 0)
	{
		return 0;
	}

	if(SeqA.size() > SeqB.size() )
	{
		if(SubSequence(SeqA, SeqB))
		{
			return 1;
		}
	}
	else
	{
		if(SubSequence(SeqB, SeqA))
		{
			return 1;
		}
	}

	unsigned long ValueDistance = EditDistance(SeqA, SeqB);

	vector<Type> vecReverseSeq = SeqB;
	reverse(vecReverseSeq.begin(), vecReverseSeq.end());
	unsigned long ReverseValue = EditDistance(SeqA, vecReverseSeq);
		
	unsigned long minDistance = min(ValueDistance, ReverseValue);
	unsigned long minLength = min(SeqA.size(), SeqB.size());
	unsigned long uLengthDifference = abs(SeqA.size() - SeqB.size());

	return 1.0 - (minDistance - uLengthDifference) * 1.0 / minLength;
}

template <typename Type>
double NormalizeValue(Type V, Type Min, Type Max)
{
	if(Min == Max)
	{
		return 0;
	}

	return (V - Min) * 1.0 /(Max - Min);
}

size_t GetMaxFromSet(set<size_t > & setInput)
{
	if(setInput.size() == 0)
	{
		return 0;
	}

	set<size_t >::iterator itSetBegin = setInput.begin();
	set<size_t >::iterator itSetEnd   = setInput.end();

	size_t result = *itSetBegin;

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		if(*itSetBegin > result)
		{
			result = *itSetBegin;
		}
	}

	return result;
}

static cl::opt<unsigned> uInnerSrcLine("noInnerLine", 
					cl::desc("Source Code Line Number for Inner Loop"), cl::Optional, 
					cl::value_desc("uInnerSrcCodeLine"));

static cl::opt<std::string> strInnerFileName("strInnerFile", 
					cl::desc("File Name for Inner Loop"), cl::Optional, 
					cl::value_desc("strInnerFileName"));

static cl::opt<std::string> strInnerFuncName("strInnerFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strInnerFuncName"));

static cl::opt<std::string> strMonitorInstFile("strInstFile",
					cl::desc("Monitored Insts File Name"), cl::Optional,
					cl::value_desc("strInstFile"));

static cl::opt<std::string> strTrace("strTrace",
					cl::desc("Trace File Name"), cl::Optional,
					cl::value_desc("strTrace"));

static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));

static cl::opt<std::string> strLoopHeader("strLoopHeader",
					cl::desc("Block Name for Inner Loop"), cl::Optional,
					cl::value_desc("strLoopHeader"));

static RegisterPass<CLCAL> X(
		"cl-cal",
		"cross loop redundancy calculation",
		false,
		true);

char CLCAL::ID = 0;

void CLCAL::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	//AU.addRequired<PostDominatorTree>();
	//AU.addRequired<DominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<ScalarEvolution>();
	
}

CLCAL::CLCAL(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	//initializePostDominatorTreePass(Registry);
	//initializeDominatorTreePass(Registry);
}

void CLCAL::print(raw_ostream &O, const Module *M) const
{
	return;
}

void CLCAL::FreeMemBuffer()
{	
	if(this->lTotalMemLength > 0)
	{
		free(this->pMemBuffer);
	}
}

void CLCAL::ParseTraceFile(vector<vector<LogRecord> > & vecLogRecord)
{
	FILE * MyLogFile = fopen(strTrace.c_str(), "r");

	if(MyLogFile == NULL)
	{
		errs() << "Fail to open trace file\n";
		exit(0);
	}

	LogRecord log;

	this->lTotalMemLength = 0;

	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{
		if(log.RecordType == LogRecord::Mem)
		{
			this->lTotalMemLength += log.MR.uLength;
			fseek(MyLogFile, log.MR.uLength, SEEK_CUR);
		}
	}

	if(lTotalMemLength > 0)
	{
		this->pMemBuffer = (char *)malloc(sizeof(char) * lTotalMemLength);
	}

	fseek(MyLogFile, 0, SEEK_SET);

	char * pCurrent = pMemBuffer;

	int iExecution = 0;
	int iTotalInstruction = 0;
	int iTotalLoad = 0;
	int iTotalPara = 0;
	int iTotalMem = 0;

	int iLast = 0;
	int iCurrent = 0;

	vector<LogRecord> vecTmp;

	while(fread(&log, sizeof(LogRecord), 1, MyLogFile))
	{	
		switch(log.RecordType)
		{
			case LogRecord::Load:
			{
				iTotalLoad++;
				vecTmp.push_back(log);
				break;
			}
			case LogRecord::Inst:
			{
				iTotalInstruction ++;
				vecTmp.push_back(log);
				break;
			}
			case LogRecord::Para:
			{
				iTotalPara ++;
				vecTmp.push_back(log);
				break;
			}
			case LogRecord::Mem:
			{
				iTotalMem ++;
				int iInstanceIndex = vecLogRecord.size();
				int iRecordIndex =vecTmp.size();
				vecTmp.push_back(log);
				pair<int, int> pairIndex(iInstanceIndex, iRecordIndex);
				IndexPonterMapping[pairIndex] = pCurrent;
				fread(pCurrent, log.MR.uLength, 1, MyLogFile);
				pCurrent += log.MR.uLength;
				break;
			}
			case LogRecord::Store:
			{
				assert(0);
				break;
			}	
			case LogRecord::Delimiter:
			{
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
	}

	if(vecTmp.size()>0)
	{
		vecLogRecord.push_back(vecTmp);
	}	
	
	fclose(MyLogFile);

	errs() << "Load: " << iTotalLoad << "\n";
	errs() << "Inst: " << iTotalInstruction << "\n";
	errs() << "Para: " << iTotalPara << "\n";
	errs() << "Mem: "  << iTotalMem << "\n";
	errs() << "Instance: " << vecLogRecord.size() << "\n";
}


void CLCAL::CalMaxMinValue(vector<vector<LogRecord> > & vecLogRecord)
{
	for(size_t i = 0; i < vecLogRecord.size(); i ++ )
	{
		for(size_t j = 0; j < vecLogRecord[i].size(); j ++ )
		{
			int iIndex;
			Value * pValue;
			long lValue;

			switch(vecLogRecord[i][j].RecordType)
			{
				case LogRecord::Load:
				{
					iIndex = vecLogRecord[i][j].LR.uInstructionID;
					pValue = this->IDInstMapping[iIndex];
					lValue = vecLogRecord[i][j].LR.LoadValue;

					break;
				}
				case LogRecord::Inst:
				{
					iIndex = vecLogRecord[i][j].IR.uInstructionID;
					pValue = this->IDInstMapping[iIndex];
					lValue = vecLogRecord[i][j].IR.Value;

					break;
				}
				case LogRecord::Para:
				{
					iIndex = vecLogRecord[i][j].PR.uValueID % 10;
					pValue = this->IDArgMapping[iIndex];
					lValue = vecLogRecord[i][j].PR.Value;

					break;
				}
				case LogRecord::Mem:
				{
					break;
				}
				case LogRecord::Store:
				{
					break;
				}
				case LogRecord::Delimiter:
				{
					break;
				}
			}

			if(this->ValueMinMaxMapping.find(pValue) == this->ValueMinMaxMapping.end() )
			{
				pair<long, long> pairTmp(lValue, lValue);
				this->ValueMinMaxMapping[pValue] = pairTmp;
			}
			else
			{
				if(lValue < this->ValueMinMaxMapping[pValue].first)
				{
					this->ValueMinMaxMapping[pValue].first = lValue;
				}

				if(lValue > this->ValueMinMaxMapping[pValue].second)
				{
					this->ValueMinMaxMapping[pValue].second = lValue;
				}
			}
		}
	}
}

void CLCAL::CalMeanSD(vector<vector<LogRecord> > & vecLogRecord)
{
	map<Value *, vector<long> > ValueValueSeqMapping;

	for(size_t i = 0; i < vecLogRecord.size(); i ++ )
	{
		for(size_t j = 0; j < vecLogRecord[i].size(); j ++ )
		{
			switch(vecLogRecord[i][j].RecordType)
			{
				case LogRecord::Load:
				{
					int iIndex = vecLogRecord[i][j].LR.uInstructionID;
					Instruction * pInst = this->IDInstMapping[iIndex];
					long lValue = vecLogRecord[i][j].LR.LoadValue;

					ValueValueSeqMapping[pInst].push_back(lValue);
					break;
				}
				case LogRecord::Inst:
				{
					int iIndex = vecLogRecord[i][j].IR.uInstructionID;
					Instruction * pInst = this->IDInstMapping[iIndex];
					long lValue = vecLogRecord[i][j].IR.Value;

					ValueValueSeqMapping[pInst].push_back(lValue);
					break;
				}
				case LogRecord::Para:
				{
					int iIndex = vecLogRecord[i][j].PR.uValueID % 10;
					Argument * pArg = this->IDArgMapping[iIndex];
					long lValue = vecLogRecord[i][j].PR.Value;

					ValueValueSeqMapping[pArg].push_back(lValue);
					break;
				}
				case LogRecord::Mem:
				{
					break;
				}
				case LogRecord::Store:
				{
					break;
				}
				case LogRecord::Delimiter:
				{
					break;
				}
			}
		}
	}

	map<Value *, vector<long> >::iterator itMapBegin = ValueValueSeqMapping.begin();
	map<Value *, vector<long> >::iterator itMapEnd   = ValueValueSeqMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		double sum = 0;

		for(size_t i =0; i < itMapBegin->second.size(); i ++ )
		{
			sum += itMapBegin->second[i];
		}

		double mean = sum/(itMapBegin->second.size());
		double sd = 0;

		for(size_t i = 0; i < itMapBegin->second.size(); i ++  )
		{
			double minus = itMapBegin->second[i] - mean;
			sd += minus * minus;
		}

		sd = sd/(itMapBegin->second.size());
		sd = sqrt(sd);

		this->ValueMeanMapping[itMapBegin->first] = mean;
		this->ValueSDMapping[itMapBegin->first] = sd;
	}
}

void CLCAL::ParseInstFile(Function * pInnerFunction, Module * pModule)
{
	ParseFeaturedInstFile(strMonitorInstFile, pModule, this->MonitoredElems);

	for(size_t i = 0; i < this->MonitoredElems.vecFileContent.size(); i ++ )
	{
		vector<vector<pair<int, int > > > vecIndex;
		if(PossibleArrayAccess(this->MonitoredElems.vecFileContent[i], vecIndex))
		{
			LoadInst * pLoad = cast<LoadInst>(SearchLineValue(this->MonitoredElems.vecFileContent[i][0], pInnerFunction));

			set<Value *> setBase;
			for(size_t j = 0; j < vecIndex[0].size(); j ++ )
			{
				Value * pTmp = SearchLineValue(this->MonitoredElems.vecFileContent[i][vecIndex[0][j].first], pInnerFunction );
				setBase.insert(pTmp);
			}

			this->PossibleSkipLoadInfoMapping[pLoad].push_back(setBase);

			set<Value *> setInit;
			for(size_t j = 0; j < vecIndex[1].size(); j ++ )
			{
				Value * pTmp = SearchLineValue(this->MonitoredElems.vecFileContent[i][vecIndex[1][j].first], pInnerFunction );
				setInit.insert(pTmp);
			}

			this->PossibleSkipLoadInfoMapping[pLoad].push_back(setInit);

			set<Value *> setIndex;

			for(size_t j = 0; j < vecIndex[2].size(); j ++ )
			{
				Value * pTmp = SearchLineValue(this->MonitoredElems.vecFileContent[i][vecIndex[2][j].first], pInnerFunction );
				setIndex.insert(pTmp);
			}

			this->PossibleSkipLoadInfoMapping[pLoad].push_back(setIndex);
		}
	}
}

void CLCAL::BuildIDInstMapping(Function * pFunction)
{
	vector<Function *> vecWorkList;
	vecWorkList.push_back(pFunction);

	set<Function *> setProcessed;
	setProcessed.insert(pFunction);

	while(vecWorkList.size()>0)
	{
		Function * pCurrent = vecWorkList.back();
		vecWorkList.pop_back();

		for(Function::iterator BB = pCurrent->begin(); BB != pCurrent->end(); BB ++  )
		{
			if(isa<UnreachableInst>(BB->getTerminator()))
			{
				continue;
			}

			for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
			{
				if(isa<DbgInfoIntrinsic>(II))
				{
					continue;
				}
				else if(isa<InvokeInst>(II) || isa<CallInst>(II))
				{
					CallSite cs(II);
					Function * pCalled = cs.getCalledFunction();
				
					if(pCalled != NULL && this->LibraryTypeMapping.find(pCalled) == this->LibraryTypeMapping.end() && !pCalled->isDeclaration() )
					{
						if(setProcessed.find(pCalled) == setProcessed.end() )
						{
							setProcessed.insert(pCalled);
							vecWorkList.push_back(pCalled);
						}
					}					
				}

				MDNode *Node = II->getMetadata("ins_id");

				if(!Node)
				{
					continue;
				}
			
				assert(Node->getNumOperands() == 1);
				ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
				assert(CI);
			
				if(this->MonitoredElems.MonitoredInst.find(CI->getZExtValue()) != this->MonitoredElems.MonitoredInst.end())
				{
					this->IDInstMapping[CI->getZExtValue()] = II;
				}
			}
		}
	}

	map<LoadInst *, vector<set<Value * > > >::iterator itMapBegin = this->PossibleSkipLoadInfoMapping.begin();
	map<LoadInst *, vector<set<Value * > > >::iterator itMapEnd   = this->PossibleSkipLoadInfoMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		MDNode * Node = itMapBegin->first->getMetadata("ins_id");
		assert(Node != NULL);

		assert(Node->getNumOperands() == 1);
		ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
		assert(CI);

		this->IDInstMapping[CI->getZExtValue()] = itMapBegin->first;

		for(size_t i = 0; i < itMapBegin->second.size(); i ++ )
		{
			set<Value *>::iterator itSetBegin = itMapBegin->second[i].begin();
			set<Value *>::iterator itSetEnd   = itMapBegin->second[i].end();

			for(; itSetBegin != itSetEnd; itSetBegin ++ )
			{
				if(Instruction * pInst = dyn_cast<Instruction>(*itSetBegin))
				{
					Node = pInst->getMetadata("ins_id");
					assert(Node != NULL);

					assert(Node->getNumOperands() == 1);
					CI = dyn_cast<ConstantInt>(Node->getOperand(0));
					assert(CI);

					this->IDInstMapping[CI->getZExtValue()] = pInst;
				}	
			}
		}
	}

	int index = 0;

	for(Function::arg_iterator AB = pFunction->arg_begin(); AB != pFunction->arg_end(); AB ++ )
	{
		IDArgMapping[index] = AB;
		index ++;
	}
}

void CLCAL::DecodeOneInstance(vector<LogRecord> & Instance, map<int, vector<LogRecord> > & IDValueMapping, map<int, LogRecord> & ArgValueMapping, map<int, vector<char> > & IDMemMapping)
{
	int InstanceID = Instance[0].DR.numExecution;

	for(size_t i = 1; i < Instance.size(); i ++ )
	{
		switch(Instance[i].RecordType)
		{
			case LogRecord::Para:
			{
				assert(ArgValueMapping.find(Instance[i].PR.uValueID%10) == ArgValueMapping.end());
				ArgValueMapping[Instance[i].PR.uValueID%10] = Instance[i];
				break;
			}
			case LogRecord::Inst:
			{
				IDValueMapping[Instance[i].IR.uInstructionID].push_back(Instance[i]);
				break;
			}
			case LogRecord::Load:
			{
				IDValueMapping[Instance[i].LR.uInstructionID].push_back(Instance[i]);
				break;
			}
			case LogRecord::Mem:
			{
				pair<int, int> pairIndex(InstanceID, i);
				char * pStart = this->IndexPonterMapping[pairIndex];

				for(long j = 0; j < Instance[i].MR.uLength; j ++ )
				{
					IDMemMapping[Instance[i].MR.uInstructionID].push_back(pStart[j]);
				}

				IDValueMapping[Instance[i].MR.uInstructionID].push_back(Instance[i]);
				break;
			}
			case LogRecord::Store:
			{
				assert(0);
			}
			case LogRecord::Delimiter:
			{
				assert(0);
			}
		}
	}
}

void CLCAL::CompMemSequence(map<Value *, double> & ValueScoreMapping)
{
	set<int> SeqToCompare;

	map<int, vector<char> >::iterator itMapBegin = this->IDMemMapping1.begin();
	map<int, vector<char> >::iterator itMapEnd   = this->IDMemMapping1.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		SeqToCompare.insert(itMapBegin->first);
	}

	itMapBegin = IDMemMapping2.begin();
	itMapEnd   = IDMemMapping2.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		SeqToCompare.insert(itMapBegin->first);
	}

	set<int>::iterator itSetIntBegin = SeqToCompare.begin();
	set<int>::iterator itSetIntEnd   = SeqToCompare.end();

	for(; itSetIntBegin != itSetIntEnd; itSetIntBegin ++ )
	{
		int index = *itSetIntBegin;
		Instruction * pInst = this->IDInstMapping[index];

		if(IDMemMapping1.find(index) == IDMemMapping1.end() || IDMemMapping2.find(index) == IDMemMapping2.end() )
		{
			ValueScoreMapping[pInst] = 0;
			continue;
		}

		this->setLength1.insert(this->IDValueMapping1[index].size());
		this->setLength2.insert(this->IDValueMapping2[index].size());

		ValueScoreMapping[pInst] = CompTwoSequence(IDMemMapping1[index], IDMemMapping2[index]);
	}
}

void CLCAL::CompValueSequence(map<Value *, double> & ValueScoreMapping)
{
	set<int> SeqToCompare;

	map<int, vector<LogRecord> >::iterator itMapBegin = this->IDValueMapping1.begin();
	map<int, vector<LogRecord> >::iterator itMapEnd   = this->IDValueMapping1.end();
	
	Function * pFunction = pLoop->getHeader()->getParent();

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		int index = itMapBegin->first;
		Instruction * pInst = IDInstMapping[index];

		if(isa<MemIntrinsic>(pInst))
		{
			continue;
		}

		if(this->MonitoredElems.MonitoredInst.find(index) == this->MonitoredElems.MonitoredInst.end())
		{
			continue;
		}

		if(this->pLoop->contains(pInst->getParent()))
		{
			SeqToCompare.insert(index);
		}
		else if(pFunction != pInst->getParent()->getParent())
		{
			SeqToCompare.insert(index);
		}

	}

	itMapBegin = this->IDValueMapping2.begin();
	itMapEnd   = this->IDValueMapping2.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		int index = itMapBegin->first;
		Instruction * pInst = IDInstMapping[index];

		if(isa<MemIntrinsic>(pInst))
		{
			continue;
		}

		if(this->MonitoredElems.MonitoredInst.find(index) == this->MonitoredElems.MonitoredInst.end())
		{
			continue;
		}

		if(this->pLoop->contains(pInst->getParent()))
		{
			SeqToCompare.insert(index);
		}
		else if(pFunction != pInst->getParent()->getParent())
		{
			SeqToCompare.insert(index);
		}
	}

	set<int>::iterator itSetIntBegin = SeqToCompare.begin();
	set<int>::iterator itSetIntEnd   = SeqToCompare.end();

	for(; itSetIntBegin != itSetIntEnd; itSetIntBegin++ )
	{
		int index = *itSetIntBegin;
		Instruction * pInst = IDInstMapping[index];

		if(IDValueMapping1.find(index) == IDValueMapping1.end() || IDValueMapping2.find(index) == IDValueMapping2.end() )
		{	
			assert(ValueScoreMapping.find(pInst) == ValueScoreMapping.end());
			ValueScoreMapping[pInst] = 0;
			continue;
		}

		vector<long> Seq1;
		vector<long> Seq2;

		if(isa<LoadInst>(pInst))
		{
			for(size_t i = 0; i < IDValueMapping1[index].size(); i ++ )
			{
				Seq1.push_back(IDValueMapping1[index][i].LR.LoadValue);
			}

			for(size_t i = 0; i < IDValueMapping2[index].size(); i ++ )
			{
				Seq2.push_back(IDValueMapping2[index][i].LR.LoadValue);
			}
		}
		else
		{
			for(size_t i = 0; i < IDValueMapping1[index].size(); i ++ )
			{
				Seq1.push_back(IDValueMapping1[index][i].IR.Value);
			}

			for(size_t i = 0; i < IDValueMapping2[index].size(); i ++ )
			{
				Seq2.push_back(IDValueMapping2[index][i].IR.Value);
			}
		}

		this->setLength1.insert(Seq1.size());
		this->setLength2.insert(Seq2.size());

		ValueScoreMapping[pInst] = CompTwoSequence(Seq1, Seq2);
	}
}

void CLCAL::CollectMonitoredValue(set<Value *> & setMonitoredValue)
{
	map<int, vector<LogRecord> >::iterator itMapBegin = IDValueMapping1.begin();
	map<int, vector<LogRecord> >::iterator itMapEnd   = IDValueMapping1.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		int index = itMapBegin->first;
		Instruction * pInst = this->IDInstMapping[index];
		setMonitoredValue.insert(pInst);
	}

	itMapBegin = IDValueMapping2.begin();
	itMapEnd   = IDValueMapping2.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++)
	{
		int index = itMapBegin->first;
		Instruction * pInst = this->IDInstMapping[index];
		setMonitoredValue.insert(pInst);
	}

	map<int, LogRecord>::iterator itArgMapBegin = ArgValueMapping1.begin();
	map<int, LogRecord>::iterator itArgMapEnd   = ArgValueMapping1.end();

	for(; itArgMapBegin != itArgMapEnd; itArgMapBegin ++)
	{
		int index = itArgMapBegin->first;

		Argument * pArg = this->IDArgMapping[index];
		setMonitoredValue.insert(pArg);
	}

	itArgMapBegin = ArgValueMapping2.begin();
	itArgMapEnd   = ArgValueMapping2.end();

	for(; itArgMapBegin != itArgMapEnd; itArgMapBegin ++)
	{
		int index = itArgMapBegin->first;
		Argument * pArg = this->IDArgMapping[index];
		setMonitoredValue.insert(pArg);
	}
}

void CLCAL::CompSkipLoad(map<Value *, double > & ValueScoreMapping, set<Value *> & setMonitoredValue)
{
	//set<LoadInst *> setSkipLoad;

	map<LoadInst *, vector<set<Value * > > >::iterator itLoadMapBegin = PossibleSkipLoadInfoMapping.begin();
	map<LoadInst *, vector<set<Value * > > >::iterator itLoadMapEnd   = PossibleSkipLoadInfoMapping.end();

	for(; itLoadMapBegin != itLoadMapEnd; itLoadMapBegin ++ )
	{
		LoadInst * pLoad = itLoadMapBegin->first;

		if(setMonitoredValue.find(pLoad) != setMonitoredValue.end() )
		{
			continue;
		}

		if(itLoadMapBegin->second[1].size() != 1)
		{
			continue;
		}

		Value * pInit = *(itLoadMapBegin->second[1].begin());

		if(setMonitoredValue.find(pInit) == setMonitoredValue.end())
		{
			continue;
		}
		
		if(itLoadMapBegin->second[2].size() != 1 )
		{
			continue;
		}

		Value * pIndex = *(itLoadMapBegin->second[2].begin());

		if(setMonitoredValue.find(pIndex) == setMonitoredValue.end())
		{
			continue;
		}

		int iInitID = GetValueID(pInit);
		int iIndexID = GetValueID(pIndex);

		vector<long> SeqA;
		vector<long> SeqB;

		Loop * pCurrentLoop = this->pLI->getLoopFor(pLoad->getParent());

		int64_t stride = CalculateStride(pLoad->getPointerOperand(), pCurrentLoop, this->SE, this->DL);

		if(isa<Argument>(pInit))
		{
			for(size_t i = 0; i < IDValueMapping1[iIndexID].size(); i++ )
			{
				long ltmp = ArgValueMapping1[iInitID].PR.Value;
				long lFinal = IDValueMapping1[iIndexID][i].IR.Value;

				while(ltmp != lFinal)
				{
					SeqA.push_back(ltmp);
					ltmp += stride;
				}
			}

			for(size_t i = 0; i < IDValueMapping2[iIndexID].size(); i++ )
			{

				long ltmp = ArgValueMapping2[iInitID].PR.Value;
				long lFinal = IDValueMapping2[iIndexID][i].IR.Value;

				while(ltmp != lFinal)
				{
					SeqB.push_back(ltmp);
					ltmp += stride;
				}
			}
		}
		else if(Instruction * pInst = dyn_cast<Instruction>(pInit))
		{
			if(this->pLoop->contains(pInst->getParent()))
			{
				assert(IDValueMapping1[iInitID].size() == IDValueMapping1[iIndexID].size());

				for(size_t i = 0; i < IDValueMapping1[iInitID].size(); i ++ )
				{
					long ltmp = IDValueMapping1[iInitID][i].IR.Value;
					long lFinal = IDValueMapping1[iIndexID][i].IR.Value;

					while(ltmp != lFinal)
					{
						SeqA.push_back(ltmp);
						ltmp += stride;
					}
				}

				assert(IDValueMapping2[iInitID].size() == IDValueMapping2[iIndexID].size());

				for(size_t i = 0; i < IDValueMapping2[iInitID].size(); i ++ )
				{
					long ltmp = IDValueMapping2[iInitID][i].IR.Value;
					long lFinal = IDValueMapping2[iIndexID][i].IR.Value;

					while(ltmp != lFinal)
					{
						SeqB.push_back(ltmp);
						ltmp += stride;
					}
				}

			}
			else
			{
				for(size_t i = 0; i < IDValueMapping1[iIndexID].size(); i++ )
				{
					long ltmp = IDValueMapping1[iInitID][0].IR.Value;
					long lFinal = IDValueMapping1[iIndexID][i].IR.Value;

					while(ltmp != lFinal)
					{
						SeqA.push_back(ltmp);
						ltmp += stride;
					}
				}

				for(size_t i = 0; i < IDValueMapping2[iIndexID].size(); i++ )
				{
					long ltmp = IDValueMapping2[iInitID][0].IR.Value;
					long lFinal = IDValueMapping2[iIndexID][i].IR.Value;

					while(ltmp != lFinal)
					{
						SeqB.push_back(ltmp);
						ltmp += stride;
					}
				}
			}
		}

		this->setLength1.insert(SeqA.size());
		this->setLength2.insert(SeqB.size());
		ValueScoreMapping[pLoad] = CompTwoSequence(SeqA, SeqB);
	}
}

bool CLCAL::CanSkipThisValue(Value * pValue)
{
	set<PHINode *> UseOne;
	set<Instruction *> UseOther;

	CollectAllUsesInsideLoop(pValue, pLoop, UseOne, UseOther);

	if(UseOther.size() > 0)
	{
		return false;
	}

	set<PHINode *>::iterator itPHIBegin = UseOne.begin();
	set<PHINode *>::iterator itPHIEnd   = UseOne.end();

	for(; itPHIBegin != itPHIEnd; itPHIBegin ++ )
	{
		PHINode * pPHI = *itPHIBegin;

		for(unsigned i = 0; pPHI->getNumIncomingValues(); i ++)
		{
			if(!pLoop->contains(pPHI->getIncomingBlock(i)))
			{
				continue;
			}

			if(Instruction * pInst = dyn_cast<Instruction>(pPHI->getIncomingValue(i)))
			{
				if(!isa<LoadInst>(pInst))
				{
					return false;
				}
			}

		}
	}

	return true;
}


bool CLCAL::CompIterativeStart(Value * pValue, long Value1, long Value2, map<Value*, double>  & ValueScoreMapping)
{
	set<PHINode *> UseOne;
	set<Instruction *> UseOther;

	CollectAllUsesInsideLoop(pValue, pLoop, UseOne, UseOther);

	if(UseOther.size() > 0)
	{
		return false;
	}

	set<PHINode *>::iterator itPHIBegin = UseOne.begin();
	set<PHINode *>::iterator itPHIEnd   = UseOne.end();

	int count = 0;
	double dResult = 0;

	size_t lengthA = GetMaxFromSet(this->setLength1);
	size_t lengthB = GetMaxFromSet(this->setLength2);
	
	size_t lengthDiff = abs(lengthA - lengthB);
	size_t minLength = min(lengthA, lengthB);

	for(; itPHIBegin != itPHIEnd; itPHIBegin ++ )
	{
		if(!IsIterativeVariable(*itPHIBegin, this->pLoop, this->SE))
		{
			return false;
		}

		int64_t stride = CalculateStride(*itPHIBegin, this->pLoop, this->SE, this->DL);

		if(stride == 0)
		{
			return false;
		}

		count ++;

		stride = abs(stride);

		long ValueDiff = abs(Value1 - Value2);

		if(ValueDiff % stride != 0 )
		{	
			continue;
		}

		ValueDiff = ValueDiff / stride;

		double differentIteration;

		if(ValueDiff > (long)lengthDiff)
		{
			differentIteration = ValueDiff - lengthDiff;
		}
		else
		{
			differentIteration = 0;
		}

		dResult += 1 - differentIteration/minLength;
	}

	ValueScoreMapping[pValue] = dResult/count;
	return true;
}



int CLCAL::CompInstancePair(vector<LogRecord> & InstanceA, vector<LogRecord> & InstanceB)
{
	assert(InstanceA[0].DR.numExecution + 1 == InstanceB[0].DR.numExecution);

	this->IDValueMapping1.clear();
	this->ArgValueMapping1.clear();
	this->IDMemMapping1.clear();

	this->IDValueMapping2.clear();
	this->ArgValueMapping2.clear();
	this->IDMemMapping2.clear();

	this->setLength1.clear();
	this->setLength2.clear();

	DecodeOneInstance(InstanceA, this->IDValueMapping1, this->ArgValueMapping1, this->IDMemMapping1);
	DecodeOneInstance(InstanceB, this->IDValueMapping2, this->ArgValueMapping2, this->IDMemMapping2);

	set<Value *> setMonitoredValue;
	CollectMonitoredValue(setMonitoredValue);

	map<Value*, double> ValueScoreMapping;
	CompMemSequence(ValueScoreMapping);
	CompValueSequence(ValueScoreMapping);
	CompSkipLoad(ValueScoreMapping, setMonitoredValue);

	size_t lengthA = GetMaxFromSet(this->setLength1);
	size_t lengthB = GetMaxFromSet(this->setLength2);

	size_t minLength = min(lengthA, lengthB);
	size_t maxLength = max(lengthA, lengthB);

	set<Value *>::iterator itSetBegin = setMonitoredValue.begin();
	set<Value *>::iterator itSetEnd   = setMonitoredValue.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		if(ValueScoreMapping.find(*itSetBegin) != ValueScoreMapping.end())
		{
			continue;
		}

		int iIndex = GetValueID(*itSetBegin);

		if(Instruction * pInst = dyn_cast<Instruction>(*itSetBegin))
		{
			if(pLoop->contains(pInst->getParent()))
			{
				continue;
			}

			if(this->MonitoredElems.MonitoredInst.find(iIndex) == this->MonitoredElems.MonitoredInst.end())
			{
				continue;
			}
		}

		if(isa<Argument>(*itSetBegin))
		{
			if(this->MonitoredElems.setMonitoredPara.find(iIndex) == this->MonitoredElems.setMonitoredPara.end() )
			{
				continue;
			}
		}

		if(CanSkipThisValue(*itSetBegin))
		{
			continue;
		}

		long lValue1;
		long lValue2;

		if(Argument * pArg = dyn_cast<Argument>(*itSetBegin))
		{
			if(this->ArgValueMapping1[iIndex].PR.Value == this->ArgValueMapping2[iIndex].PR.Value)
			{
				ValueScoreMapping[pArg] = 1;
				continue;
			}

			lValue1 = this->ArgValueMapping1[iIndex].PR.Value;
			lValue2 = this->ArgValueMapping2[iIndex].PR.Value;
		}
		else if(Instruction * pInst = dyn_cast<Instruction>(*itSetBegin))
		{
			if(this->IDValueMapping1[iIndex][0].IR.Value == this->IDValueMapping2[iIndex][0].IR.Value)
			{
				ValueScoreMapping[pInst] = 1;
				continue;
			}

			lValue1 = IDValueMapping1[iIndex][0].IR.Value;
			lValue2 = IDValueMapping2[iIndex][0].IR.Value;
		}

		if(OnlyControlInLoop(*itSetBegin, pLoop) && OnlyCompWithInteger(*itSetBegin, pLoop))
		{
			ValueScoreMapping[*itSetBegin] = min(lValue1, lValue2) * 1.0/max(lValue1, lValue2);
			continue;
		}

		if(minLength == 0)
		{
			ValueScoreMapping[*itSetBegin] = 0;
		}

		if(CompIterativeStart(*itSetBegin, lValue1, lValue2, ValueScoreMapping))
		{
			continue;
		}

		ValueScoreMapping[*itSetBegin] = 0;
	}

	map<Value*, double>::iterator itScoreMapBegin = ValueScoreMapping.begin();
	map<Value*, double>::iterator itScoreMapEnd   = ValueScoreMapping.end();

	double average = 0;

	for(; itScoreMapBegin != itScoreMapEnd; itScoreMapBegin ++ )
	{
		itScoreMapBegin->first->dump();
		errs() << itScoreMapBegin->second << "\n";
		average += itScoreMapBegin->second;
	}

	exit(0);


	average = average/ValueScoreMapping.size();

	if(minLength < 100 && maxLength/minLength >= 2)
	{
		return 0;
	}
	else if(maxLength < 10)
	{
		return 0;
	}
	else if(average > 0.9)
	{
		return 1;
	}
	else
	{
		return 0;
	}


}

bool CLCAL::runOnModule(Module& M)
{
	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	Function * pInnerFunction = SearchFunctionByName(M, strInnerFileName, strInnerFuncName, uInnerSrcLine);

	if(pInnerFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return true;
	}

	this->SE = &(getAnalysis<ScalarEvolution>(*pInnerFunction));
	this->DL = &(getAnalysis<DataLayout>());

	ParseInstFile(pInnerFunction, &M);

	this->pLI = &(getAnalysis<LoopInfo>(*pInnerFunction));

	if(strLoopHeader == "")
	{
		this->pLoop = SearchLoopByLineNo(pInnerFunction, pLI, uInnerSrcLine);
	}
	else
	{
		BasicBlock * pHeader = SearchBlockByName(pInnerFunction, strLoopHeader);
		if(pHeader == NULL)
		{
			errs() << "Cannot find the given loop header!\n";
			return true;
		}

		this->pLoop = pLI->getLoopFor(pHeader);
	}

	if(this->pLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return true;
	}

	vector<vector<LogRecord> > vecLogRecord;
	ParseTraceFile(vecLogRecord);
	BuildIDInstMapping(pInnerFunction);
	//CalMaxMinValue(vecLogRecord);
	
	size_t iIndex = 0;
	int count = 0;

	while(iIndex + 1 < vecLogRecord.size() )
	{
		count += CompInstancePair(vecLogRecord[iIndex], vecLogRecord[iIndex+1]);
		iIndex += 2;
	}

	errs() << "Redundancy: " << count << " / " << vecLogRecord.size()/2 << " == " << (count * 1.0 / (vecLogRecord.size()/2)) << "\n";

	FreeMemBuffer();

	return false;
}
