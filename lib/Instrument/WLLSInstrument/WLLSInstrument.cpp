
#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Loop/Loop.h"
#include "Instrument/WLLSInstrument/WLLSInstrument.h"


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

#include <fstream>

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static cl::opt<unsigned> uSrcLine("noLine", 
					cl::desc("Source Code Line Number for the input Loop"), cl::Optional, 
					cl::value_desc("uSrcCodeLine"));


static cl::opt<std::string> strFileName("strFile", 
					cl::desc("File Name for the input Loop"), cl::Optional, 
					cl::value_desc("strFileName"));

static cl::opt<std::string> strFuncName("strFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strFuncName"));

static cl::opt<std::string> strMainName("strMain",
					cl::desc("Function Name for Main"), cl::Optional,
					cl::value_desc("strMainName"));

static cl::opt<std::string> strWorkingBlockFileName("strWorkingBlock",
					cl::desc("File contain working block list"), cl::Optional,
					cl::value_desc("strWorkingBlockFileName"));

static cl::opt<unsigned> uType( "noType",
					cl::desc("Workless Type"), cl::Optional, 
					cl::value_desc("uType") );


static RegisterPass<WorklessLSInstrument> X(
		"workless-instrument",
		"workless instrument",
		true,
		true);

char WorklessLSInstrument::ID = 0;

void WorklessLSInstrument::getAnalysisUsage(AnalysisUsage &AU) const 
{
	//AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<DominatorTree>();
	AU.addRequired<LoopInfo>();
	
}

WorklessLSInstrument::WorklessLSInstrument(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	initializeDominatorTreePass(Registry);
	//initializePromotePassPass(Registry);
}

void WorklessLSInstrument::print(raw_ostream &O, const Module *M) const
{
	return;
}


void WorklessLSInstrument::SetupTypes(Module * pModule)
{
	this->VoidType = Type::getVoidTy(pModule->getContext());
	this->LongType = IntegerType::get(pModule->getContext(), 64); 
	this->IntType  = IntegerType::get(pModule->getContext(), 32);
	this->CharType = IntegerType::get(pModule->getContext(), 8);
	this->BoolType = IntegerType::get(pModule->getContext(), 1);

	this->VoidPointerType = PointerType::get(this->CharType, 0);
	this->CharStarType = PointerType::get(this->CharType, 0);

}

void WorklessLSInstrument::SetupConstants(Module * pModule)
{
	this->ConstantInt0 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("0"), 10));
	this->ConstantInt1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("1"), 10));
	this->ConstantInt2 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("2"), 10));
	this->ConstantInt3 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("3"), 10));
	this->ConstantInt4 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("4"), 10));
	this->ConstantInt10 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("10"), 10));
	this->ConstantInt32 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("32"), 10));

	this->ConstantInt_1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("-1"), 10));

	this->ConstantLong_1 = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("-1"), 10)); 
	this->ConstantLong1  = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("1"), 10));;
	this->ConstantLong0  = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("0"), 10));;

	this->ConstantCharFalse = ConstantInt::get(pModule->getContext(), APInt(8, StringRef("0"), 10));
	this->ConstantCharTrue  = ConstantInt::get(pModule->getContext(), APInt(8, StringRef("1"), 10));

	this->ConstantBoolFalse = ConstantInt::get(pModule->getContext(), APInt(1, StringRef("0"), 10));
	this->ConstantBoolTrue  = ConstantInt::get(pModule->getContext(), APInt(1, StringRef("1"), 10));


	this->ConstantNULL = ConstantPointerNull::get(this->CharStarType);
	
}

void WorklessLSInstrument::SetupHooks(Module * pModule)
{
	assert(pModule->getGlobalVariable("numIterations")==NULL);
    assert(pModule->getGlobalVariable("numInstances")==NULL);
    assert(pModule->getGlobalVariable("numWorkingIterations")==NULL);
    assert(pModule->getGlobalVariable("bWorkingIteration")==NULL);

    assert(pModule->getFunction("PrintLoopInfo")==NULL);
    assert(pModule->getFunction("PrintIterationRatio")==NULL);


	this->numIterations = new GlobalVariable( *pModule , LongType, false, GlobalValue::ExternalLinkage, 0, "numIterations");
	this->numIterations->setAlignment(8);
	this->numIterations->setInitializer(this->ConstantLong0);

	this->numInstances = new GlobalVariable( *pModule , LongType, false, GlobalValue::ExternalLinkage, 0, "numInstances");
	this->numInstances->setAlignment(8);
	this->numInstances->setInitializer(this->ConstantLong0);

	this->numWorkingIterations = new GlobalVariable( *pModule , LongType, false, GlobalValue::ExternalLinkage, 0, "numWorkingIterations");
	this->numWorkingIterations->setAlignment(8);
	this->numWorkingIterations->setInitializer(this->ConstantLong0);

	
	this->bWorkingIteration = new GlobalVariable(*pModule, LongType, false, GlobalValue::ExternalLinkage, 0, "bWorkingIteration");
	this->bWorkingIteration->setAlignment(8);
	this->bWorkingIteration->setInitializer(this->ConstantLong0);

	vector<Type *> ArgTypes;
	ArgTypes.push_back(this->LongType);
	ArgTypes.push_back(this->LongType);
	FunctionType * PrintLoopInfoType = FunctionType::get(this->VoidType, ArgTypes, false);

	this->PrintLoopInfo = Function::Create(PrintLoopInfoType, GlobalValue::ExternalLinkage, "PrintLoopInfo", pModule);

	ArgTypes.clear();
	ArgTypes.push_back(this->LongType);
	ArgTypes.push_back(this->LongType);
    FunctionType * PrintWorkingRatioType = FunctionType::get(this->VoidType, ArgTypes, false);

    this->PrintWorkingRatio = Function::Create(PrintWorkingRatioType, GlobalValue::ExternalLinkage, "PrintWorkingRatio", pModule);
}


void WorklessLSInstrument::InstrumentWorkless0Star1(Module * pModule, Loop * pLoop)
{
	Function * pMain = NULL;

	if(strMainName != "" )
	{
		pMain = pModule->getFunction(strMainName.c_str());
	}
	else
	{
		pMain = pModule->getFunction("main");
	}

	LoadInst * pLoad;
	BinaryOperator* pAdd = NULL;
	StoreInst * pStore = NULL;

	for (Function::iterator BB = pMain->begin(); BB != pMain->end(); ++BB) 
	{
		for (BasicBlock::iterator Ins = BB->begin(); Ins != BB->end(); ++Ins) 
		{
			if (isa<ReturnInst>(Ins) || isa<ResumeInst>(Ins)) 
			{
				vector<Value*> vecParams;
				pLoad = new LoadInst(numIterations, "", false, Ins); 
				pLoad->setAlignment(8); 
				vecParams.push_back(pLoad);
				pLoad = new LoadInst(numInstances, "", false, Ins); 
				pLoad->setAlignment(8);
				vecParams.push_back(pLoad);
				
				CallInst* pCall = CallInst::Create(this->PrintLoopInfo, vecParams, "", Ins);
				pCall->setCallingConv(CallingConv::C);
				pCall->setTailCall(false);
				AttributeSet aSet;
				pCall->setAttributes(aSet);
			}
			else if(isa<CallInst>(Ins) || isa<InvokeInst>(Ins))
			{
				CallSite cs(Ins);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				if(pCalled->getName() == "exit" || pCalled->getName() == "_ZL9mysql_endi")
				{
					vector<Value*> vecParams;
					pLoad = new LoadInst(numIterations, "", false, Ins); 
					pLoad->setAlignment(8); 
					vecParams.push_back(pLoad);
					pLoad = new LoadInst(numInstances, "", false, Ins); 
					pLoad->setAlignment(8);
					vecParams.push_back(pLoad);
				
					CallInst* pCall = CallInst::Create(this->PrintLoopInfo, vecParams, "", Ins);
					pCall->setCallingConv(CallingConv::C);
					pCall->setTailCall(false);
					AttributeSet aSet;
					pCall->setAttributes(aSet);
				}
			}
		}
	}

	BasicBlock * pPreHeader = pLoop->getLoopPreheader();
	
	assert(pPreHeader != NULL);


	pLoad = new LoadInst(this->numInstances, "", false, pPreHeader->getTerminator());
	pLoad->setAlignment(8);
	pAdd = BinaryOperator::Create(Instruction::Add, pLoad, this->ConstantLong1, "add", pPreHeader->getTerminator());
	pStore = new StoreInst(pAdd, this->numInstances, false, pPreHeader->getTerminator());
	pStore->setAlignment(8);

	BasicBlock * pHeader = pLoop->getHeader();
	pLoad = new LoadInst(this->numIterations, "", false, pHeader->getTerminator());
	pLoad->setAlignment(8);
	pAdd = BinaryOperator::Create(Instruction::Add, pLoad, this->ConstantLong1, "add", pHeader->getTerminator());
	pStore = new StoreInst(pAdd, this->numIterations, false, pHeader->getTerminator());
	pStore->setAlignment(8);


	
}



void WorklessLSInstrument::InstrumentWorkless0Or1Star(Module * pModule, Loop * pLoop, set<string> & setWorkingBlocks)
{
	LoadInst * pLoad0 = NULL;
	LoadInst * pLoad1 = NULL;
	BinaryOperator* pAdd = NULL;
	StoreInst * pStore = NULL;
	CallInst * pCall = NULL;

	Function * pMain = NULL;

	if(strMainName != "" )
	{
		pMain = pModule->getFunction(strMainName.c_str());
	}
	else
	{
		pMain = pModule->getFunction("main");
		//pMain->dump();
	}

	for (Function::iterator BB = pMain->begin(); BB != pMain->end(); ++BB) 
	{
		for (BasicBlock::iterator Ins = BB->begin(); Ins != BB->end(); ++Ins) 
		{
			if (isa<ReturnInst>(Ins) || isa<ResumeInst>(Ins)) 
			{
				vector<Value*> vecParams;
				pLoad0 = new LoadInst(numIterations, "", false, Ins); 
				pLoad0->setAlignment(8); 
				vecParams.push_back(pLoad0);
				pLoad1 = new LoadInst(numInstances, "", false, Ins); 
				pLoad1->setAlignment(8);
				vecParams.push_back(pLoad1);
				
				pCall = CallInst::Create(this->PrintLoopInfo, vecParams, "", Ins);
				pCall->setCallingConv(CallingConv::C);
				pCall->setTailCall(false);
				AttributeSet aSet;
				pCall->setAttributes(aSet);

				vecParams.clear();
				pLoad0 = new LoadInst(numIterations, "", false, Ins); 
				pLoad0->setAlignment(8); 
				vecParams.push_back(pLoad0);
				pLoad1 = new LoadInst(numWorkingIterations, "", false, Ins); 
				pLoad1->setAlignment(8);
				vecParams.push_back(pLoad1);


				pCall = CallInst::Create(PrintWorkingRatio, vecParams, "", Ins);
				pCall->setCallingConv(CallingConv::C);
				pCall->setTailCall(false);
				pCall->setAttributes(aSet);
			}
			else if(isa<CallInst>(Ins) || isa<InvokeInst>(Ins))
			{
				CallSite cs(Ins);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				if(pCalled->getName() == "exit" || pCalled->getName() == "_ZL9mysql_endi")
				{
					vector<Value*> vecParams;
					pLoad0 = new LoadInst(numIterations, "", false, Ins);
					pLoad0->setAlignment(8); 
					vecParams.push_back(pLoad0);
					pLoad1 = new LoadInst(numInstances, "", false, Ins); 
					pLoad1->setAlignment(8);
					vecParams.push_back(pLoad1);

					pCall = CallInst::Create(this->PrintLoopInfo, vecParams, "", Ins);
					pCall->setCallingConv(CallingConv::C);
					pCall->setTailCall(false);
					AttributeSet aSet;
					pCall->setAttributes(aSet);

					vecParams.clear();
					pLoad0 = new LoadInst(numIterations, "", false, Ins); 
					pLoad0->setAlignment(8); 
					vecParams.push_back(pLoad0);
					pLoad1 = new LoadInst(numWorkingIterations, "", false, Ins); 
					pLoad1->setAlignment(8);
					vecParams.push_back(pLoad1);

					pCall = CallInst::Create(PrintWorkingRatio, vecParams, "", Ins);
					pCall->setCallingConv(CallingConv::C);
					pCall->setTailCall(false);
					pCall->setAttributes(aSet);
				}
			}
		}
	}

	vector<BasicBlock *> vecWorkingBlock;
	Function * pFunction = pLoop->getHeader()->getParent();
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); ++ BB)
	{
		if(setWorkingBlocks.find(BB->getName()) != setWorkingBlocks.end() )
		{
			vecWorkingBlock.push_back(BB);
		}
	}

	vector<BasicBlock *>::iterator itVecBegin = vecWorkingBlock.begin();
	vector<BasicBlock *>::iterator itVecEnd   = vecWorkingBlock.end();

	for(; itVecBegin != itVecEnd; itVecBegin++ )
	{
		pStore = new StoreInst(this->ConstantLong1, this->bWorkingIteration, false, (*itVecBegin)->getTerminator());
		pStore->setAlignment(8);
	}

	BasicBlock * pPreHeader = pLoop->getLoopPreheader();
	assert(pPreHeader != NULL);

	pLoad0 = new LoadInst(this->numInstances, "", false, pPreHeader->getTerminator());
	pLoad0->setAlignment(8);
	pAdd = BinaryOperator::Create(Instruction::Add, pLoad0, this->ConstantLong1, "add", pPreHeader->getTerminator());
	pStore = new StoreInst(pAdd, this->numInstances, false, pPreHeader->getTerminator());
	pStore->setAlignment(8);
	pStore = new StoreInst(this->ConstantLong0, this->bWorkingIteration, false, pPreHeader->getTerminator());
	pStore->setAlignment(8);


	BasicBlock * pHeader = pLoop->getHeader();
	pLoad0 = new LoadInst(this->numIterations, "", false, pHeader->getTerminator());
	pLoad0->setAlignment(8);
	pAdd = BinaryOperator::Create(Instruction::Add, pLoad0, this->ConstantLong1, "add", pHeader->getTerminator());
	pStore = new StoreInst(pAdd, this->numIterations, false, pHeader->getTerminator());
	pStore->setAlignment(8);

	pLoad0 = new LoadInst(this->bWorkingIteration, "", false, pHeader->getTerminator() );
	pLoad0->setAlignment(8);

	pLoad1 = new LoadInst(this->numWorkingIterations, "", false, pHeader->getTerminator());
	pLoad1->setAlignment(8);  
	pAdd = BinaryOperator::Create(Instruction::Add, pLoad0, pLoad1, "add", pHeader->getTerminator());
	pStore = new StoreInst(pAdd, this->numWorkingIterations, false, pHeader->getTerminator());
	pStore->setAlignment(8);

	pStore = new StoreInst(this->ConstantLong0, this->bWorkingIteration, false, pHeader->getTerminator());
	pStore->setAlignment(8);


}

void WorklessLSInstrument::ParseWorkingBlocks(set<string> & setWorkingBlocks)
{
	string line;
	ifstream ifile(strWorkingBlockFileName.c_str());
	if (ifile.is_open())
	{
		while(getline(ifile, line))
		{
			if(line[0] == '=')
			{
				line = line.substr(1, line.size()-1);
				setWorkingBlocks.insert(line);
			}
		}

		ifile.close();
	}

	set<string>::iterator itSetBegin = setWorkingBlocks.begin();
	set<string>::iterator itSetEnd   = setWorkingBlocks.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		errs() << *itSetBegin << "\n";
	}
}


bool WorklessLSInstrument::runOnModule(Module& M)
{
	
	Function * pFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);
	if(pFunction == NULL)
	{
		errs() << "Cannot find the input function\n";
		return false;
	}

	LoopInfo *pLoopInfo = &(getAnalysis<LoopInfo>(*pFunction));
	Loop * pLoop = SearchLoopByLineNo(pFunction, pLoopInfo, uSrcLine);

	if(pLoop == NULL)
	{
		errs() << "Cannot find the input loop\n";
		return false;
	}

	SetupTypes(&M);
	SetupConstants(&M);
	SetupHooks(&M);

	BasicBlock * pHeader = pLoop->getHeader();

	LoopSimplify(pLoop, this);

	pLoop = pLoopInfo->getLoopFor(pHeader);

	if(uType == 0)
	{

	}
	else if(uType == 1)
	{
		InstrumentWorkless0Star1(&M, pLoop);
	}
	else if(uType == 2)
	{
		set<string> setWorkingBlocks;
		ParseWorkingBlocks(setWorkingBlocks);
		InstrumentWorkless0Or1Star(&M, pLoop, setWorkingBlocks);
	}
	else
	{
		errs() << "Wrong Workless Instrument Type\n";
	}

	//pFunction->dump();

	return true;
}

