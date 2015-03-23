
#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Loop/Loop.h"
#include "Instrument/WLInstrument/WLInstrument.h"


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
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


static RegisterPass<WorklessInstrument> X(
		"workless-instrument",
		"workless instrument",
		true,
		true);

char WorklessInstrument::ID = 0;

void WorklessInstrument::getAnalysisUsage(AnalysisUsage &AU) const 
{
	//AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<DominatorTree>();
	AU.addRequired<LoopInfo>();
	
}

WorklessInstrument::WorklessInstrument(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	initializeDominatorTreePass(Registry);
	//initializePromotePassPass(Registry);
}

void WorklessInstrument::print(raw_ostream &O, const Module *M) const
{
	return;
}


void WorklessInstrument::SetupTypes(Module * pModule)
{
	this->VoidType = Type::getVoidTy(pModule->getContext());
	this->LongType = IntegerType::get(pModule->getContext(), 64); 
	this->IntType  = IntegerType::get(pModule->getContext(), 32);
	this->CharType = IntegerType::get(pModule->getContext(), 8);
	this->BoolType = IntegerType::get(pModule->getContext(), 1);

	this->VoidPointerType = PointerType::get(this->CharType, 0);
	this->CharStarType = PointerType::get(this->CharType, 0);

}

void WorklessInstrument::SetupConstants(Module * pModule)
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

void WorklessInstrument::SetupHooks(Module * pModule)
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

    ArgTypes.clear();
	this->getenv = pModule->getFunction("getenv");
	if(!this->getenv)
	{
		ArgTypes.push_back(this->CharStarType);
		FunctionType * getenv_FuncTy = FunctionType::get(this->CharStarType, ArgTypes, false);
		this->getenv = Function::Create(getenv_FuncTy, GlobalValue::ExternalLinkage, "getenv", pModule);
		this->getenv->setCallingConv(CallingConv::C);
	}

	this->function_atoi = pModule->getFunction("atoi");
	if(!this->function_atoi)
	{
		ArgTypes.clear();
		ArgTypes.push_back(this->CharStarType);
		FunctionType * atoi_FuncTy = FunctionType::get(this->IntType, ArgTypes, false);
		this->function_atoi = Function::Create(atoi_FuncTy, GlobalValue::ExternalLinkage, "atoi", pModule );
		this->function_atoi->setCallingConv(CallingConv::C);
	}

	this->printf = pModule->getFunction("printf");
	if(!this->printf)
	{
		ArgTypes.clear();
		ArgTypes.push_back(this->CharStarType);
		FunctionType * printf_FuncTy = FunctionType::get(this->IntType, ArgTypes, true);
		this->printf = Function::Create(printf_FuncTy, GlobalValue::ExternalLinkage, "printf", pModule);
		this->printf->setCallingConv(CallingConv::C);
	}

	this->func_llvm_memcpy = pModule->getFunction("llvm.memcpy.p0i8.p0i8.i64");
	if(!this->func_llvm_memcpy)
	{
		ArgTypes.clear();
		ArgTypes.push_back(this->CharStarType);
		ArgTypes.push_back(this->CharStarType);
		ArgTypes.push_back(this->LongType);
		ArgTypes.push_back(this->IntType);
		ArgTypes.push_back(this->BoolType);
		FunctionType * memcpy_funcTy = FunctionType::get(this->VoidType, ArgTypes, false);
		this->func_llvm_memcpy = Function::Create(memcpy_funcTy, GlobalValue::ExternalLinkage, "llvm.memcpy.p0i8.p0i8.i64", pModule);
		this->func_llvm_memcpy->setCallingConv(CallingConv::C);
	}

	AttributeSet func_llvm_memcpy_PAL;
	{
		SmallVector<AttributeSet, 4> Attrs;
		AttributeSet PAS;
		{
			AttrBuilder B;
			B.addAttribute(Attribute::NoCapture);
			PAS = AttributeSet::get(pModule->getContext(), 1U, B);
		}

		Attrs.push_back(PAS);
		{
			AttrBuilder B;
			B.addAttribute(Attribute::ReadOnly);
			B.addAttribute(Attribute::NoCapture);
			PAS = AttributeSet::get(pModule->getContext(), 2U, B);
		}

		Attrs.push_back(PAS);
		{
			AttrBuilder B;
			B.addAttribute(Attribute::NoUnwind);
			PAS = AttributeSet::get(pModule->getContext(), ~0U, B);
		}

		Attrs.push_back(PAS);
		func_llvm_memcpy_PAL = AttributeSet::get(pModule->getContext(), Attrs);
	}

	this->func_llvm_memcpy->setAttributes(func_llvm_memcpy_PAL);

	assert(pModule->getFunction("geo") == NULL);
	ArgTypes.clear();
	ArgTypes.push_back(this->IntType);
	FunctionType * geo_FuncTy = FunctionType::get(this->IntType, ArgTypes, false);
	this->geo = Function::Create(geo_FuncTy, GlobalValue::ExternalLinkage, "geo", pModule);
	this->geo->setCallingConv(CallingConv::C);

	assert(pModule->getFunction("InitHooks") == NULL);
	ArgTypes.clear();
	//FunctionType * InitHooks_FuncTy = FunctionType::get(this->VoidType, ArgTypes, false);
	FunctionType * InitHooks_FuncTy = FunctionType::get(this->CharStarType, ArgTypes, false);
	this->InitHooks = Function::Create(InitHooks_FuncTy, GlobalValue::ExternalLinkage, "InitHooks", pModule);
	this->InitHooks->setCallingConv(CallingConv::C);
}


void WorklessInstrument::SetupGlobals(Module * pModule)
{
	assert(pModule->getGlobalVariable("SAMPLE_RATE")==NULL);
	this->SAMPLE_RATE = new GlobalVariable(*pModule, this->IntType, false, GlobalValue::CommonLinkage, 0, "SAMPLE_RATE");
	this->SAMPLE_RATE->setAlignment(4);
	this->SAMPLE_RATE->setInitializer(this->ConstantInt0);

	assert(pModule->getGlobalVariable("PC_SAMPLE_RATE")==NULL);
	this->PC_SAMPLE_RATE = new GlobalVariable(*pModule, this->CharStarType, false, GlobalValue::CommonLinkage, 0, "PC_SAMPLE_RATE");
	this->PC_SAMPLE_RATE->setAlignment(8);
	this->PC_SAMPLE_RATE->setInitializer(this->ConstantNULL);

	assert(pModule->getGlobalVariable("numGlobalCounter")==NULL);
	this->numGlobalCounter = new GlobalVariable( *pModule , this->LongType, false, GlobalValue::ExternalLinkage, 0, "numGlobalCounter");
	this->numGlobalCounter->setAlignment(8);
	this->numGlobalCounter->setInitializer(this->ConstantLong0);

/*
	assert(pModule->getGlobalVariable("numInstances")==NULL);
	this->numInstances = new GlobalVariable(*pModule, this->LongType, false, GlobalVariable::ExternalLinkage, 0, "numInstances");
	this->numInstances->setAlignment(8);
	this->numInstances->setInitializer(this->ConstantLong0);
*/
	assert(pModule->getGlobalVariable("CURRENT_SAMPLE") == NULL);
	this->CURRENT_SAMPLE = new GlobalVariable(*pModule, this->LongType, false, GlobalValue::ExternalLinkage, 0, "CURRENT_SAMPLE");
	this->CURRENT_SAMPLE->setAlignment(8);
	this->CURRENT_SAMPLE->setInitializer(this->ConstantLong0);


	//"SAMPLE_RATE" string
	ArrayType* ArrayTy12 = ArrayType::get(IntegerType::get(pModule->getContext(), 8), 12);
	GlobalVariable * pArrayStr = new GlobalVariable(*pModule, ArrayTy12, true, GlobalValue::PrivateLinkage, 0, "");
	pArrayStr->setAlignment(1);  
	Constant * ConstArray = ConstantDataArray::getString(pModule->getContext(), "SAMPLE_RATE", true);
	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0); 
	vecIndex.push_back(this->ConstantInt0);
	this->SAMPLE_RATE_ptr = ConstantExpr::getGetElementPtr(pArrayStr, vecIndex);
	pArrayStr->setInitializer(ConstArray);

	//""
	ArrayType * ArrayTy17 = ArrayType::get(IntegerType::get(pModule->getContext(), 8), 17);
	pArrayStr = new GlobalVariable(*pModule, ArrayTy17, true, GlobalValue::PrivateLinkage, 0, "");
	pArrayStr->setAlignment(1);
	ConstArray = ConstantDataArray::getString(pModule->getContext(), "SAMPLE_RATE: %d\x0A", true);
	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	this->Output_Format_String = ConstantExpr::getGetElementPtr(pArrayStr, vecIndex);
	pArrayStr->setInitializer(ConstArray);	
}

void WorklessInstrument::CreateIfElseBlock(Loop * pLoop, vector<BasicBlock *> & vecAdded)
{
	BasicBlock * pPreHeader = pLoop->getLoopPreheader();
	BasicBlock * pHeader = pLoop->getHeader();
	Function * pInnerFunction = pPreHeader->getParent();
	Module * pModule = pPreHeader->getParent()->getParent();

	BasicBlock * pElseBody = NULL;
	TerminatorInst * pTerminator = NULL;

	BranchInst * pBranch = NULL;
	LoadInst * pLoad1 = NULL;
	LoadInst * pLoad2 = NULL;
	LoadInst * pLoadnumGlobalCounter = NULL;
	BinaryOperator * pAddOne = NULL;
	StoreInst * pStoreNew = NULL;
	CmpInst * pCmp = NULL;
	CallInst * pCall = NULL;
	StoreInst * pStore = NULL;
	AttributeSet emptySet;

	pTerminator = pPreHeader->getTerminator();
	pLoadnumGlobalCounter = new LoadInst(this->numGlobalCounter, "", false, pTerminator);
	pLoadnumGlobalCounter->setAlignment(8);
	pAddOne = BinaryOperator::Create(Instruction::Add, pLoadnumGlobalCounter, this->ConstantLong1, "add", pTerminator);
	pStoreNew = new StoreInst(pAddOne, this->numGlobalCounter, false, pTerminator);
	pStoreNew->setAlignment(8);

	pElseBody = BasicBlock::Create(pModule->getContext(), ".else.body.CPI", pInnerFunction, 0);

	pLoad2 = new LoadInst(this->CURRENT_SAMPLE, "", false, pTerminator);
	pLoad2->setAlignment(8);
	pCmp = new ICmpInst(pTerminator, ICmpInst::ICMP_SLT, pAddOne, pLoad2, "");
	pBranch = BranchInst::Create(pHeader, pElseBody, pCmp );
	ReplaceInstWithInst(pTerminator, pBranch);

	pLoad1 = new LoadInst(this->SAMPLE_RATE, "", false, pElseBody);
	pCall = CallInst::Create(this->geo, pLoad1, "", pElseBody);
  	pCall->setCallingConv(CallingConv::C);
  	pCall->setTailCall(false);
  	pCall->setAttributes(emptySet);

  	CastInst * pCast = CastInst::CreateIntegerCast(pCall, this->LongType, true, "", pElseBody);
  	//pBinary = BinaryOperator::Create(Instruction::Add, pLoad2, pCast, "add", pIfBody);
  	pStore = new StoreInst(pCast, this->CURRENT_SAMPLE, false, pElseBody);
  	pStore->setAlignment(8);

  	pStore = new StoreInst(this->ConstantLong0, this->numGlobalCounter, false, pElseBody);
  	pStore->setAlignment(8);

  	pLoad1 = new LoadInst(this->numInstances, "", false, pElseBody);
  	pLoad1->setAlignment(8);
  	pAddOne = BinaryOperator::Create(Instruction::Add, pLoad1, this->ConstantLong1, "add", pElseBody);
	pStore = new StoreInst(pAddOne, this->numInstances, false, pElseBody);
	pStore->setAlignment(8);

	vecAdded.push_back(pPreHeader);
	vecAdded.push_back(pElseBody);
}



void WorklessInstrument::RemapInstruction(Instruction *I, ValueToValueMapTy &VMap) 
{
	for (unsigned op = 0, E = I->getNumOperands(); op != E; ++op) 
	{
		Value *Op = I->getOperand(op);
		ValueToValueMapTy::iterator It = VMap.find(Op);
		if (It != VMap.end())
		{
			I->setOperand(op, It->second);
		}
	}

	if (PHINode *PN = dyn_cast<PHINode>(I)) 
	{
		for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) 
		{
			ValueToValueMapTy::iterator It = VMap.find(PN->getIncomingBlock(i));
			if (It != VMap.end())
				PN->setIncomingBlock(i, cast<BasicBlock>(It->second));
		}
	}
}


void WorklessInstrument::CloneInnerLoop(Loop * pLoop, vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap, set<BasicBlock *> & setCloned)
{
	Function * pFunction = pLoop->getHeader()->getParent();
	BasicBlock * pPreHeader = vecAdd[0];

	SmallVector<BasicBlock *, 4> ExitBlocks;
	pLoop->getExitBlocks(ExitBlocks);

	set<BasicBlock *> setExitBlocks;

	for(unsigned long i = 0; i < ExitBlocks.size(); i++)
	{
		setExitBlocks.insert(ExitBlocks[i]);
	}

	for(unsigned long i = 0; i < ExitBlocks.size(); i++ )
	{
		VMap[ExitBlocks[i]] = ExitBlocks[i];
	}

	vector<BasicBlock *> ToClone;
	vector<BasicBlock *> BeenCloned;

	
	//clone loop
	ToClone.push_back(pLoop->getHeader());

	while(ToClone.size()>0)
	{
		BasicBlock * pCurrent = ToClone.back();
		ToClone.pop_back();

		WeakVH & BBEntry = VMap[pCurrent];
		if (BBEntry)
		{
			continue;
		}

		BasicBlock * NewBB;
		BBEntry = NewBB = BasicBlock::Create(pCurrent->getContext(), "", pFunction);

		if(pCurrent->hasName())
		{
			NewBB->setName(pCurrent->getName() + ".CPI");
		}

		if(pCurrent->hasAddressTaken())
		{
			errs() << "hasAddressTaken branch\n" ;
			exit(0);
		}

		for(BasicBlock::const_iterator II = pCurrent->begin(); II != pCurrent->end(); ++II )
		{
			Instruction * NewInst = II->clone();
			if(II->hasName())
			{
				NewInst->setName(II->getName() + ".CPI");
			}
			VMap[II] = NewInst;
			NewBB->getInstList().push_back(NewInst);
		}

		const TerminatorInst *TI = pCurrent->getTerminator();
		for (unsigned i = 0, e = TI->getNumSuccessors(); i != e; ++i)
		{
			ToClone.push_back(TI->getSuccessor(i));
		}

		setCloned.insert(NewBB);
		BeenCloned.push_back(NewBB);
	}

	//remap value used inside loop
	vector<BasicBlock *>::iterator itVecBegin = BeenCloned.begin();
	vector<BasicBlock *>::iterator itVecEnd = BeenCloned.end();

	for(; itVecBegin != itVecEnd; itVecBegin ++)
	{
		for(BasicBlock::iterator II = (*itVecBegin)->begin(); II != (*itVecBegin)->end(); II ++ )
		{
			//II->dump();
			RemapInstruction(II, VMap);
		}
	}

	//add to the else if body
	BasicBlock * pElseBody = vecAdd[1];

	BasicBlock * pClonedHeader = cast<BasicBlock>(VMap[pLoop->getHeader()]);

	BranchInst::Create(pClonedHeader, pElseBody);

	//errs() << pPreHeader->getName() << "\n";
	for(BasicBlock::iterator II = pClonedHeader->begin(); II != pClonedHeader->end(); II ++ )
	{
		if(PHINode * pPHI = dyn_cast<PHINode>(II))
		{
			vector<int> vecToRemoved;
			for (unsigned i = 0, e = pPHI->getNumIncomingValues(); i != e; ++i) 
			{
				if(pPHI->getIncomingBlock(i) == pPreHeader)
				{
					pPHI->setIncomingBlock(i, pElseBody);
				}
			}
		}
	}

	set<BasicBlock *> setProcessedBlock;

	for(unsigned long i = 0; i < ExitBlocks.size(); i++ )
	{
		if(setProcessedBlock.find(ExitBlocks[i]) != setProcessedBlock.end() )
		{
			continue;
		}
		else
		{
			setProcessedBlock.insert(ExitBlocks[i]);
		}

		for(BasicBlock::iterator II = ExitBlocks[i]->begin(); II != ExitBlocks[i]->end(); II ++ )
		{
			if(PHINode * pPHI = dyn_cast<PHINode>(II))
			{
				unsigned numIncomming = pPHI->getNumIncomingValues();
				for(unsigned i = 0; i<numIncomming; i++)
				{
					BasicBlock * incommingBlock = pPHI->getIncomingBlock(i);
					if(VMap.find(incommingBlock) != VMap.end() )
					{
						Value * incommingValue = pPHI->getIncomingValue(i);

						if(VMap.find(incommingValue) != VMap.end() )
						{
							incommingValue = VMap[incommingValue];
						}

						pPHI->addIncoming(incommingValue, cast<BasicBlock>(VMap[incommingBlock]));

					}
				} 

			}
		}
	}
}

void WorklessInstrument::InstrumentWorkless0Star1(Module * pModule, Loop * pLoop)
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
		if(BB->getName().equals("entry"))
		{
			CallInst * pCall;
			StoreInst * pStore;

			Instruction * II = BB->begin();
			pCall = CallInst::Create(this->InitHooks, "", II);
			pCall->setCallingConv(CallingConv::C);
			pCall->setTailCall(false);
			AttributeSet emptySet;
			pCall->setAttributes(emptySet);

			pCall = CallInst::Create(this->getenv, this->SAMPLE_RATE_ptr, "", II);
			pCall->setCallingConv(CallingConv::C);
			pCall->setTailCall(false);
			AttributeSet AS;
			{
				SmallVector<AttributeSet, 4> Attrs;
				AttributeSet PAS;
				{
					AttrBuilder B;
					B.addAttribute(Attribute::NoUnwind);
					PAS = AttributeSet::get(pModule->getContext(), ~0U, B);
				}
				Attrs.push_back(PAS);
				AS = AttributeSet::get(pModule->getContext(), Attrs);
			}
			pCall->setAttributes(AS);

			pCall = CallInst::Create(this->function_atoi, pCall, "", II);
			pCall->setCallingConv(CallingConv::C);
			pCall->setTailCall(false);
			{
  				SmallVector<AttributeSet, 4> Attrs;
   				AttributeSet PAS;
    			{
    	 			AttrBuilder B;
     				B.addAttribute(Attribute::NoUnwind);
     				B.addAttribute(Attribute::ReadOnly);
     				PAS = AttributeSet::get(pModule->getContext(), ~0U, B);
    			}
   
   				Attrs.push_back(PAS);
   				AS = AttributeSet::get(pModule->getContext(), Attrs);
   
  			}
  			pCall->setAttributes(AS);

  			pStore = new StoreInst(pCall, this->SAMPLE_RATE, false, II);
  			pStore->setAlignment(4);

  			pCall = CallInst::Create(this->geo, pCall, "", II);
  			pCall->setCallingConv(CallingConv::C);
  			pCall->setTailCall(false);
  			pCall->setAttributes(emptySet);

  			CastInst * pCast = CastInst::CreateIntegerCast(pCall, this->LongType, true, "", II);
  			pStore = new StoreInst(pCast, this->CURRENT_SAMPLE, false, II);
  			pStore->setAlignment(8);

  			vector<Value *> vecParam;
  			vecParam.push_back(this->Output_Format_String);
  			vecParam.push_back(pCall);
  			pCall = CallInst::Create(this->printf, vecParam, "", II);
  			pCall->setCallingConv(CallingConv::C);
  			pCall->setTailCall(false);
  			pCall->setAttributes(emptySet);
  			break;
		}
	}

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



	BasicBlock * pHeader = pLoop->getHeader();
	set<BasicBlock *> setExitBlock;
	CollectExitBlock(pLoop, setExitBlock);

	vector<BasicBlock *> vecAdded;
	CreateIfElseBlock(pLoop, vecAdded);

	ValueToValueMapTy  VMap;
	set<BasicBlock *> setCloned;
	CloneInnerLoop(pLoop, vecAdded, VMap, setCloned);

	BasicBlock * pPreHeader = vecAdded[1];
	pLoad = new LoadInst(this->numIterations, "", false, pPreHeader->getTerminator());
	pLoad->setAlignment(8);

	BasicBlock * pClonedHeader = cast<BasicBlock>(VMap[pHeader]);

	set<BasicBlock *> setPredBlocks;

	for(pred_iterator PI = pred_begin(pClonedHeader), E = pred_end(pClonedHeader); PI != E; ++PI)
	{
		setPredBlocks.insert(*PI);
	}

	PHINode * pNew = PHINode::Create(pLoad->getType(), setPredBlocks.size(), "numIterations", pClonedHeader->getFirstInsertionPt());
	pAdd = BinaryOperator::Create(Instruction::Add, pNew, this->ConstantLong1, "add", pClonedHeader->getFirstInsertionPt());

	set<BasicBlock *>::iterator itSetBegin = setPredBlocks.begin();
	set<BasicBlock *>::iterator itSetEnd   = setPredBlocks.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		if((*itSetBegin) == pPreHeader)
		{
			pNew->addIncoming(pLoad, pPreHeader);
		}
		else
		{
			pNew->addIncoming(pAdd, *itSetBegin);
		}
	}


	itSetBegin = setExitBlock.begin();
	itSetEnd   = setExitBlock.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		SmallVector<BasicBlock*, 8> LoopBlocks;

		for(pred_iterator PI = pred_begin(*itSetBegin), E = pred_end(*itSetBegin); PI != E; ++PI)
		{
			if(setCloned.find(*PI) != setCloned.end())
			{
				LoopBlocks.push_back(*PI);
			}
		}

		BasicBlock * NewExitBB = SplitBlockPredecessors(*itSetBegin, LoopBlocks, ".WL.loopexit", this);

		pStore = new StoreInst(pAdd, this->numIterations, false, NewExitBB->getFirstInsertionPt());
		pStore->setAlignment(8);
	}

	pPreHeader->getParent()->dump();

}

//void WorklessInstrument::InstrumentWorkless0Star1OPT(Module * pModule, Loop * pLoop)
//{
	/*
	Function * 


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
		}
	}
	*/

//}



void WorklessInstrument::InstrumentWorkless0Or1Star(Module * pModule, Loop * pLoop, set<string> & setWorkingBlocks)
{
	LoadInst * pLoad0 = NULL;
	LoadInst * pLoad1 = NULL;
	//BinaryOperator* pAdd = NULL;
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
	}

	for (Function::iterator BB = pMain->begin(); BB != pMain->end(); ++BB) 
	{
		if(BB->getName().equals("entry"))
		{
			CallInst * pCall;
			StoreInst * pStore;

			Instruction * II = BB->begin();
			pCall = CallInst::Create(this->InitHooks, "", II);
			pCall->setCallingConv(CallingConv::C);
			pCall->setTailCall(false);
			AttributeSet emptySet;
			pCall->setAttributes(emptySet);

			pCall = CallInst::Create(this->getenv, this->SAMPLE_RATE_ptr, "", II);
			pCall->setCallingConv(CallingConv::C);
			pCall->setTailCall(false);
			AttributeSet AS;
			{
				SmallVector<AttributeSet, 4> Attrs;
				AttributeSet PAS;
				{
					AttrBuilder B;
					B.addAttribute(Attribute::NoUnwind);
					PAS = AttributeSet::get(pModule->getContext(), ~0U, B);
				}
				Attrs.push_back(PAS);
				AS = AttributeSet::get(pModule->getContext(), Attrs);
			}
			pCall->setAttributes(AS);

			pCall = CallInst::Create(this->function_atoi, pCall, "", II);
			pCall->setCallingConv(CallingConv::C);
			pCall->setTailCall(false);
			{
  				SmallVector<AttributeSet, 4> Attrs;
   				AttributeSet PAS;
    			{
    	 			AttrBuilder B;
     				B.addAttribute(Attribute::NoUnwind);
     				B.addAttribute(Attribute::ReadOnly);
     				PAS = AttributeSet::get(pModule->getContext(), ~0U, B);
    			}
   
   				Attrs.push_back(PAS);
   				AS = AttributeSet::get(pModule->getContext(), Attrs);
   
  			}
  			pCall->setAttributes(AS);

  			pStore = new StoreInst(pCall, this->SAMPLE_RATE, false, II);
  			pStore->setAlignment(4);

  			pCall = CallInst::Create(this->geo, pCall, "", II);
  			pCall->setCallingConv(CallingConv::C);
  			pCall->setTailCall(false);
  			pCall->setAttributes(emptySet);

  			CastInst * pCast = CastInst::CreateIntegerCast(pCall, this->LongType, true, "", II);
  			pStore = new StoreInst(pCast, this->CURRENT_SAMPLE, false, II);
  			pStore->setAlignment(8);

  			vector<Value *> vecParam;
  			vecParam.push_back(this->Output_Format_String);
  			vecParam.push_back(pCall);
  			pCall = CallInst::Create(this->printf, vecParam, "", II);
  			pCall->setCallingConv(CallingConv::C);
  			pCall->setTailCall(false);
  			pCall->setAttributes(emptySet);
  			break;
		}
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

	Function * pFunction = pLoop->getHeader()->getParent();
	BasicBlock * pEntry = &(pFunction->getEntryBlock());

	AllocaInst * pAlloc = new AllocaInst(this->LongType, "bWorkingIteration.local", pEntry->getFirstInsertionPt());

	vector<BasicBlock *> vecWorkingBlock;
	
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); ++ BB)
	{
		if(setWorkingBlocks.find(BB->getName()) != setWorkingBlocks.end() )
		{
			vecWorkingBlock.push_back(BB);
		}
	}

	errs() << "working block number: " << vecWorkingBlock.size() << "\n";

	BasicBlock * pHeader = pLoop->getHeader();
	set<BasicBlock *> setExitBlock;
	CollectExitBlock(pLoop, setExitBlock);

	vector<BasicBlock *> vecAdded;
	CreateIfElseBlock(pLoop, vecAdded);

	ValueToValueMapTy  VMap;
	set<BasicBlock *> setCloned;
	CloneInnerLoop(pLoop, vecAdded, VMap, setCloned);

	//BasicBlock * pPreHeader = vecAdded[0];
	BasicBlock * pElseBody = vecAdded[1];
	
	vector<BasicBlock *>::iterator itVecBegin = vecWorkingBlock.begin();
	vector<BasicBlock *>::iterator itVecEnd   = vecWorkingBlock.end();

	for(; itVecBegin != itVecEnd; itVecBegin++ )
	{
		BasicBlock * pClonedBlock = cast<BasicBlock>(VMap[*itVecBegin]);
		pStore = new StoreInst(this->ConstantLong1, pAlloc, false, pClonedBlock->getFirstInsertionPt());
		pStore->setAlignment(8);
		pClonedBlock->dump();
	}


	pStore = new StoreInst(this->ConstantLong0, pAlloc, false, pElseBody->getTerminator());
	pStore->setAlignment(8);

	pLoad0 = new LoadInst(this->numIterations, "", false, pElseBody->getTerminator());
	pLoad0->setAlignment(8);

	pLoad1 = new LoadInst(this->numWorkingIterations, "", false, pElseBody->getTerminator());
	pLoad1->setAlignment(8);  

	BasicBlock * pClonedHeader = cast<BasicBlock>(VMap[pHeader]);

	set<BasicBlock *> setPredBlocks;

	for(pred_iterator PI = pred_begin(pClonedHeader), E = pred_end(pClonedHeader); PI != E; ++PI)
	{
		setPredBlocks.insert(*PI);
	}

	BasicBlock::iterator itInsert = pClonedHeader->getFirstInsertionPt();

	PHINode * pNewIterations = PHINode::Create(pLoad0->getType(), setPredBlocks.size(), "numIterations.2", itInsert);
	PHINode * pNewWorkingIterations = PHINode::Create(pLoad1->getType(), setPredBlocks.size(), "WorkingIterations.2", itInsert);

	BinaryOperator * pIterationAdd = BinaryOperator::Create(Instruction::Add, pNewIterations, this->ConstantLong1, "Iterations.add.2", itInsert);

	set<BasicBlock *>::iterator itSetBegin = setPredBlocks.begin();
	set<BasicBlock *>::iterator itSetEnd   = setPredBlocks.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		if((*itSetBegin) == pElseBody)
		{
			pNewIterations->addIncoming(pLoad0, pElseBody);
		}
		else
		{
			pNewIterations->addIncoming(pIterationAdd, *itSetBegin);
		}
	}

	pLoad0 = new LoadInst(pAlloc, "", false, itInsert);
	BinaryOperator * pWorkingAdd = 	BinaryOperator::Create(Instruction::Add, pNewWorkingIterations, pLoad0, "Working.add.2", itInsert);

	itSetBegin = setPredBlocks.begin();
	itSetEnd   = setPredBlocks.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		if((*itSetBegin) == pElseBody)
		{
			pNewWorkingIterations->addIncoming(pLoad1, pElseBody);
		}
		else
		{
			pNewWorkingIterations->addIncoming(pWorkingAdd, *itSetBegin);
		}
	}

	pStore = new StoreInst(this->ConstantLong0, pAlloc, false, itInsert);
	pStore->setAlignment(8);


	itSetBegin = setExitBlock.begin();
	itSetEnd   = setExitBlock.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		SmallVector<BasicBlock*, 8> LoopBlocks;

		for(pred_iterator PI = pred_begin(*itSetBegin), E = pred_end(*itSetBegin); PI != E; ++PI)
		{
			if(setCloned.find(*PI) != setCloned.end())
			{
				LoopBlocks.push_back(*PI);
			}
		}

		BasicBlock * NewExitBB = SplitBlockPredecessors(*itSetBegin, LoopBlocks, ".WL.loopexit", this);

		pStore = new StoreInst(pIterationAdd, this->numIterations, false, NewExitBB->getFirstInsertionPt());
		pStore->setAlignment(8);

		pStore = new StoreInst(pWorkingAdd, this->numWorkingIterations, false, NewExitBB->getFirstInsertionPt());
		pStore->setAlignment(8);
	}

	//pFunction->dump();

	DominatorTree * DT = &(getAnalysis<DominatorTree>(*pFunction));
	vector<AllocaInst *> vecAlloc;
	vecAlloc.push_back(pAlloc);
	PromoteMemToReg(vecAlloc, *DT);

	pFunction->dump();
}

void WorklessInstrument::ParseWorkingBlocks(set<string> & setWorkingBlocks)
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


bool WorklessInstrument::runOnModule(Module& M)
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
	SetupGlobals(&M);

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

	return true;
}

