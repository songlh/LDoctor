#include <fstream>
#include <iostream>
#include <string>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sstream>


#include "llvm-Commons/Search/Search.h"
#include "Instrument/CLInstrument/CLInstrument.h"


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;

static cl::opt<unsigned> uInnerSrcLine("noInnerLine", 
					cl::desc("Source Code Line Number for Inner Loop"), cl::Optional, 
					cl::value_desc("uInnerSrcCodeLine"));


static cl::opt<std::string> strInnerFileName("strInnerFile", 
					cl::desc("File Name for Inner Loop"), cl::Optional, 
					cl::value_desc("strInnerFileName"));

static cl::opt<std::string> strInnerFuncName("strInnerFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strInnerFuncName"));

static cl::opt<unsigned> uOuterSrcLine("noOuterLine", 
					cl::desc("Source Code Line Number for Outer Loop"), cl::Optional, 
					cl::value_desc("uSrcOuterCodeLine"));

static cl::opt<std::string> strOuterFileName("strOuterFile", 
					cl::desc("File Name for Outer Loop"), cl::Optional, 
					cl::value_desc("strOuterFileName"));

static cl::opt<std::string> strOuterFuncName("strOuterFunc", 
					cl::desc("Function Name for Outer Loop"), cl::Optional, 
					cl::value_desc("strOuterFuncName"));

static cl::opt<std::string> strMonitorInstFile("strInstFile",
					cl::desc("Monitored Insts File Name"), cl::Optional,
					cl::value_desc("strInstFile"));

static RegisterPass<CrossLoopInstrument> X(
		"cross-loop-instrument",
		"cross loop instrument",
		true,
		true);

char CrossLoopInstrument::ID = 0;

void CrossLoopInstrument::getAnalysisUsage(AnalysisUsage &AU) const 
{
	//AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<DominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	
}

CrossLoopInstrument::CrossLoopInstrument(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	initializeDominatorTreePass(Registry);
}

void CrossLoopInstrument::print(raw_ostream &O, const Module *M) const
{
	return;
}

void CrossLoopInstrument::SetupTypes(Module * pModule)
{
	this->VoidType = Type::getVoidTy(pModule->getContext());
	this->LongType = IntegerType::get(pModule->getContext(), 64); 
	this->IntType  = IntegerType::get(pModule->getContext(), 32);
	this->CharType = IntegerType::get(pModule->getContext(), 8);
	this->BoolType = IntegerType::get(pModule->getContext(), 1);

	this->VoidPointerType = PointerType::get(this->CharType, 0);
	this->CharStarType = PointerType::get(this->CharType, 0);

}

void CrossLoopInstrument::SetupConstants(Module * pModule)
{
	this->ConstantInt0 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("0"), 10));
	this->ConstantInt1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("1"), 10));
	this->ConstantInt2 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("2"), 10));
	this->ConstantInt3 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("3"), 10));
	this->ConstantInt4 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("4"), 10));
	this->ConstantInt10 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("10"), 10));
	this->ConstantInt32 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("32"), 10));

	this->ConstantInt_1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("-1"), 10));

	this->ConstantIntFalse = ConstantInt::get(pModule->getContext(), APInt(1, StringRef("0"), 10));


	this->ConstantNULL = ConstantPointerNull::get(this->CharStarType);
	
}

void CrossLoopInstrument::SetupStruct(Module * pModule)
{
	vector<Type *> struct_fields;
	assert(pModule->getTypeByName("struct.stLoadRecord") == NULL);
	this->struct_stLoadRecord = StructType::create(pModule->getContext(), "struct.stLoadRecord");
	struct_fields.push_back(this->IntType);
	struct_fields.push_back(this->LongType);
	struct_fields.push_back(this->LongType);
	if(this->struct_stLoadRecord->isOpaque())
	{
		this->struct_stLoadRecord->setBody(struct_fields, false);
	}

	assert(pModule->getTypeByName("struct.stStoreRecord") == NULL);
	this->struct_stStoreRecord = StructType::create(pModule->getContext(), "struct.stStoreRecord");
	struct_fields.clear();
	struct_fields.push_back(this->IntType);
	struct_fields.push_back(this->LongType);
	struct_fields.push_back(this->LongType);
	if(this->struct_stStoreRecord->isOpaque())
	{
		this->struct_stStoreRecord->setBody(struct_fields, false);
	}

	assert(pModule->getTypeByName("struct.stInstRecord") == NULL);
	this->struct_stInstRecord = StructType::create(pModule->getContext(), "struct.stInstRecord");
	struct_fields.clear();
	struct_fields.push_back(this->IntType);
	struct_fields.push_back(this->LongType);
	if(this->struct_stInstRecord->isOpaque())
	{
		this->struct_stInstRecord->setBody(struct_fields, false);
	}

	assert(pModule->getTypeByName("struct.stParaRecord") == NULL);
	this->struct_stParaRecord = StructType::create(pModule->getContext(), "struct.stParaRecord");
	struct_fields.clear();
	struct_fields.push_back(this->IntType);
	struct_fields.push_back(this->LongType);
	if(this->struct_stParaRecord->isOpaque())
	{
		this->struct_stParaRecord->setBody(struct_fields, false);
	}

	assert(pModule->getTypeByName("struct.stDelimiterRecord") == NULL);
	this->struct_stDelimiterRecord = StructType::create(pModule->getContext(), "struct.stDelimiterRecord");
	struct_fields.clear();
	struct_fields.push_back(this->LongType);
	if(this->struct_stDelimiterRecord->isOpaque())
	{
		this->struct_stDelimiterRecord->setBody(struct_fields, false);
	}

	assert(pModule->getTypeByName("struct.stLogRecord") == NULL);
	this->struct_stLogRecord = StructType::create(pModule->getContext(), "struct.stLogRecord");
	struct_fields.clear();
	struct_fields.push_back(this->IntType);

	assert(pModule->getTypeByName("union.anon.CPI") == NULL);
	this->union_anon_CPI = StructType::create(pModule->getContext(), "union.anon.CPI");
	vector<Type *> union_fields;
	union_fields.push_back(this->struct_stLoadRecord);
	if(this->union_anon_CPI->isOpaque())
	{
		this->union_anon_CPI->setBody(union_fields, false);
	}
	struct_fields.push_back(this->union_anon_CPI);
	if(this->struct_stLogRecord->isOpaque())
	{	
		this->struct_stLogRecord->setBody(struct_fields, false);
	}
}



void CrossLoopInstrument::SetupHooks(Module * pModule)
{
	vector<Type*> ArgTypes;

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

	assert(pModule->getFunction("FinalizeMemHooks") == NULL);
	ArgTypes.clear();
	ArgTypes.push_back(this->IntType);
	FunctionType * Finalize_FuncTy = FunctionType::get(this->VoidType, ArgTypes, false);
	this->FinalizeMemHooks = Function::Create(Finalize_FuncTy, GlobalValue::ExternalLinkage, "FinalizeMemHooks", pModule);

}

void CrossLoopInstrument::SetupGlobals(Module * pModule)
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
	this->numGlobalCounter = new GlobalVariable( *pModule , this->IntType, false, GlobalValue::ExternalLinkage, 0, "numGlobalCounter");
	this->numGlobalCounter->setAlignment(8);
	this->numGlobalCounter->setInitializer(this->ConstantInt0);

	assert(pModule->getGlobalVariable("CURRENT_SAMPLE") == NULL);
	this->CURRENT_SAMPLE = new GlobalVariable(*pModule, this->IntType, false, GlobalValue::ExternalLinkage, 0, "CURRENT_SAMPLE");
	this->CURRENT_SAMPLE->setAlignment(4);
	this->CURRENT_SAMPLE->setInitializer(this->ConstantInt0);

	assert(pModule->getGlobalVariable("Record_CPI") == NULL);
	this->Record_CPI = new GlobalVariable(*pModule, this->struct_stLogRecord, false, GlobalValue::ExternalLinkage, 0, "Record_CPI");
	this->Record_CPI->setAlignment(8);
	ConstantAggregateZero * const_struct = ConstantAggregateZero::get(this->struct_stLogRecord);
	this->Record_CPI->setInitializer(const_struct);

	assert(pModule->getGlobalVariable("pcBuffer_CPI") == NULL);
	this->pcBuffer_CPI = new GlobalVariable(*pModule, this->CharStarType, false, GlobalValue::ExternalLinkage, 0, "pcBuffer_CPI");
	this->pcBuffer_CPI->setAlignment(8);
	this->pcBuffer_CPI->setInitializer(this->ConstantNULL);

	assert(pModule->getGlobalVariable("iRecordSize_CPI") == NULL);
	this->iRecordSize_CPI = new GlobalVariable(*pModule, this->IntType, false, GlobalValue::ExternalLinkage, 0, "iRecordSize_CPI");
	this->iRecordSize_CPI->setAlignment(4);
	this->iRecordSize_CPI->setInitializer(this->ConstantInt0);

	assert(pModule->getGlobalVariable("iBufferIndex_CPI") == NULL);
	this->iBufferIndex_CPI = new GlobalVariable(*pModule, this->IntType, false, GlobalValue::ExternalLinkage, 0, "iBufferIndex_CPI");
	this->iBufferIndex_CPI->setAlignment(4);
	this->iBufferIndex_CPI->setInitializer(this->ConstantInt0);

	
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

void CrossLoopInstrument::InlineHookPara(Argument * pArg, Instruction * II)
{

	StoreInst * pStore;
	Constant * const_ptr;
	CastInst * pCast;
	Function * pFunction = pArg->getParent();

	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(this->ConstantInt3, const_ptr, false, II);
	pStore->setAlignment(4);

	int iID = 0;

	MDNode *Node = pFunction->begin()->begin()->getMetadata("func_id");
	if(Node!=NULL)
	{
		assert(Node->getNumOperands() == 1);
		ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
		assert(CI);
		iID = CI->getZExtValue();
	}

	iID = iID * 10 + pArg->getArgNo();
	ConstantInt * pID = ConstantInt::get(this->IntType, iID, false);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Constant * ParaRecord_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	PointerType * stParaRecord_PT = PointerType::get(this->struct_stParaRecord, 0);
	ParaRecord_ptr = ConstantExpr::getCast(Instruction::BitCast, ParaRecord_ptr, stParaRecord_PT);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
	pStore = new StoreInst(pID, const_ptr, false, II);
	pStore->setAlignment(4);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pArg->getType()))
	{
		//errs() << "IntegerType: " << pIntType->getBitWidth() << "\n";
		if(pIntType->getBitWidth() == 64)
		{
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt1);
			const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
			pStore = new StoreInst(pArg, const_ptr, false, II);
			pStore->setAlignment(8);
		}
		else
		{
			pCast = CastInst::CreateIntegerCast(pArg, this->LongType, true, "", II);
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt1);
			const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
			pStore = new StoreInst(pCast, const_ptr, false, II);
			pStore->setAlignment(8);
		}
	}

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(4);
	CastInst * pCastIndex   = new SExtInst(pLoadIndex, this->LongType, "", II);
	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pCastIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(4);
	CastInst * pCastSize = new SExtInst(pLoadRecordSize, this->LongType, "", II);

	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pCastSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(4);

}


void CrossLoopInstrument::InlineHookLoad(LoadInst * pLoad)
{
	BasicBlock::iterator II = pLoad;
	II ++;
	Constant * const_ptr;
	StoreInst * pStore;
	CastInst * pCast1 = new PtrToIntInst(pLoad->getPointerOperand(), this->LongType, "", II);
	CastInst * pCast2 = NULL;

	if(isa<IntegerType>(pLoad->getType()))
	{
		pCast2 = CastInst::CreateIntegerCast(pLoad, this->LongType, true, "", II);
	}
	else if(isa<PointerType>(pLoad->getType()))
	{
		pCast2 = new PtrToIntInst(pLoad, this->LongType, "", II);
	}


	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(this->ConstantInt0, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(pCast1, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(pCast2, const_ptr, false, II);
	pStore->setAlignment(8);

	MDNode *Node = pLoad->getMetadata("ins_id");
	assert(Node);
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(4);
	CastInst * pCastIndex   = new SExtInst(pLoadIndex, this->LongType, "", II);
	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pCastIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(4);
	CastInst * pCastSize = new SExtInst(pLoadRecordSize, this->LongType, "", II);

	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pCastSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(4);

}


void CrossLoopInstrument::InlineHookInst(Instruction * pI, Instruction * II)
{
	MDNode *Node = pI->getMetadata("ins_id");
	assert(Node);
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
	CastInst * pCast;
	
	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Constant* const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	StoreInst * pStore = new StoreInst(this->ConstantInt2, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Constant * InstRecord_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	PointerType * stInstRecord_PT = PointerType::get( this->struct_stInstRecord, 0);
	InstRecord_ptr = ConstantExpr::getCast(Instruction::BitCast, InstRecord_ptr, stInstRecord_PT);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(InstRecord_ptr, vecIndex);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = ConstantExpr::getGetElementPtr(InstRecord_ptr, vecIndex);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pI->getType()))
	{
		if(pIntType->getBitWidth() != 64)
		{
			pCast = CastInst::CreateIntegerCast(pI, this->LongType, true, "", II);
			pStore = new StoreInst(pCast, const_ptr, false, II);
		}
		else
		{
			pStore = new StoreInst(pI, const_ptr, false, II);
		}
	}
	else if(isa<PointerType>(pI->getType()))
	{
		pCast = new PtrToIntInst(pI, this->LongType, "", II);
		pStore = new StoreInst(pCast, const_ptr, false, II);
	}

	
	pStore->setAlignment(8);

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(4);
	CastInst * pCastIndex   = new SExtInst(pLoadIndex, this->LongType, "", II);
	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pCastIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(4);
	CastInst * pCastSize = new SExtInst(pLoadRecordSize, this->LongType, "", II);

	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pCastSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(4);

}


void CrossLoopInstrument::InlineHookDelimit(Instruction * II)
{
	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Constant* const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	StoreInst * pStore = new StoreInst(this->ConstantInt4, const_ptr, false, II);
	pStore->setAlignment(4);

	LoadInst * pLoad = new LoadInst(this->numGlobalCounter, "", false, II);
	pLoad->setAlignment(4);
	CastInst * pCast = CastInst::CreateIntegerCast(pLoad, this->LongType, true, "", II);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Constant * DelimitRecord_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	PointerType * DelimitRecord_PT = PointerType::get(this->struct_stDelimiterRecord, 0);
	DelimitRecord_ptr = ConstantExpr::getCast(Instruction::BitCast, DelimitRecord_ptr, DelimitRecord_PT);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(DelimitRecord_ptr, vecIndex);

	pStore = new StoreInst(pCast, const_ptr, false, II);
	pStore->setAlignment(8);

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(4);
	CastInst * pCastIndex   = new SExtInst(pLoadIndex, this->LongType, "", II);
	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pCastIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(4);
	CastInst * pCastSize = new SExtInst(pLoadRecordSize, this->LongType, "", II);

	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pCastSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(4);

}


void CrossLoopInstrument::InstrumentMain(Module * pModule)
{
	Function * pFunctionMain = pModule->getFunction("main");
	assert(pFunctionMain != NULL);

	for(Function::iterator BB = pFunctionMain->begin(); BB != pFunctionMain->end(); BB ++)
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

			pStore = new StoreInst(pCall, this->pcBuffer_CPI, false, II);
			pStore->setAlignment(8);

			pStore = new StoreInst(this->ConstantInt32, this->iRecordSize_CPI, false, II);
			pStore->setAlignment(4);

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

  			//Multipled by 2
  			BinaryOperator * pMul = BinaryOperator::Create(Instruction::Mul, pCall, this->ConstantInt2, "", II);
  			pStore = new StoreInst(pMul, this->SAMPLE_RATE, false, II);
  			pStore->setAlignment(4);

  			pCall = CallInst::Create(this->geo, pMul, "", II);
  			pCall->setCallingConv(CallingConv::C);
  			pCall->setTailCall(false);
  			pCall->setAttributes(emptySet);

  			pStore = new StoreInst(pCall, this->CURRENT_SAMPLE, false, II);
  			pStore->setAlignment(4);

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

	for(Function::iterator BB = pFunctionMain->begin(); BB != pFunctionMain->end(); BB ++)
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++)
		{
			if(ReturnInst * pRet = dyn_cast<ReturnInst>(II))
			{
				
				LoadInst * pLoad = new LoadInst(this->iBufferIndex_CPI, "", false, pRet);
				pLoad->setAlignment(4);

				CallInst * pCall = CallInst::Create(this->FinalizeMemHooks, pLoad, "", pRet);
				pCall->setCallingConv(CallingConv::C);
				pCall->setTailCall(false);
				AttributeSet AS;
				pCall->setAttributes(AS);
			}
		}
	}

}


void CrossLoopInstrument::CollectInstrumentedInst(set<int> & setIndex, Loop * pLoop, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecOut)
{
	set<BasicBlock *> setLoopBlocks;
	for(Loop::block_iterator BB = pLoop->block_begin() ; BB != pLoop->block_end(); BB ++)
	{
		setLoopBlocks.insert(*BB);
	}

	Function * pFunction = (*(pLoop->block_begin()))->getParent();
	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			MDNode *Node = II->getMetadata("ins_id");
			if(!Node)
			{
				continue;
			}
			assert(Node->getNumOperands() == 1);
			ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
			assert(CI);
			if(setIndex.find(CI->getZExtValue()) != setIndex.end())
			{
				if(setLoopBlocks.find(BB) == setLoopBlocks.end() )
				{
					vecOut.push_back(II);
				}
				else
				{
					//II->dump();
					assert(isa<LoadInst>(II));
					vecLoad.push_back(cast<LoadInst>(II));					
				}
			}
		}
	}
}

void CrossLoopInstrument::InstrumentOuterLoop(Loop * pOuterLoop)
{
	BasicBlock * pHeader = pOuterLoop->getHeader();
	LoadInst * pLoadnumGlobalCounter = NULL;
	BinaryOperator * pAdd = NULL;
	StoreInst * pStore = NULL;

	pLoadnumGlobalCounter = new LoadInst(this->numGlobalCounter, "", false, pHeader->getTerminator());
	pLoadnumGlobalCounter->setAlignment(8);
	pAdd = BinaryOperator::Create(Instruction::Add, pLoadnumGlobalCounter, this->ConstantInt1, "add", pHeader->getTerminator());
	pStore = new StoreInst(pAdd, this->numGlobalCounter, false, pHeader->getTerminator());
	pStore->setAlignment(8);
}

BasicBlock * CrossLoopInstrument::SearchPostDominatorForLoop(Loop * pLoop,  PostDominatorTree * pPDT )
{
	//Function * pFunction = pLoop->getHeader()->getParent();
	SmallVector<BasicBlock *, 4> ExitBlocks;
	pLoop->getExitBlocks(ExitBlocks);

	if(ExitBlocks.size() == 1)
	{
		return ExitBlocks[0];
	}

	//errs() << ExitBlocks.size() << "\n";
	BasicBlock * pPostDominator = ExitBlocks[0];

	for(unsigned long i = 1; i < ExitBlocks.size(); i++ )
	{
		pPostDominator = pPDT->findNearestCommonDominator(pPostDominator, ExitBlocks[i]);
	}

	return pPostDominator;

}


void CrossLoopInstrument::CreateIfElseIfBlock(Loop * pInnerLoop, BasicBlock * pPostDominator, vector<BasicBlock *> & vecAdded)
{
	BasicBlock * pCondition1 = NULL;
	BasicBlock * pCondition2 = NULL;
	BasicBlock * pCondition3 = NULL;

	BasicBlock * pElseBody = NULL;
	BasicBlock * pIfBody = NULL;

	LoadInst * pLoad1 = NULL;
	LoadInst * pLoad2 = NULL;
	ICmpInst * pCmp = NULL; 
	BinaryOperator * pBinary = NULL;
	TerminatorInst * pTerminator = NULL;
	BranchInst * pBranch = NULL;
	StoreInst * pStore = NULL;
	CallInst * pCall = NULL;
	AttributeSet emptySet;

	Function * pInnerFunction = pPostDominator->getParent();
	Module * pModule = pInnerFunction->getParent();

	SmallVector<BasicBlock*, 8> OutsideBlocks;
	BasicBlock * pHeader = pInnerLoop->getHeader();
	for(pred_iterator PI = pred_begin(pHeader), PE = pred_end(pHeader); PI != PE; ++PI)
	{
		BasicBlock *P = *PI;
		if(!pInnerLoop->contains(P))
		{
			if(isa<IndirectBrInst>(P->getTerminator()))
			{
				errs() << "IndirectBrInst toward loop header\n";
				exit(0);
			}

			OutsideBlocks.push_back(P);
		}
	}

	if(!pHeader->isLandingPad())
	{
		pCondition1 = SplitBlockPredecessors(pHeader, OutsideBlocks, ".if1.CPI", this);
	}
	else
	{
		errs() << "Header isLandingPad!\n" ;
		exit(0);
	}

	pCondition2 = BasicBlock::Create(pModule->getContext(), ".if2.CPI", pInnerFunction, 0);
	pCondition3 = BasicBlock::Create(pModule->getContext(), ".if3.CPI", pInnerFunction, 0);

	pIfBody = BasicBlock::Create(pModule->getContext(), ".if.body.CPI", pInnerFunction, 0);
	pElseBody = BasicBlock::Create(pModule->getContext(), ".else.body.CPI", pInnerFunction, 0);

	pTerminator = pCondition1->getTerminator();

	if(!this->bGivenOuterLoop)
	{
		LoadInst * pLoadnumGlobalCounter = NULL;
		BinaryOperator * pAddOne = NULL;
		StoreInst * pStoreNew = NULL;

		pLoadnumGlobalCounter = new LoadInst(this->numGlobalCounter, "", false, pTerminator);
		pLoadnumGlobalCounter->setAlignment(8);
		pAddOne = BinaryOperator::Create(Instruction::Add, pLoadnumGlobalCounter, this->ConstantInt1, "add", pTerminator);
		pStoreNew = new StoreInst(pAddOne, this->numGlobalCounter, false, pTerminator);
		pStoreNew->setAlignment(8);
	}


	pLoad1 = new LoadInst(this->numGlobalCounter, "", false, pTerminator);
	pLoad1->setAlignment(4);
	pLoad2 = new LoadInst(this->CURRENT_SAMPLE, "", false, pTerminator);
	pLoad2->setAlignment(4);
	pCmp = new ICmpInst(pTerminator, ICmpInst::ICMP_NE, pLoad1, pLoad2, "");
	pBranch = BranchInst::Create(pCondition2, pElseBody, pCmp );
	ReplaceInstWithInst(pTerminator, pBranch);

	pBinary = BinaryOperator::Create(Instruction::Add, pLoad2, this->ConstantInt1, "", pCondition2);
	pCmp = new ICmpInst(*pCondition2, ICmpInst::ICMP_NE, pLoad1, pBinary, "");
	BranchInst::Create(pCondition3, pElseBody, pCmp, pCondition2);

	//condition3
	pBinary = BinaryOperator::Create(Instruction::Add, pLoad2, this->ConstantInt2, "", pCondition3);
	pCmp = new ICmpInst(*pCondition3, ICmpInst::ICMP_EQ, pLoad1, pBinary, "");
	BranchInst::Create(pIfBody, pHeader, pCmp, pCondition3);

	//
	pLoad1 = new LoadInst(this->SAMPLE_RATE, "", false, pIfBody);
	pCall = CallInst::Create(this->geo, pLoad1, "", pIfBody);
  	pCall->setCallingConv(CallingConv::C);
  	pCall->setTailCall(false);
  	pCall->setAttributes(emptySet);

  	pStore = new StoreInst(pCall, this->CURRENT_SAMPLE, false, pIfBody);
  	pStore->setAlignment(4);

  	pStore = new StoreInst(this->ConstantInt0, this->numGlobalCounter, false, pIfBody);
  	pStore->setAlignment(4);
  	BranchInst::Create(pHeader, pIfBody);

  	BranchInst::Create(pPostDominator, pElseBody);

	for(BasicBlock::iterator II = pHeader->begin(); II != pHeader->end(); II ++)
	{
		if(PHINode * pPHI = dyn_cast<PHINode>(II))
		{
			vector<pair<Value *, BasicBlock *> > vecToAdd;

			for (unsigned i = 0, e = pPHI->getNumIncomingValues(); i != e; ++i) 
			{
				if(pPHI->getIncomingBlock(i) == pCondition1)
				{
					pPHI->setIncomingBlock(i, pCondition3);
					pair<Value *, BasicBlock *> pairTmp;
					pairTmp.first = pPHI->getIncomingValue(i);
					pairTmp.second = pIfBody;
					vecToAdd.push_back(pairTmp);
				}
			}

			vector<pair<Value *, BasicBlock *> >::iterator itVecAddBegin = vecToAdd.begin();
			vector<pair<Value *, BasicBlock *> >::iterator itVecAddEnd = vecToAdd.end();

			for(; itVecAddBegin != itVecAddEnd; itVecAddBegin++ )
			{
				pPHI->addIncoming(itVecAddBegin->first, itVecAddBegin->second);
			}

		}
	}


	vecAdded.push_back(pCondition1);
	vecAdded.push_back(pCondition2);
	vecAdded.push_back(pCondition3);
	vecAdded.push_back(pIfBody);
	vecAdded.push_back(pElseBody);

	//pInnerFunction->dump();
	
}


void CrossLoopInstrument::RemapInstruction(Instruction *I, ValueToValueMapTy &VMap) 
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

void CrossLoopInstrument::CloneInnerLoop(Loop * pLoop, BasicBlock * pPostDominator, vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap)
{
	Function * pFunction = pPostDominator->getParent();
	BranchInst * pBranch;

	VMap[pPostDominator] = pPostDominator;

	vector<BasicBlock *> ToClone;
	vector<BasicBlock *> BeenCloned;

	set<BasicBlock *> setCloned;
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

		setCloned.insert(pCurrent);
		BeenCloned.push_back(NewBB);
	}

	//remap value used inside loop
	vector<BasicBlock *>::iterator itVecBegin = BeenCloned.begin();
	vector<BasicBlock *>::iterator itVecEnd = BeenCloned.end();


	for(; itVecBegin != itVecEnd; itVecBegin ++)
	{
		for(BasicBlock::iterator II = (*itVecBegin)->begin(); II != (*itVecBegin)->end(); II ++ )
		{
			RemapInstruction(II, VMap);
		}
	}

	//add to the else if body
	BasicBlock * pCondition3 = vecAdd[2];
	BasicBlock * pIfBody     = vecAdd[3];
	BasicBlock * pElseBody   = vecAdd[4];


	pBranch = dyn_cast<BranchInst>(pElseBody->getTerminator());
	BasicBlock * pClonedHeader = cast<BasicBlock>(VMap[pLoop->getHeader()]);
	pBranch->setSuccessor(0, pClonedHeader);
	
	for(BasicBlock::iterator II = pClonedHeader->begin(); II != pClonedHeader->end(); II ++ )
	{
		if(PHINode * pPHI = dyn_cast<PHINode>(II))
		{
			vector<int> vecToRemoved;
			for (unsigned i = 0, e = pPHI->getNumIncomingValues(); i != e; ++i) 
			{
				if(pPHI->getIncomingBlock(i) == pCondition3)
				{
					pPHI->setIncomingBlock(i, pElseBody);
				}
				else if(pPHI->getIncomingBlock(i) == pIfBody)
				{
					vecToRemoved.push_back(i);
				}
			}

			for(unsigned i = 0; i < vecToRemoved.size(); ++i )
			{
				pPHI->removeIncomingValue(vecToRemoved[i] - i, true);
			}
		}
	}

	for(BasicBlock::iterator II = pPostDominator->begin(); II != pPostDominator->end(); II ++)
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

	map<Instruction *, set<Instruction *> > escapeInst ;

	set<BasicBlock *>::iterator itSetBegin = setCloned.begin();
	set<BasicBlock *>::iterator itSetEnd = setCloned.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		for(BasicBlock::iterator II = (*itSetBegin)->begin(); II != (*itSetBegin)->end(); II ++ )
		{
			for(Value::use_iterator ub = II->use_begin(); ub != II->use_end(); ub++)
			{
				if(Instruction * pInstruction = dyn_cast<Instruction>(*ub) )
				{
					if(pInstruction->getParent() == pPostDominator && isa<PHINode>(pInstruction) )
					{
						continue;
					}

					if(setCloned.find(pInstruction->getParent()) == setCloned.end() )
					{
						escapeInst[II].insert(pInstruction);
					}
				}
			}
		}
	}

	if(escapeInst.size() > 0)
	{
		DominatorTree * DT = &getAnalysis<DominatorTree>(*pFunction);
		Instruction * pBegin = pPostDominator->begin();

		map<Instruction *, set<Instruction *> >::iterator itMapBegin = escapeInst.begin();
		map<Instruction *, set<Instruction *> >::iterator itMapEnd   = escapeInst.end();

		for(; itMapBegin != itMapEnd; itMapBegin ++)
		{
			vector<BasicBlock *> vecToAdd;
			BasicBlock * pBlock = itMapBegin->first->getParent();

			for(pred_iterator PI = pred_begin(pPostDominator); PI != pred_end(pPostDominator); PI ++ )
			{
				if(setCloned.find(*PI) == setCloned.end())
				{
					continue;
				}

				if(DT->dominates(pBlock, *PI))
				{
					vecToAdd.push_back(*PI);
				}
			}

			PHINode * pPHI = PHINode::Create(itMapBegin->first->getType(), 2 * vecToAdd.size(), "", pBegin );

			vector<BasicBlock *>::iterator itBlockBegin = vecToAdd.begin();
			vector<BasicBlock *>::iterator itBlockEnd = vecToAdd.end();

			for(; itBlockBegin != itBlockEnd; itBlockBegin ++ )
			{
				pPHI->addIncoming(itMapBegin->first, *itBlockBegin);
				pPHI->addIncoming(cast<Instruction>(VMap[itMapBegin->first]), cast<BasicBlock>(VMap[*itBlockBegin]));
			}

			set<Instruction *>::iterator itSetBegin = itMapBegin->second.begin();
			set<Instruction *>::iterator itSetEnd   = itMapBegin->second.end();

			for(; itSetBegin != itSetEnd; itSetBegin ++ )
			{
				for(unsigned i = 0; i < (*itSetBegin)->getNumOperands(); i ++ )
				{
					if((*itSetBegin)->getOperand(i) == itMapBegin->first)
					{
						(*itSetBegin)->setOperand(i, pPHI);
					}
				}
			}
		}
	}

}

void CrossLoopInstrument::AddHooksToInnerLoop(vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecOut)
{

	


	BasicBlock * pElseBody = vecAdd[4];
	Function * pCurrent = pElseBody->getParent();

	AttributeSet attSet;
	TerminatorInst * pTerminator = pElseBody->getTerminator();

	InlineHookDelimit(pTerminator);
	vector<pair<Function *, int> >::iterator itParaBegin = this->vecParaIndex.begin();
	vector<pair<Function *, int> >::iterator itParaEnd   = this->vecParaIndex.end();

	for(; itParaBegin != itParaEnd; itParaBegin ++)
	{
		Argument * pArg = NULL;
		int iIndex = 0;
		for(Function::arg_iterator argBegin = itParaBegin->first->arg_begin(); argBegin != itParaBegin->first->arg_end(); argBegin ++)
		{
			if(iIndex == itParaBegin->second)
			{
				pArg = argBegin;
				break;
			}
			iIndex ++;
		}

		if(pCurrent == itParaBegin->first)
		{
			InlineHookPara(pArg, pTerminator);
		}
	}

	vector<Instruction *>::iterator itInstVecBegin = vecOut.begin();
	vector<Instruction *>::iterator itInstVecEnd = vecOut.end();
	

	

	for(; itInstVecBegin != itInstVecEnd; itInstVecBegin ++ )
	{
		InlineHookInst(*itInstVecBegin, pTerminator);
	}

	vector<LoadInst *>::iterator itLoadVecBegin = vecLoad.begin();
	vector<LoadInst *>::iterator itLoadVecEnd = vecLoad.end();

	for(; itLoadVecBegin != itLoadVecEnd; itLoadVecBegin++ )
	{
		LoadInst * pLoad = cast<LoadInst>(VMap[*itLoadVecBegin]);
		//pLoad->dump();
		InlineHookLoad(pLoad);
	}
	
}


void CrossLoopInstrument::InstrumentInnerLoop(Loop * pInnerLoop, PostDominatorTree * PDT)
{
	pInnerLoop->dump();
	vector<LoadInst *> vecLoad;
	vector<Instruction *> vecOut;
	CollectInstrumentedInst(this->setInstIndex, pInnerLoop, vecLoad, vecOut);

	BasicBlock * pPostDominator = SearchPostDominatorForLoop(pInnerLoop, PDT);

	vector<BasicBlock *> vecAdd;
	CreateIfElseIfBlock(pInnerLoop, pPostDominator, vecAdd);
	
	ValueToValueMapTy VMap;
	CloneInnerLoop(pInnerLoop, pPostDominator, vecAdd, VMap);
	AddHooksToInnerLoop(vecAdd, VMap, vecLoad, vecOut);

}

void CrossLoopInstrument::ParseMonitoredInstFile(string & sFileName, Module * pModule)
{
	string line;
	ifstream iFile(sFileName.c_str());

	if(iFile.is_open())
	{
		while (getline(iFile,line))
		{
			if(line.find("Func") == 0 )
			{
				if(line.find(':') == string::npos )
				{
					continue;
				}

				string sIndex = line.substr(0, line.find(':'));
				string buf; // Have a buffer string
				stringstream ss(sIndex); // Insert the string into a stream

    			vector<string> tokens; // Create vector to hold our words

				while (ss >> buf)
					tokens.push_back(buf);

				Function * pFunction = pModule->getFunction(tokens[1].c_str());
				
				int iParaID = atoi(tokens[3].c_str());
				pair<Function *, int> pairTmp;
				pairTmp.first = pFunction;
				pairTmp.second = iParaID;
				vecParaIndex.push_back(pairTmp);
				//errs() << pFunction->getName() << " " << iParaID << "\n";
				
			}
			else if(line.find("Inst") == 0)
			{
				if(line.find(':') == string::npos)
				{
					continue;
				}

				string sIndex = line.substr(5, line.find(':'));
				int iIndex = atoi(sIndex.c_str());
				this->setInstIndex.insert(iIndex);
			}
			else
			{

			}
			
		}

		iFile.close();
	}
	else
	{
		errs() << "Failed to open the inst-monitor-file\n";
	}

/*
	set<int>::iterator itSetBegin = this->setInstIndex.begin();
	set<int>::iterator itSetEnd   = this->setInstIndex.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		errs() << *itSetBegin << "\n";
	}
	
	exit(0);
*/
}

bool CrossLoopInstrument::runOnModule(Module& M)
{

	if( strOuterFileName != "" )
	{
		Function * pOuterFunction = SearchFunctionByName(M, strOuterFileName, strOuterFuncName, uOuterSrcLine);
		if(pOuterFunction == NULL)
		{
			errs() << "Cannot find the function containing the outer loop!\n";
			return false;
		}

		LoopInfo * pOuterLI = &(getAnalysis<LoopInfo>(*pOuterFunction));
		this->pOuterLoop = SearchLoopByLineNo(pOuterFunction, pOuterLI, uOuterSrcLine);

		if(pOuterLoop == NULL)
		{
			errs() << "Cannot find the outer loop!\n";
			return false;
		}

		this->bGivenOuterLoop = true;
	}
	else
	{
		this->bGivenOuterLoop = false;
	}


	ParseMonitoredInstFile(strMonitorInstFile, &M);

	SetupTypes(&M);
	SetupConstants(&M);
	SetupStruct(&M);
	SetupHooks(&M);
	SetupGlobals(&M);

	InstrumentMain(&M);

	if(this->bGivenOuterLoop)
	{
		InstrumentOuterLoop(this->pOuterLoop);
	}

	Function * pInnerFunction = SearchFunctionByName(M, strInnerFileName, strInnerFuncName, uInnerSrcLine);
	if(pInnerFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return false;
	}

	PostDominatorTree * PDT = &getAnalysis<PostDominatorTree>(*pInnerFunction);
	LoopInfo * pInnerLI = &(getAnalysis<LoopInfo>(*pInnerFunction));
	Loop * pInnerLoop = SearchLoopByLineNo(pInnerFunction, pInnerLI, uInnerSrcLine);
	if(pInnerLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}
	
	InstrumentInnerLoop(pInnerLoop, PDT);
	
	pInnerFunction->dump();
	return true;
}

