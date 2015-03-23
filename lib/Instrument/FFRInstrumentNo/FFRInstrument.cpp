#include <fstream>
#include <iostream>
#include <string>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sstream>

#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/Config/Config.h"
#include "llvm-Commons/Clone/Clone.h"
#include "Instrument/FFRInstrumentNo/FFRInstrument.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/DebugInfo.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;


static cl::opt<unsigned> uSrcLine("noLine", 
					cl::desc("Source Code Line Number"), cl::Optional, 
					cl::value_desc("uSrcLine"));

static cl::opt<std::string> strFileName("strFile", 
					cl::desc("File Name"), cl::Optional, 
					cl::value_desc("strFileName"));

static cl::opt<std::string> strFuncName("strFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strFuncName"));

static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));

static cl::opt<std::string> strMonitorInstFile("strInstFile",
					cl::desc("Monitored Insts File Name"), cl::Optional,
					cl::value_desc("strInstFile"));

static cl::opt<std::string> strMainFunc("strMain",
					cl::desc("Main Function"), cl::Optional,
					cl::value_desc("strMain"));

static cl::opt<std::string> strLoopHeader("strLoopHeader",
					cl::desc("Block Name for Inner Loop"), cl::Optional,
					cl::value_desc("strLoopHeader"));

static RegisterPass<FFRInstrument> X(
		"ff-recursive-instrument",
		"ff recursive instrument",
		false,
		true);


char FFRInstrument::ID = 0;

void FFRInstrument::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<DominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	
}

FFRInstrument::FFRInstrument(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	initializeDominatorTreePass(Registry);
}

void FFRInstrument::print(raw_ostream &O, const Module *M) const
{
	return;
}

//hooks
void FFRInstrument::SetupTypes(Module * pModule)
{
	this->VoidType = Type::getVoidTy(pModule->getContext());
	this->LongType = IntegerType::get(pModule->getContext(), 64); 
	this->IntType  = IntegerType::get(pModule->getContext(), 32);
	this->CharType = IntegerType::get(pModule->getContext(), 8);
	this->BoolType = IntegerType::get(pModule->getContext(), 1);

	this->VoidPointerType = PointerType::get(this->CharType, 0);
	this->CharStarType = PointerType::get(this->CharType, 0);
	this->LongStarType = PointerType::get(this->LongType, 0);
}

void FFRInstrument::SetupStruct(Module * pModule)
{
	vector<Type *> struct_fields;
	assert(pModule->getTypeByName("struct.stLoadRecord") == NULL);
	this->struct_stLoadRecord = StructType::create(pModule->getContext(), "struct.stLoadRecord");
	struct_fields.push_back(this->LongType);
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
	struct_fields.push_back(this->LongType);
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
	struct_fields.push_back(this->LongType);
	struct_fields.push_back(this->IntType);
	struct_fields.push_back(this->LongType);
	if(this->struct_stInstRecord->isOpaque())
	{
		this->struct_stInstRecord->setBody(struct_fields, false);
	}

	assert(pModule->getTypeByName("struct.stParaRecord") == NULL);
	this->struct_stParaRecord = StructType::create(pModule->getContext(), "struct.stParaRecord");
	struct_fields.clear();
	struct_fields.push_back(this->LongType);
	struct_fields.push_back(this->IntType);
	struct_fields.push_back(this->LongType);
	if(this->struct_stParaRecord->isOpaque())
	{
		this->struct_stParaRecord->setBody(struct_fields, false);
	}

	assert(pModule->getTypeByName("struct.stMemRecord") == NULL);
	this->struct_stMemRecord = StructType::create(pModule->getContext(), "struct.stMemRecord");
	struct_fields.clear();
	struct_fields.push_back(this->LongType);
	struct_fields.push_back(this->IntType);
	struct_fields.push_back(this->LongType);
	if(this->struct_stMemRecord->isOpaque())
	{
		this->struct_stMemRecord->setBody(struct_fields, false);
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

	this->PT_struct_stLogRecord = PointerType::get(this->struct_stLogRecord, 0);
}

void FFRInstrument::SetupConstants(Module * pModule)
{
	this->ConstantInt0 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("0"), 10));
	this->ConstantInt1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("1"), 10));
	this->ConstantInt2 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("2"), 10));
	this->ConstantInt3 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("3"), 10));
	this->ConstantInt4 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("4"), 10));
	this->ConstantInt10 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("10"), 10));
	this->ConstantInt32 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("32"), 10));

	this->ConstantLong0  = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("0"), 10));
	this->ConstantLong1  = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("1"), 10));
	this->ConstantLong32 = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("32"), 10));
	this->ConstantLong40 = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("40"), 10));

	this->ConstantInt_1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("-1"), 10));
	this->ConstantIntFalse = ConstantInt::get(pModule->getContext(), APInt(1, StringRef("0"), 10));

	this->ConstantNULL = ConstantPointerNull::get(this->CharStarType);	
}

void FFRInstrument::SetupHooks(Module * pModule)
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
	FunctionType * InitHooks_FuncTy = FunctionType::get(this->CharStarType, ArgTypes, false);
	this->InitHooks = Function::Create(InitHooks_FuncTy, GlobalValue::ExternalLinkage, "InitHooks", pModule);
	this->InitHooks->setCallingConv(CallingConv::C);

	assert(pModule->getFunction("FinalizeMemHooks") == NULL);
	ArgTypes.clear();
	ArgTypes.push_back(this->LongType);
	FunctionType * Finalize_FuncTy = FunctionType::get(this->VoidType, ArgTypes, false);
	this->FinalizeMemHooks = Function::Create(Finalize_FuncTy, GlobalValue::ExternalLinkage, "FinalizeMemHooks", pModule);
}

void FFRInstrument::SetupGlobals(Module * pModule)
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

	assert(pModule->getGlobalVariable("CURRENT_SAMPLE") == NULL);
	this->CURRENT_SAMPLE = new GlobalVariable(*pModule, this->LongType, false, GlobalValue::ExternalLinkage, 0, "CURRENT_SAMPLE");
	this->CURRENT_SAMPLE->setAlignment(8);
	this->CURRENT_SAMPLE->setInitializer(this->ConstantLong0);

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
	this->iRecordSize_CPI = new GlobalVariable(*pModule, this->LongType, false, GlobalValue::ExternalLinkage, 0, "iRecordSize_CPI");
	this->iRecordSize_CPI->setAlignment(8);
	this->iRecordSize_CPI->setInitializer(this->ConstantLong0);

	assert(pModule->getGlobalVariable("iBufferIndex_CPI") == NULL);
	this->iBufferIndex_CPI = new GlobalVariable(*pModule, this->LongType, false, GlobalValue::ExternalLinkage, 0, "iBufferIndex_CPI");
	this->iBufferIndex_CPI->setAlignment(8);
	this->iBufferIndex_CPI->setInitializer(this->ConstantLong0);
	
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


void FFRInstrument::InlineHookPara(Argument * pArg, Instruction * II, BinaryOperator * pAdd, int FunctionID)
{
	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	CastInst * pStoreAddress = new BitCastInst(getElementPtr, this->PT_struct_stLogRecord, "", II);

	StoreInst * pStore;
	//Constant * const_ptr;
	CastInst * pCast;

	vector<Value *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Instruction * const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(this->ConstantInt1, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Instruction * ParaRecord_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	PointerType * stParaRecord_PT = PointerType::get(this->struct_stParaRecord, 0);
	CastInst * pParaRecord = new BitCastInst(ParaRecord_ptr, stParaRecord_PT, "", II);

	int iID = 0;

	iID = FunctionID * 10 + pArg->getArgNo();
	ConstantInt * pID = ConstantInt::get(this->IntType, iID, false);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
	pStore = new StoreInst(pID, const_ptr, false, II);
	pStore->setAlignment(4);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pArg->getType()))
	{
		if(pIntType->getBitWidth() == 64)
		{
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt2);
			const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
			pStore = new StoreInst(pArg, const_ptr, false, II);
			pStore->setAlignment(8);
		}
		else
		{
			pCast = CastInst::CreateIntegerCast(pArg, this->LongType, true, "", II);
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt2);
			const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
			pStore = new StoreInst(pCast, const_ptr, false, II);
			pStore->setAlignment(8);
		}
	}
	else if(isa<PointerType>(pArg->getType()))
	{
		pCast = new PtrToIntInst(pArg, this->LongType, "", II);
		vecIndex.clear();
		vecIndex.push_back(this->ConstantInt0);
		vecIndex.push_back(this->ConstantInt2);
		const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
		pStore = new StoreInst(pCast, const_ptr, false, II);
		pStore->setAlignment(8);
	}
	else
	{
		assert(0);
	}

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);
}

/*
void FFRInstrument::InlineHookPara(Argument * pArg, Instruction * II, BinaryOperator * pAdd, int FunctionID)
{
	StoreInst * pStore;
	Constant * const_ptr;
	CastInst * pCast;

	//set type
	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(this->ConstantInt1, const_ptr, false, II);
	pStore->setAlignment(4);

	int iID = 0;

	iID = FunctionID * 10 + pArg->getArgNo();
	ConstantInt * pID = ConstantInt::get(this->IntType, iID, false);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Constant * ParaRecord_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	PointerType * stParaRecord_PT = PointerType::get(this->struct_stParaRecord, 0);
	ParaRecord_ptr = ConstantExpr::getCast(Instruction::BitCast, ParaRecord_ptr, stParaRecord_PT);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
	pStore = new StoreInst(pID, const_ptr, false, II);
	pStore->setAlignment(4);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pArg->getType()))
	{
		if(pIntType->getBitWidth() == 64)
		{
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt2);
			const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
			pStore = new StoreInst(pArg, const_ptr, false, II);
			pStore->setAlignment(8);
		}
		else
		{
			pCast = CastInst::CreateIntegerCast(pArg, this->LongType, true, "", II);
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt2);
			const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
			pStore = new StoreInst(pCast, const_ptr, false, II);
			pStore->setAlignment(8);
		}
	}
	else if(isa<PointerType>(pArg->getType()))
	{
		pCast = new PtrToIntInst(pArg, this->LongType, "", II);
		vecIndex.clear();
		vecIndex.push_back(this->ConstantInt0);
		vecIndex.push_back(this->ConstantInt2);
		const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
		pStore = new StoreInst(pCast, const_ptr, false, II);
		pStore->setAlignment(8);
	}
	else
	{
		assert(0);
	}

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);


	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);
	
	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pLoadRecordSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}
*/


void FFRInstrument::InlineHookLoad(LoadInst * pLoad, BinaryOperator * pAdd, int InstID)
{	
	BasicBlock::iterator II = pLoad;
	II ++;

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	CastInst * pStoreAddress = new BitCastInst(getElementPtr, this->PT_struct_stLogRecord, "", II);

	Instruction * const_ptr;
	StoreInst * pStore;
	CastInst * pCast1 = new PtrToIntInst(pLoad->getPointerOperand(), this->LongType, "", II);
	CastInst * pCast2 = NULL;
	vector<Value *> vecIndex;

	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt3);

	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pLoad->getType()))
	{
		if(pIntType->getBitWidth() != 64)
		{
			pCast2 = CastInst::CreateIntegerCast(pLoad, this->LongType, true, "", II);
			pStore = new StoreInst(pCast2, const_ptr, false, II);
			pStore->setAlignment(8);
		}
		else
		{
			pStore = new StoreInst(pLoad, const_ptr, false, II);
			pStore->setAlignment(8);
		}
	}
	else if(isa<PointerType>(pLoad->getType()))
	{
		pCast2 = new PtrToIntInst(pLoad, this->LongType, "", II);
		pStore = new StoreInst(pCast2, const_ptr, false, II);
		pStore->setAlignment(8);
	}
	else
	{
		assert(0);
	}


	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(this->ConstantInt0, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(pCast1, const_ptr, false, II);
	pStore->setAlignment(8);

	ConstantInt *CI = ConstantInt::get(this->IntType, InstID, false);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}

/*
void FFRInstrument::InlineHookLoad(LoadInst * pLoad, BinaryOperator * pAdd, int InstID)
{
	BasicBlock::iterator II = pLoad;
	II ++;
	Constant * const_ptr;
	StoreInst * pStore;
	CastInst * pCast1 = new PtrToIntInst(pLoad->getPointerOperand(), this->LongType, "", II);
	CastInst * pCast2 = NULL;
	vector<Constant *> vecIndex;

	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt3);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pLoad->getType()))
	{
		if(pIntType->getBitWidth() != 64)
		{
			pCast2 = CastInst::CreateIntegerCast(pLoad, this->LongType, true, "", II);
			pStore = new StoreInst(pCast2, const_ptr, false, II);
			pStore->setAlignment(8);
		}
		else
		{
			pStore = new StoreInst(pLoad, const_ptr, false, II);
			pStore->setAlignment(8);
		}
	}
	else if(isa<PointerType>(pLoad->getType()))
	{
		pCast2 = new PtrToIntInst(pLoad, this->LongType, "", II);
		pStore = new StoreInst(pCast2, const_ptr, false, II);
		pStore->setAlignment(8);
	}
	else
	{
		assert(0);
	}


	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(this->ConstantInt0, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(pCast1, const_ptr, false, II);
	pStore->setAlignment(8);

	ConstantInt *CI = ConstantInt::get(this->IntType, InstID, false);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);
	
	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);


	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pLoadRecordSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);
}
*/


void FFRInstrument::InlineHookInst(Instruction * pI, Instruction * II, BinaryOperator * pAdd)
{
	MDNode *Node = pI->getMetadata("ins_id");
	assert(Node);
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
	CastInst * pCast;

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	CastInst * pStoreAddress = new BitCastInst(getElementPtr, this->PT_struct_stLogRecord, "", II);

	vector<Value *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Instruction * const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	StoreInst * pStore = new StoreInst(this->ConstantInt3, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Instruction * InstRecord_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	PointerType * stInstRecord_PT = PointerType::get( this->struct_stInstRecord, 0);
	CastInst * pInstRecord = new BitCastInst(InstRecord_ptr, stInstRecord_PT, "", II);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pInstRecord, vecIndex, "", II);
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = GetElementPtrInst::Create(pInstRecord, vecIndex, "", II);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
	const_ptr = GetElementPtrInst::Create(pInstRecord, vecIndex, "", II);

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
	else
	{
		assert(0);
	}
	
	pStore->setAlignment(8);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}


/*
void FFRInstrument::InlineHookInst(Instruction * pI, Instruction * II, BinaryOperator * pAdd)
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
	StoreInst * pStore = new StoreInst(this->ConstantInt3, const_ptr, false, II);
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
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = ConstantExpr::getGetElementPtr(InstRecord_ptr, vecIndex);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
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
	else
	{
		assert(0);
	}
	
	pStore->setAlignment(8);

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pLoadRecordSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);
}
*/


void FFRInstrument::InlineHookMem(MemTransferInst * pMem, Instruction * II, BinaryOperator * pAdd)
{
	MDNode *Node = pMem->getMetadata("ins_id");
	assert(Node);
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	CastInst * pStoreAddress = new BitCastInst(getElementPtr, this->PT_struct_stLogRecord, "", II);

	vector<Value *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Instruction * const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	StoreInst * pStore = new StoreInst(this->ConstantInt4, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Instruction * MemRecord_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	PointerType * stMemRecord_PT = PointerType::get( this->struct_stMemRecord, 0);
	CastInst * pMemRecord = new BitCastInst(MemRecord_ptr, stMemRecord_PT, "", II);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = GetElementPtrInst::Create(pMemRecord, vecIndex, "", II);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pMemRecord, vecIndex, "", II);
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
	const_ptr = GetElementPtrInst::Create(pMemRecord, vecIndex, "", II);
	Value * pValueLength = pMem->getLength();
	pStore = new StoreInst(pValueLength, const_ptr, false, II);
	pStore->setAlignment(8);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);

	getElementPtr = GetElementPtrInst::Create(pLoadPointer, pAdd, "", II);
	
	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(pMem->getRawSource());
	vecParam.push_back(pValueLength);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	pAdd = BinaryOperator::Create(Instruction::Add, pAdd, pValueLength, "", II );
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}

/*
void FFRInstrument::InlineHookMem(MemTransferInst * pMem, Instruction * II, BinaryOperator * pAdd)
{
	MDNode *Node = pMem->getMetadata("ins_id");
	assert(Node);
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));


	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Constant* const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	StoreInst * pStore = new StoreInst(this->ConstantInt4, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Constant * MemRecord_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	PointerType * stMemRecord_PT = PointerType::get( this->struct_stMemRecord, 0);
	MemRecord_ptr = ConstantExpr::getCast(Instruction::BitCast, MemRecord_ptr, stMemRecord_PT);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = ConstantExpr::getGetElementPtr(MemRecord_ptr, vecIndex);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(MemRecord_ptr, vecIndex);
	pStore = new StoreInst(pAdd, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
	const_ptr = ConstantExpr::getGetElementPtr(MemRecord_ptr, vecIndex);
	Value * pValueLength = pMem->getLength();
	pStore = new StoreInst(pValueLength, const_ptr, false, II);
	pStore->setAlignment(8);

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);
	
	Constant* const_ptr_Record = ConstantExpr::getCast(Instruction::BitCast, this->Record_CPI, this->CharStarType);

	vector<Value *> vecParam;
	vecParam.push_back(getElementPtr);
	vecParam.push_back(const_ptr_Record);
	vecParam.push_back(pLoadRecordSize);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);

	getElementPtr = GetElementPtrInst::Create(pLoadPointer, pAdd, "", II);
	
	vecParam.clear();
	vecParam.push_back(getElementPtr);
	vecParam.push_back(pMem->getRawSource());
	vecParam.push_back(pValueLength);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	pCall->setAttributes(AS);

	pAdd = BinaryOperator::Create(Instruction::Add, pAdd, pValueLength, "", II );
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}

*/

void FFRInstrument::InstrumentMain(Module * pModule)
{
	Function * pFunctionMain;

	if(strMainFunc == "" )
	{
		pFunctionMain = pModule->getFunction("main");
	}
	else
	{
		pFunctionMain = pModule->getFunction(strMainFunc.c_str());
	}

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

			pStore = new StoreInst(this->ConstantLong40, this->iRecordSize_CPI, false, II);
			pStore->setAlignment(8);


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
				pLoad->setAlignment(8);

				CallInst * pCall = CallInst::Create(this->FinalizeMemHooks, pLoad, "", pRet);
				pCall->setCallingConv(CallingConv::C);
				pCall->setTailCall(false);
				AttributeSet AS;
				pCall->setAttributes(AS);
			}
			else if(isa<CallInst>(II) || isa<InvokeInst>(II))
			{
				CallSite cs(II);
				Function * pCalled = cs.getCalledFunction();

				if(pCalled == NULL)
				{
					continue;
				}

				if(pCalled->getName() == "exit" || pCalled->getName() == "_ZL9mysql_endi")
				{
					LoadInst * pLoad = new LoadInst(this->iBufferIndex_CPI, "", false, II);
					pLoad->setAlignment(8);

					CallInst * pCall = CallInst::Create(this->FinalizeMemHooks, pLoad, "", II);
					pCall->setCallingConv(CallingConv::C);
					pCall->setTailCall(false);
					AttributeSet AS;
					pCall->setAttributes(AS);

				}
			}
		}
	}
}

void FFRInstrument::CollectInstrumentedInst(Function * pFunction, vector<LoadInst *> & vecLoad, vector<MemCpyInst *> & vecMem, vector<Instruction *>  & vecInst)
{
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

			if(setInstIndex.find(CI->getZExtValue()) != setInstIndex.end() )
			{
				if(LoadInst * pLoad = dyn_cast<LoadInst>(II))
				{
					vecLoad.push_back(pLoad);
				}
				else if(MemCpyInst * pMem = dyn_cast<MemCpyInst>(II))
				{
					Value * pLength = pMem->getLength();
					assert(isa<ConstantInt>(pLength));
					int iLength = cast<ConstantInt>(pLength)->getSExtValue();

					assert(iLength == 4);
					vecMem.push_back(pMem);
				}
				else 
				{
					assert(isa<CallInst>(II) || isa<InvokeInst>(II));
					vecInst.push_back(II);
				}
			}
		}
	}
}

//parse the instruction file
/*
void FFRInstrument::ParseMonitoredInstFile(string & sFileName, Module * pModule)
{
	string line;
	ifstream iFile(sFileName.c_str());

	if(iFile.is_open())
	{
		while (getline(iFile,line))
		{
			if(line.find("//--") == 0)
			{
				continue;
			}
			else if(line.find("Func") == 0 )
			{
				if(line.find(':') == string::npos )
				{
					continue;
				}

				string sIndex = line.substr(0, line.find(':'));
				string buf; 
				stringstream ss(sIndex); 

    			vector<string> tokens; 

				while (ss >> buf)
					tokens.push_back(buf);

				Function * pFunction = pModule->getFunction(tokens[1].c_str());
				
				int iParaID = atoi(tokens[3].c_str());
				pair<Function *, int> pairTmp;
				pairTmp.first = pFunction;
				pairTmp.second = iParaID;
				vecParaIndex.push_back(pairTmp);
				
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
}
*/

//check the return 
void FFRInstrument::SplitReturnBlock(Function * pFunction)
{
	set<ReturnInst *> setReturns;
	GetAllReturnSite(pFunction, setReturns);

	//errs() << setReturns.size() << "\n";
	assert(setReturns.size() == 1);

	set<ReturnInst *>::iterator itRetBegin = setReturns.begin();
	set<ReturnInst *>::iterator itRetEnd   = setReturns.end();

	for(; itRetBegin != itRetEnd; itRetBegin ++)
	{
		BasicBlock * pRetBlock = (*itRetBegin)->getParent();

		if(pRetBlock->size() > 1)
		{
			pRetBlock->splitBasicBlock(*itRetBegin, "CPI.return");
		}
	}
}

BinaryOperator * FFRInstrument::CreateIfElseBlock(Function * pFunction, Module * pModule, vector<BasicBlock *> & vecAdd)
{

	BasicBlock * pEntryBlock = NULL;
	//BasicBlock * pElseBlock = NULL;

	LoadInst * pLoad1 = NULL;
	//LoadInst * pLoad2 = NULL;
	StoreInst * pStore = NULL;
	Instruction * pTerminator = NULL;
	BinaryOperator * pAdd1 = NULL;
	//BinaryOperator * pAdd2 = NULL;
	//ICmpInst * pCmp = NULL;
	//BranchInst * pBranch = NULL;
	//CallInst * pCall = NULL;
	//AttributeSet emptySet;

	for(Function::iterator BB = pFunction->begin(); BB != pFunction->end(); BB ++ )
	{
		if(BB->getName() == "entry")
		{
			pEntryBlock = BB;
			break;
		}
	}

	assert(pEntryBlock != NULL);
	//BasicBlock * pRawEntryBlock = pEntryBlock->splitBasicBlock(pEntryBlock->begin(), "old.entry");
	//pElseBlock = BasicBlock::Create(pModule->getContext(), ".else.body.CPI", pFunction, 0);

	pTerminator = pEntryBlock->getFirstInsertionPt();
	pLoad1 = new LoadInst(this->numGlobalCounter, "", false, pTerminator);
	pLoad1->setAlignment(8);
	pAdd1 = BinaryOperator::Create(Instruction::Add, pLoad1, this->ConstantLong1, "add", pTerminator);
	pStore = new StoreInst(pAdd1, this->numGlobalCounter, false, pTerminator);
	pStore->setAlignment(8);



/*
	pLoad2 = new LoadInst(this->CURRENT_SAMPLE, "", false, pTerminator);
	pLoad2->setAlignment(8);

	pCmp = new ICmpInst(pTerminator, ICmpInst::ICMP_SLT, pAdd1, pLoad2, "");
	pBranch = BranchInst::Create(pRawEntryBlock, pElseBlock, pCmp );
	ReplaceInstWithInst(pTerminator, pBranch);

	//
	pLoad1 = new LoadInst(this->SAMPLE_RATE, "", false, pElseBlock);
	pCall = CallInst::Create(this->geo, pLoad1, "", pElseBlock);
  	pCall->setCallingConv(CallingConv::C);
  	pCall->setTailCall(false);
  	pCall->setAttributes(emptySet);

  	CastInst * pCast = CastInst::CreateIntegerCast(pCall, this->LongType, true, "", pElseBlock);
  	pAdd2 = BinaryOperator::Create(Instruction::Add, pCast, pLoad2, "add", pElseBlock);

  	pStore = new StoreInst(pAdd2, this->CURRENT_SAMPLE, false, pElseBlock);
  	pStore->setAlignment(8);

  	BranchInst::Create(pRawEntryBlock, pElseBlock);

	vecAdd.push_back(pEntryBlock);
	vecAdd.push_back(pRawEntryBlock);
	vecAdd.push_back(pElseBlock);
*/

	vecAdd.push_back(pEntryBlock);
	return pAdd1;
}


void FFRInstrument::RemapInstruction(Instruction *I, ValueToValueMapTy &VMap) 
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

//clone the whole function 
void FFRInstrument::CloneFunction(Function * pFunction, vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap)
{
	BasicBlock * pEntry = vecAdd[0];
	//BasicBlock * pRawEntry = vecAdd[1];
	//BasicBlock * pElseBlock = vecAdd[2];

	set<ReturnInst *> setReturns;
	GetAllReturnSite(pFunction, setReturns);
	assert(setReturns.size() == 1);

	BasicBlock * pRetBlock = (*setReturns.begin())->getParent();

	VMap[pRetBlock] = pRetBlock;

	vector<BasicBlock *> ToClone;
	//vector<BasicBlock *> BeenCloned;

	set<BasicBlock *> setCloned;

	ToClone.push_back(pEntry);

	while(ToClone.size()>0)
	{
		BasicBlock * pCurrent = ToClone.back();
		ToClone.pop_back();

		WeakVH & BBEntry = VMap[pCurrent];
		if (BBEntry)
		{
			continue;
		}
		
		BBEntry = pCurrent;

		for(BasicBlock::iterator II = pCurrent->begin(); II != pCurrent->end(); ++II )
		{
			VMap[II] = II;
		}

		const TerminatorInst *TI = pCurrent->getTerminator();
		for (unsigned i = 0, e = TI->getNumSuccessors(); i != e; ++i)
		{
			ToClone.push_back(TI->getSuccessor(i));
		}

		setCloned.insert(pCurrent);
	}

}

void FFRInstrument::CloneFunctionCalled(Function * pRootFunction, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping)
{
	vector<Function *> vecWorkList;
	set<Function *> toDo;

	set<Instruction *> setMonitoredInst;

	for(Function::iterator BB = pRootFunction->begin(); BB != pRootFunction->end(); BB ++)
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
				
				if(pCalled == NULL)
				{
					continue;
				}

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end() )
				{
					continue;
				}

				if(pCalled->isDeclaration())
				{
					continue;
				}

				if(pRootFunction == pCalled)
				{
					continue;
				}

				FuncCallSiteMapping[pCalled].insert(II);

				if(toDo.find(pCalled) == toDo.end() )
				{
					toDo.insert(pCalled);
					vecWorkList.push_back(pCalled);
				}
			}
		}
	}

	while(vecWorkList.size() > 0)
	{
		Function * pCurrent = vecWorkList[vecWorkList.size() -1];
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
				
					if(pCalled != NULL)
					{
						if(this->LibraryTypeMapping.find(pCalled) == this->LibraryTypeMapping.end() )
						{
							if(!pCalled->isDeclaration() && pCalled != pRootFunction)
							{
								FuncCallSiteMapping[pCalled].insert(II);

								if(toDo.find(pCalled) == toDo.end() )
								{
									toDo.insert(pCalled);
									vecWorkList.push_back(pCalled);
								}
							}
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
			
				if(this->setInstIndex.find(CI->getZExtValue()) != this->setInstIndex.end())
				{
					setMonitoredInst.insert(II);
				}
			}
		}
	}

	set<Function *>::iterator itSetFuncBegin = toDo.begin();
	set<Function *>::iterator itSetFuncEnd   = toDo.end();

	vector<Type *> vecExtra;
	vecExtra.push_back(this->LongType);

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
	{
		Function * rawFunction = *itSetFuncBegin;
		Function * duplicateFunction = CloneFunctionWithExtraArguments(rawFunction, VCalleeMap, false, vecExtra, 0);
		duplicateFunction->setName(rawFunction->getName() + ".CPI");
		duplicateFunction->setLinkage(GlobalValue::InternalLinkage);
		rawFunction->getParent()->getFunctionList().push_back(duplicateFunction);
		VCalleeMap[rawFunction] = duplicateFunction;
	}

	itSetFuncBegin = toDo.begin();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
	{
		set<Instruction *>::iterator itSetInstBegin = FuncCallSiteMapping[*itSetFuncBegin].begin();
		set<Instruction *>::iterator itSetInstEnd   = FuncCallSiteMapping[*itSetFuncBegin].end();

		ValueToValueMapTy::iterator FuncIt = VCalleeMap.find(*itSetFuncBegin);
		assert(FuncIt != VCalleeMap.end());

		Function * clonedFunction = cast<Function>(FuncIt->second);

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
		{
			ValueToValueMapTy::iterator It = VCalleeMap.find(*itSetInstBegin);

			if (It != VCalleeMap.end())
			{
				if(CallInst * pCall = dyn_cast<CallInst>(It->second) )
				{
					vector<Value*> vecParams;
					for(unsigned i = 0; i < pCall->getNumArgOperands(); i ++)
					{
						vecParams.push_back(pCall->getArgOperand(i));
					}

					Function * pParent = pCall->getParent()->getParent();

					Function::arg_iterator pAdd = pParent->arg_begin();
					for(size_t index = 0; index < pParent->arg_size() - 1; index ++ )
					{
						pAdd++;
					}

					vecParams.push_back(pAdd);
					CallInst * pNew = CallInst::Create(clonedFunction, vecParams, "");
					ReplaceInstWithInst(pCall, pNew);

				}
				else if(InvokeInst * pInvoke = dyn_cast<InvokeInst>(It->second))
				{
					vector<Value *> vecParams;
					for(unsigned i = 0; i < pInvoke->getNumArgOperands(); i ++ )
					{
						vecParams.push_back(pInvoke->getArgOperand(i));
					}	

					Function * pParent = pInvoke->getParent()->getParent();

					Function::arg_iterator pAdd = pParent->arg_begin();

					for(size_t index = 0; index < pParent->arg_size() -1; index ++ )
					{
						pAdd++;
					}

					vecParams.push_back(pAdd);
					CallInst * pNew = CallInst::Create(clonedFunction, vecParams, "");
					ReplaceInstWithInst(pInvoke, pNew);
				}
			}
		}
	}
}



//instrument
void FFRInstrument::AddHooksToClonedFunction(BinaryOperator * pAdd, vector<BasicBlock *> & vecAdd, int iFunctionID, vector<LoadInst *> & vecLoad, vector<MemCpyInst *> & vecMem, vector<Instruction *> & vecInst, ValueToValueMapTy & VMap )
{

	BasicBlock * pElseBlock = vecAdd[0];
	TerminatorInst * pTerminator = pElseBlock->getTerminator();
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

		InlineHookPara(pArg, pTerminator, pAdd, iFunctionID);
		
	}


	vector<LoadInst *>::iterator itVecLoadBegin = vecLoad.begin();
	vector<LoadInst *>::iterator itVecLoadEnd   = vecLoad.end();

	for(; itVecLoadBegin != itVecLoadEnd; itVecLoadBegin ++ )
	{
		MDNode *Node = (*itVecLoadBegin)->getMetadata("ins_id");
		if(!Node)
		{
			continue;
		}

		assert(Node->getNumOperands() == 1);
		ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
		assert(CI);

		int iID = CI->getZExtValue();

		InlineHookLoad(cast<LoadInst>(VMap[*itVecLoadBegin]), pAdd, iID);
	}

	vector<MemCpyInst *>::iterator itMemBegin = vecMem.begin();
	vector<MemCpyInst *>::iterator itMemEnd   = vecMem.end();

	for(; itMemBegin != itMemEnd; itMemBegin ++ )
	{
		MemCpyInst * pCloned = cast<MemCpyInst>(VMap[*itMemBegin]);

		InlineHookMem(pCloned, pCloned->getParent()->getTerminator(), pAdd);

	}

	vector<Instruction *>::iterator itInstInBegin = vecInst.begin();
	vector<Instruction *>::iterator itInstInEnd   = vecInst.end();

	for(; itInstInBegin != itInstInEnd; itInstInBegin ++ )
	{
		Instruction * pInst = cast<Instruction>(VMap[*itInstInBegin]);
		InlineHookInst(pInst, pInst->getParent()->getTerminator(), pAdd);
	}
}



bool FFRInstrument::runOnModule(Module& M)
{
	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	Function * pFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);

	if(pFunction == NULL)
	{
		errs() << "Cannot find the recursive function!\n";
		return false;
	}

	ParseMonitoredInstFile(strMonitorInstFile, &M, this->setInstIndex, this->vecParaIndex);

	SetupTypes(&M);
	SetupConstants(&M);
	SetupStruct(&M);
	SetupHooks(&M);
	SetupGlobals(&M);

	InstrumentMain(&M);

	vector<LoadInst *> vecLoad;
	vector<MemCpyInst *> vecMem;
	vector<Instruction *> vecInst;

	MDNode *Node = pFunction->begin()->begin()->getMetadata("func_id");
	int iFunctionID = -1;
	if(Node!=NULL)
	{
		assert(Node->getNumOperands() == 1);
		ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
		assert(CI);
		iFunctionID = CI->getZExtValue();
	}


	CollectInstrumentedInst(pFunction, vecLoad, vecMem, vecInst);

	//SplitReturnBlock(pFunction);

	vector<BasicBlock *> vecAdd;
	BinaryOperator * pAdd = CreateIfElseBlock(pFunction, &M, vecAdd);

	ValueToValueMapTy VCalleeMap;
	map<Function *, set<Instruction *> > FuncCallSiteMapping;

	CloneFunctionCalled(pFunction, VCalleeMap, FuncCallSiteMapping);

	ValueToValueMapTy VMap;

	CloneFunction(pFunction, vecAdd, VMap);
	AddHooksToClonedFunction(pAdd, vecAdd, iFunctionID, vecLoad, vecMem, vecInst, VMap );

	map<Function *, set<Instruction *> >::iterator itMapBegin = FuncCallSiteMapping.begin();
	map<Function *, set<Instruction *> >::iterator itMapEnd   = FuncCallSiteMapping.end();

	for(; itMapBegin != itMapEnd; itMapBegin ++ )
	{
		ValueToValueMapTy::iterator FuncIt = VCalleeMap.find(itMapBegin->first);
		assert(FuncIt != VCalleeMap.end());

		Function * clonedFunction = cast<Function>(FuncIt->second);

		set<Instruction *>::iterator itSetInstBegin = itMapBegin->second.begin();
		set<Instruction *>::iterator itSetInstEnd   = itMapBegin->second.end();

		for(; itSetInstBegin != itSetInstEnd; itSetInstBegin ++ )
		{
			ValueToValueMapTy::iterator It = VMap.find(*itSetInstBegin);

			if(It != VMap.end())
			{
				if(CallInst * pCall = dyn_cast<CallInst>(It->second) )
				{
					vector<Value *> vecParams;

					for(unsigned i = 0; i < pCall->getNumArgOperands(); i ++)
					{
						vecParams.push_back(pCall->getArgOperand(i));
					}

					vecParams.push_back(pAdd);
					CallInst * pNew = CallInst::Create(clonedFunction, vecParams, "");
					ReplaceInstWithInst(pCall, pNew);

				}
				else if(InvokeInst * pInvoke = dyn_cast<InvokeInst>(It->second))
				{
					vector<Value *> vecParams;
					for(unsigned i = 0; i < pInvoke->getNumArgOperands(); i ++)
					{
						vecParams.push_back(pInvoke->getArgOperand(i));
					}

					vecParams.push_back(pAdd);
					CallInst * pNew = CallInst::Create(clonedFunction, vecParams, "");
					ReplaceInstWithInst(pInvoke, pNew);

				}
			}
		}
	}

	pFunction->dump();

	return false;
}

