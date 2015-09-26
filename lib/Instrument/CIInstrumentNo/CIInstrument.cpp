#include <fstream>
#include <iostream>
#include <string>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sstream>

#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/Loop/Loop.h"
#include "llvm-Commons/Invariant/InvariantAnalysis.h"

#include "Instrument/CIInstrumentNo/CIInstrument.h"

#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/PredIteratorCache.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/MDBuilder.h"


static RegisterPass<CrossInterationInstrument> X(
		"cross-iteration-instrument",
		"cross iteration instrument",
		true,
		true);

static cl::opt<unsigned> uSrcLine("noLine", 
					cl::desc("Source Code Line Number"), cl::Optional, 
					cl::value_desc("uSrcCodeLine"));

static cl::opt<std::string> strFileName("strFile", 
					cl::desc("File Name"), cl::Optional, 
					cl::value_desc("strFileName"));

static cl::opt<std::string> strFuncName("strFunc", 
					cl::desc("Function Name"), cl::Optional, 
					cl::value_desc("strFuncName"));

static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));

static cl::opt<std::string> strLoopHeader("strLoopHeader",
					cl::desc("Block Name for Inner Loop Header"), cl::Optional,
					cl::value_desc("strLoopHeader"));

static cl::opt<std::string> strMonitorInstFile("strInstFile",
					cl::desc("Monitored Insts File Name"), cl::Optional,
					cl::value_desc("strInstFile"));

static cl::opt<std::string> strMainFunc("strMain",
					cl::desc("Main Function"), cl::Optional,
					cl::value_desc("strMain"));

char CrossInterationInstrument::ID = 0;

void CrossInterationInstrument::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<DominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();	
	AU.addRequired<AliasAnalysis>();
}

CrossInterationInstrument::CrossInterationInstrument(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	initializeDominatorTreePass(Registry);
	initializeAliasAnalysisAnalysisGroup(Registry);
}

void CrossInterationInstrument::print(raw_ostream &O, const Module *M) const
{
	return;
}

void CrossInterationInstrument::SetupTypes(Module * pModule)
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

void CrossInterationInstrument::SetupConstants(Module * pModule)
{
	this->ConstantInt0 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("0"), 10));
	this->ConstantInt1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("1"), 10));
	this->ConstantInt2 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("2"), 10));
	this->ConstantInt3 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("3"), 10));
	this->ConstantInt4 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("4"), 10));
	this->ConstantInt5 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("5"), 10));

	this->ConstantInt10 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("10"), 10));
	this->ConstantInt32 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("32"), 10));

	this->ConstantInt_1 = ConstantInt::get(pModule->getContext(), APInt(32, StringRef("-1"), 10));

	this->ConstantIntFalse = ConstantInt::get(pModule->getContext(), APInt(1, StringRef("0"), 10));

	this->ConstantLong0  = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("0"), 10));
	this->ConstantLong1  = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("1"), 10));
	this->ConstantLong32 = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("32"), 10));
	this->ConstantLong40 = ConstantInt::get(pModule->getContext(), APInt(64, StringRef("40"), 10));

	this->ConstantNULL = ConstantPointerNull::get(this->CharStarType);
	
}


void CrossInterationInstrument::SetupStruct(Module * pModule)
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

	assert(pModule->getTypeByName("struct.stMemRecord") == NULL);
	this->struct_stMemRecord = StructType::create(pModule->getContext(), "struct.stMemRecord");
	struct_fields.clear();
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


void CrossInterationInstrument::SetupHooks(Module * pModule)
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
	ArgTypes.push_back(this->LongType);
	FunctionType * Finalize_FuncTy = FunctionType::get(this->VoidType, ArgTypes, false);
	this->FinalizeMemHooks = Function::Create(Finalize_FuncTy, GlobalValue::ExternalLinkage, "FinalizeMemHooks", pModule);
}

void CrossInterationInstrument::SetupGlobals(Module * pModule)
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

	assert(pModule->getGlobalVariable("numInstances")==NULL);
	this->numInstances = new GlobalVariable(*pModule, this->LongType, false, GlobalVariable::ExternalLinkage, 0, "numInstances");
	this->numInstances->setAlignment(8);
	this->numInstances->setInitializer(this->ConstantLong0);

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


void CrossInterationInstrument::InlineHookLoad(LoadInst * pLoad, Instruction * II )
{
	if(pLoad->getType()->isVectorTy())
	{
		return;
	}


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
	vecIndex.push_back(this->ConstantInt0);
	const_ptr =  GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(this->ConstantInt0, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(pCast1, const_ptr, false, II);
	pStore->setAlignment(8);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt2);
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pLoad->getType()))
	{
		if(pIntType->getBitWidth() == 64)
		{
			pStore = new StoreInst(pLoad, const_ptr, false, II);
		}
		else
		{
			pCast2 = CastInst::CreateIntegerCast(pLoad, this->LongType, true, "", II);
			pStore = new StoreInst(pCast2, const_ptr, false, II);
		}
		
	}
	else if(isa<PointerType>(pLoad->getType()))
	{
		pCast2 = new PtrToIntInst(pLoad, this->LongType, "", II);
		pStore = new StoreInst(pCast2, const_ptr, false, II);
	}
	else if(pLoad->getType()->isDoubleTy())
	{
		CastInst * pCast = new FPToSIInst(pLoad, this->LongType, "", II);
		pStore = new StoreInst(pCast, const_ptr, false, II);
	}
	else
	{	
		//pLoad->dump();
		//errs() << pLoad->getType()->isIntOrIntVectorTy() << "\n";
		assert(0);
	}

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
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);


	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}


/*
void CrossInterationInstrument::InlineHookLoad(LoadInst * pLoad, Instruction * II )
{
	//BasicBlock::iterator II = pLoad;
	//II ++;
	Constant * const_ptr;
	StoreInst * pStore;
	CastInst * pCast1 = new PtrToIntInst(pLoad->getPointerOperand(), this->LongType, "", II);
	CastInst * pCast2 = NULL;

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

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pLoad->getType()))
	{
		if(pIntType->getBitWidth() == 64)
		{
			pStore = new StoreInst(pLoad, const_ptr, false, II);
		}
		else
		{
			pCast2 = CastInst::CreateIntegerCast(pLoad, this->LongType, true, "", II);
			pStore = new StoreInst(pCast2, const_ptr, false, II);
		}
		
	}
	else if(isa<PointerType>(pLoad->getType()))
	{
		pCast2 = new PtrToIntInst(pLoad, this->LongType, "", II);
		pStore = new StoreInst(pCast2, const_ptr, false, II);
	}
	else
	{
		assert(0);
	}

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

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);
}
*/

void CrossInterationInstrument::InlineHookInst(Instruction * pI, Instruction * II)
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
	StoreInst * pStore = new StoreInst(this->ConstantInt2, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Instruction * InstRecord_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	PointerType * stInstRecord_PT = PointerType::get(this->struct_stInstRecord, 0);
	CastInst * pInstRecord = new BitCastInst(InstRecord_ptr, stInstRecord_PT, "", II);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pInstRecord, vecIndex, "", II);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
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
	else if(pI->getType()->isDoubleTy())
	{
		CastInst * pCast = new FPToSIInst(pI, this->LongType, "", II);
		pStore = new StoreInst(pCast, const_ptr, false, II);
	}
	else
	{
		pI->dump();
		assert(0);
	}
	
	pStore->setAlignment(8);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}


/*
void CrossInterationInstrument::InlineHookInst(Instruction * pI, Instruction * II)
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

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}
*/

void CrossInterationInstrument::InlineHookDelimit(Instruction * II)
{
	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	CastInst * pStoreAddress = new BitCastInst(getElementPtr, this->PT_struct_stLogRecord, "", II);

	//errs() << "after the first\n";
	vector<Value *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);

	Instruction * const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	StoreInst * pStore = new StoreInst(this->ConstantInt4, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Instruction * DelimitRecord_ptr =  GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);;
	PointerType * DelimitRecord_PT = PointerType::get(this->struct_stDelimiterRecord, 0);
	CastInst * pDelimitRecord = new BitCastInst(DelimitRecord_ptr, DelimitRecord_PT , "", II);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pDelimitRecord, vecIndex, "", II);

	pStore = new StoreInst(this->pAddCurrentInstances, const_ptr, false, II);
	pStore->setAlignment(8);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}


/*
void CrossInterationInstrument::InlineHookDelimit(Instruction * II)
{
	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Constant* const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	StoreInst * pStore = new StoreInst(this->ConstantInt4, const_ptr, false, II);
	pStore->setAlignment(4);

	//LoadInst * pLoad = new LoadInst(this->numGlobalCounter, "", false, II);
	//LoadInst * pLoad = new LoadInst(this->pAddCurrentInstances, "", false, II );
	//pLoad->setAlignment(8);
	

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

	pStore = new StoreInst(this->pAddCurrentInstances, const_ptr, false, II);
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

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);
}
*/

void CrossInterationInstrument::InlineHookMem(MemTransferInst * pMem, Instruction * II)
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
	StoreInst * pStore = new StoreInst(this->ConstantInt5, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Instruction * MemRecord_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	PointerType * stMemRecord_PT = PointerType::get(this->struct_stMemRecord, 0);
	CastInst * pMemRecord = new BitCastInst(MemRecord_ptr, stMemRecord_PT, "", II);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pMemRecord, vecIndex, "", II);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	const_ptr = GetElementPtrInst::Create(pMemRecord, vecIndex, "", II);
	Value * pValueLength = pMem->getLength();
	pStore = new StoreInst(pValueLength, const_ptr, false, II);
	pStore->setAlignment(8);

	//LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	//pLoadPointer->setAlignment(8);
	//LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	//pLoadIndex->setAlignment(8);

	//GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);
	
	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);

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
void CrossInterationInstrument::InlineHookMem(MemTransferInst * pMem, Instruction * II)
{
	MDNode *Node = pMem->getMetadata("ins_id");
	assert(Node);
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));

	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Constant* const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	StoreInst * pStore = new StoreInst(this->ConstantInt5, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Constant * MemRecord_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	PointerType * stMemRecord_PT = PointerType::get( this->struct_stMemRecord, 0);
	MemRecord_ptr = ConstantExpr::getCast(Instruction::BitCast, MemRecord_ptr, stMemRecord_PT);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = ConstantExpr::getGetElementPtr(MemRecord_ptr, vecIndex);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
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

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);

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

void CrossInterationInstrument::InstrumentPreHeader(Loop * pLoop)
{
	LoadInst * pLoad = NULL;
	StoreInst * pStore = NULL;

	//update instance counter in the preheader
	this->pPreHeader = pLoop->getLoopPreheader();
	
	assert(this->pPreHeader != NULL);

	pLoad = new LoadInst(this->numInstances, "", false, this->pPreHeader->getTerminator());
	pLoad->setAlignment(8);
	this->pAddCurrentInstances = BinaryOperator::Create(Instruction::Add, pLoad, this->ConstantLong1, "add.currentinstance", this->pPreHeader->getTerminator());
	pStore = new StoreInst(this->pAddCurrentInstances, this->numInstances, false, this->pPreHeader->getTerminator());
	pStore->setAlignment(8);

	/*
	this->pLoadnumGlobalCounter = new LoadInst(this->numGlobalCounter, "", false, pPreHeader->getTerminator());
	this->pLoadnumGlobalCounter->setAlignment(8);

	this->pLoadCURRENT_SAMPLE = new LoadInst(this->CURRENT_SAMPLE, "", false, pPreHeader->getTerminator());
	this->pLoadCURRENT_SAMPLE->setAlignment(8);
	*/
}


void CrossInterationInstrument::RemapInstruction(Instruction *I, ValueToValueMapTy &VMap) 
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

void CrossInterationInstrument::DoClone(Function * pFunction, vector<BasicBlock *> & ToClone, ValueToValueMapTy & VMap, set<BasicBlock *> & setCloned)
{

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

void CrossInterationInstrument::SplitHeader(Loop * pLoop)
{
	Instruction * pFirstCall = NULL;

	for(BasicBlock::iterator II = this->pHeader->begin(); II != this->pHeader->end(); II ++ )
	{
		if(isa<CallInst>(II) || isa<InvokeInst>(II))
		{
			pFirstCall = II;
			break;
		}
	}

	if(pFirstCall == NULL)
	{
		pFirstCall = this->pHeader->getTerminator();
	}

	this->pOldHeader = this->pHeader->splitBasicBlock(pFirstCall, ".oldheader");

}

void CrossInterationInstrument::InstrumentNewHeader()
{
	//LoadInst * pLoad = new LoadInst(this->SAMPLE_RATE, "", false, this->pNewHeader->getTerminator());
	//CallInst * pCall = CallInst::Create(this->geo, pLoad, "", this->pNewHeader->getTerminator());
  	//pCall->setCallingConv(CallingConv::C);
  	//pCall->setTailCall(false);
  	//AttributeSet emptySet;
  	//pCall->setAttributes(emptySet);

  	//this->pCastCURRENT_SAMPLE = CastInst::CreateIntegerCast(pCall, this->LongType, true, "", this->pNewHeader->getTerminator());
  	//StoreInst * pStore = new StoreInst(this->pCastCURRENT_SAMPLE, this->CURRENT_SAMPLE, false, this->pNewHeader->getTerminator());
  	//pStore->setAlignment(8);

}

void CrossInterationInstrument::UpdateHeader(set<BasicBlock *> & setCloned, ValueToValueMapTy & VMap)
{
	
	/*
	for(BasicBlock::iterator II = this->pHeader->begin(); II != this->pHeader->end(); II ++)
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
	*/

	/*
	vector<BasicBlock *> vecPredBlocks;
	for(pred_iterator PI = pred_begin(this->pHeader), E = pred_end(this->pHeader); PI != E; ++PI)
	{
		vecPredBlocks.push_back(*PI);
	}

	PHINode * pPHI = PHINode::Create(this->LongType, vecPredBlocks.size(), "numGlobalCounter", this->pHeader->getFirstInsertionPt() );

	this->pAddnumGlobalCounter = BinaryOperator::Create(Instruction::Add, pPHI, this->ConstantLong1, "AddnumGlobalCounter", this->pHeader->getTerminator());

	vector<BasicBlock *>::iterator itVecBlockBegin = vecPredBlocks.begin();
	vector<BasicBlock *>::iterator itVecBlockEnd   = vecPredBlocks.end();

	for(; itVecBlockBegin != itVecBlockEnd; itVecBlockBegin ++ )
	{
		if(*itVecBlockBegin == this->pPreHeader)
		{
			pPHI->addIncoming(this->pLoadnumGlobalCounter, *itVecBlockBegin);
		}
		else if(setCloned.find(*itVecBlockBegin) != setCloned.end() )
		{
			pPHI->addIncoming(this->pAddnumGlobalCounter, *itVecBlockBegin);
		}
		else
		{
			pPHI->addIncoming(this->ConstantLong0, *itVecBlockBegin);
		}
	}

	pPHI = PHINode::Create(this->LongType, vecPredBlocks.size(), "CURRENT_SAMPLE", this->pHeader->getFirstInsertionPt());

	itVecBlockBegin = vecPredBlocks.begin();

	for(; itVecBlockBegin != itVecBlockEnd; itVecBlockBegin ++)
	{
		if(*itVecBlockBegin == pPreHeader)
		{
			pPHI->addIncoming(this->pLoadCURRENT_SAMPLE, *itVecBlockBegin);
		}
		else if(setCloned.find(*itVecBlockBegin) != setCloned.end() )
		{
			pPHI->addIncoming(pPHI, *itVecBlockBegin);
		}
		else
		{
			pPHI->addIncoming(this->pCastCURRENT_SAMPLE, *itVecBlockBegin);
		}
	}
	*/

	//add condition
	//ICmpInst * pCmp = new ICmpInst(this->pHeader->getTerminator(), ICmpInst::ICMP_SLT, this->pAddnumGlobalCounter, pPHI, "");
	//BranchInst * pBranch = BranchInst::Create(this->pOldHeader, this->pNewHeader, pCmp );
	//ReplaceInstWithInst(this->pHeader->getTerminator(), pBranch);

	//MDNode * Node = MDBuilder(this->pM->getContext()).createBranchWeights(99999999,1);
	//pBranch->setMetadata(llvm::LLVMContext::MD_prof, Node);

}

void CrossInterationInstrument::UpdateExitBlock(Function * pFunction, set<BasicBlock *> & setExitBlocks, set<BasicBlock *> & setCloned, ValueToValueMapTy & VMap)
{
	set<BasicBlock *>::iterator itSetBlockBegin = setExitBlocks.begin();
	set<BasicBlock *>::iterator itSetBlockEnd   = setExitBlocks.end();

	for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin++)
	{
		for(BasicBlock::iterator II = (*itSetBlockBegin)->begin(); II != (*itSetBlockBegin)->end(); II ++ )
		{
			if(PHINode * pPHI = dyn_cast<PHINode>(II))
			{
				unsigned numIncomming = pPHI->getNumIncomingValues();
				for(unsigned i = 0; i < numIncomming; i++)
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

void CrossInterationInstrument::AddHooksToLoop(vector<Instruction *> & vecInst, ValueToValueMapTy & VMap, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping)
{
	//add delimiter


	InlineHookDelimit(this->pHeader->getFirstInsertionPt());

	vector<Instruction *>::iterator itVecBegin = vecInst.begin();
	vector<Instruction *>::iterator itVecEnd   = vecInst.end();

	for(; itVecBegin != itVecEnd; itVecBegin ++ )
	{	
		if(LoadInst * pLoad = dyn_cast<LoadInst>(*itVecBegin))
		{
			InlineHookLoad(pLoad, pLoad->getParent()->getTerminator());
		}
		else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(*itVecBegin))
		{
			InlineHookMem(pMem, pMem->getParent()->getTerminator());
		}
		else
		{
			if (InvokeInst *Inv = dyn_cast<InvokeInst>(*itVecBegin))
			{
				InlineHookInst(Inv, Inv->getNormalDest()->getTerminator());
			}
			else
			{
				InlineHookInst(*itVecBegin, (*itVecBegin)->getParent()->getTerminator());
			}	
		}
	}

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
					pCall->setCalledFunction(clonedFunction);
				}
				else if(InvokeInst * pInvoke = dyn_cast<InvokeInst>(It->second))
				{
					pInvoke->setCalledFunction(clonedFunction);
				}
			}
		}
	}

}



void CrossInterationInstrument::CloneLoopBody(Loop * pLoop, vector<Instruction *> & vecInst )
{
	this->pHeader = pLoop->getHeader();
	Function * pFunction = this->pHeader->getParent();
	//StoreInst * pStore = NULL;

	LoopSimplify(pLoop, this);
	LoopInfo * pLI = &getAnalysis<LoopInfo>(*pFunction);
	pLoop = pLI->getLoopFor(pHeader);

	ValueToValueMapTy VCalleeMap;
	map<Function *, set<Instruction *> > FuncCallSiteMapping;
	set<BasicBlock *> setBlocksInLoop;

	for(Loop::block_iterator BB = pLoop->block_begin(); BB != pLoop->block_end(); BB ++)
	{
		setBlocksInLoop.insert(*BB);
	}

	CloneFunctionCalled(setBlocksInLoop, VCalleeMap, FuncCallSiteMapping);

	InstrumentPreHeader(pLoop);
	//SplitHeader(pLoop);


	this->pPreHeader = pLoop->getLoopPreheader();

	vector<BasicBlock *> vecToDo;
	vecToDo.push_back(this->pHeader);
	
	ValueToValueMapTy VMap;
	
	//VMap[pHeader] = pHeader;

	SmallVector<BasicBlock *, 4> ExitBlocks;
	set<BasicBlock *> setExitBlocks;
	pLoop->getExitBlocks(ExitBlocks);
	
	for(unsigned long i = 0; i < ExitBlocks.size(); i++ )
	{
		VMap[ExitBlocks[i]] = ExitBlocks[i];	
		setExitBlocks.insert(ExitBlocks[i]);
	}

	set<BasicBlock *> setCloned;
	DoClone(pFunction, vecToDo, VMap, setCloned);

	

	AddHooksToLoop(vecInst, VMap, VCalleeMap, FuncCallSiteMapping);

}


bool CrossInterationInstrument::pointerInvalidatedByLoop(Value *V, uint64_t Size, const MDNode *TBAAInfo) 
{
	// Check to see if any of the basic blocks in CurLoop invalidate *V.
	return CurAST->getAliasSetForPointer(V, Size, TBAAInfo).isMod();
}

/// canSinkOrHoistInst - Return true if the hoister and sinker can handle this
/// instruction.
///
bool CrossInterationInstrument::canSinkOrHoistInst(Instruction &I) 
{
	// Loads have extra constraints we have to verify before we can hoist them.
	if (LoadInst *LI = dyn_cast<LoadInst>(&I)) 
	{
		if (!LI->isUnordered())
			return false;        // Don't hoist volatile/atomic loads!

		// Loads from constant memory are always safe to move, even if they end up
		// in the same alias set as something that ends up being modified.
		if (AA->pointsToConstantMemory(LI->getOperand(0)))
			return true;
		if (LI->getMetadata("invariant.load"))
			return true;

		// Don't hoist loads which have may-aliased stores in loop.
		uint64_t Size = 0;
		if (LI->getType()->isSized())
			Size = AA->getTypeStoreSize(LI->getType());
		return !pointerInvalidatedByLoop(LI->getOperand(0), Size, LI->getMetadata(LLVMContext::MD_tbaa));
	} 
	else if (CallInst *CI = dyn_cast<CallInst>(&I)) 
	{
		// Don't sink or hoist dbg info; it's legal, but not useful.
		if (isa<DbgInfoIntrinsic>(I))
			return false;

		// Handle simple cases by querying alias analysis.
		AliasAnalysis::ModRefBehavior Behavior = AA->getModRefBehavior(CI);
		if (Behavior == AliasAnalysis::DoesNotAccessMemory)
			return true;
		if (AliasAnalysis::onlyReadsMemory(Behavior)) 
		{
			// If this call only reads from memory and there are no writes to memory
			// in the loop, we can hoist or sink the call as appropriate.
			bool FoundMod = false;
			for (AliasSetTracker::iterator I = CurAST->begin(), E = CurAST->end(); I != E; ++I) 
			{
				AliasSet &AS = *I;
				if (!AS.isForwardingAliasSet() && AS.isMod()) 
				{
					FoundMod = true;
					break;
				}
			}
			if (!FoundMod) return true;
		}

		// FIXME: This should use mod/ref information to see if we can hoist or
		// sink the call.

		return false;
	}


	// Only these instructions are hoistable/sinkable.
	if (!isa<BinaryOperator>(I) && !isa<CastInst>(I) && !isa<SelectInst>(I) &&
		!isa<GetElementPtrInst>(I) && !isa<CmpInst>(I) &&
		!isa<InsertElementInst>(I) && !isa<ExtractElementInst>(I) &&
		!isa<ShuffleVectorInst>(I) && !isa<ExtractValueInst>(I) &&
		!isa<InsertValueInst>(I))
		return false;

	//return isSafeToExecuteUnconditionally(I);
	return true;
}

void CrossInterationInstrument::CollectInstrumentedInst(Loop * pLoop, vector<Instruction *> & vecInst)
{
	Function * pFunction = pLoop->getHeader()->getParent();

	for(Loop::block_iterator I = pLoop->block_begin(); I != pLoop->block_end(); I ++ )
	{
		BasicBlock * BB = *I;
		this->CurAST->add(*BB);

		for(BasicBlock::iterator II = BB->begin(); II != BB->end(); II ++ )
		{
			this->MayThrow |= II->mayThrow();
		}
	}

	vector<Instruction *> vecOut;
	vector<Instruction *> vecInv;

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

			if(this->setInstID.find(CI->getZExtValue()) != this->setInstID.end())
			{
				if(!pLoop->contains(BB))
				{
					vecOut.push_back(II);
					continue;
				}

				if(isa<LoadInst>(II))
				{
					if(hasLoopInvariantOperands(II, pLoop) && canSinkOrHoistInst(*II))
					{
						vecInv.push_back(II);
						continue;
					}

					vecInst.push_back(II);
				}					
				else if(isa<CallInst>(II) || isa<InvokeInst>(II))
				{
					if(hasLoopInvariantOperands(II, pLoop) && canSinkOrHoistInst(*II))
					{
						vecInv.push_back(II);
						continue;
					}

					vecInst.push_back(II);
				}
				else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
				{
					vecInst.push_back(pMem);
				}
				else
				{
					vecInst.push_back(II);
				}
			}
		}
	}



	vector<Instruction *>::iterator itVecBegin = vecOut.begin();
	vector<Instruction *>::iterator itVecEnd   = vecOut.end();

	errs() << "Instruction defined outside: " << vecOut.size() << "\n";

	for(; itVecBegin != itVecEnd; itVecBegin ++ )
	{
		PrintInstructionInfo(*itVecBegin);
	}

	errs() << "\n\n";

	itVecBegin = vecInv.begin();
	itVecEnd   = vecInv.end();

	errs() << "Invariant Instruction: " << vecInv.size() << "\n";

	for(; itVecBegin != itVecEnd; itVecBegin ++ )
	{
		PrintInstructionInfo(*itVecBegin);
	}


	itVecBegin = vecInst.begin();
	itVecEnd = vecInst.end();

	int numPHI = 0;

	for(; itVecBegin != itVecEnd; itVecBegin ++ )
	{
		if(isa<PHINode>(*itVecBegin))
		{
			numPHI++;
		}
	}

	errs() << "\n\nMonitored Instruction : " << vecInst.size() << " " << numPHI << " " << vecInst.size() - numPHI << "\n";

	itVecBegin = vecInst.begin();
	itVecEnd = vecInst.end();

	for(; itVecBegin != itVecEnd; itVecBegin ++ )
	{

		PrintInstructionInfo(*itVecBegin);
	}
	//exit(0);


}

void CrossInterationInstrument::CloneFunctionCalled(set<BasicBlock *> & setBlocksInLoop, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping)
{
	vector<Function *> vecWorkList;
	set<Function *> toDo;

	set<Instruction *> setMonitoredInstInCallee;

	set<BasicBlock *>::iterator itBlockSetBegin = setBlocksInLoop.begin();
	set<BasicBlock *>::iterator itBlockSetEnd   = setBlocksInLoop.end();

	for(; itBlockSetBegin != itBlockSetEnd; itBlockSetBegin ++)
	{
		BasicBlock * BB = * itBlockSetBegin;

		if(isa<UnreachableInst>(BB->getTerminator()))
		{
			continue;
		}

		for(BasicBlock::iterator II = (BB)->begin(); II != (BB)->end(); II ++ )
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

				if(this->LibraryTypeMapping.find(pCalled) != this->LibraryTypeMapping.end())
				{
					continue;
				}

				if(pCalled->isDeclaration() )
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
				
					if(pCalled != NULL && this->LibraryTypeMapping.find(pCalled) == this->LibraryTypeMapping.end() && !pCalled->isDeclaration() )
					{
						FuncCallSiteMapping[pCalled].insert(II);	
						
						if(toDo.find(pCalled) == toDo.end() )
						{
							toDo.insert(pCalled);
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
			
				if(this->setInstID.find(CI->getZExtValue()) != this->setInstID.end())
				{
					if(isa<LoadInst>(II) || isa<CallInst>(II) || isa<InvokeInst>(II) || isa<MemTransferInst>(II) )
					{
						setMonitoredInstInCallee.insert(II);
					}
					else
					{
						assert(0);
					}
				}
			}
		}
	}

	set<Function *>::iterator itSetFuncBegin = toDo.begin();
	set<Function *>::iterator itSetFuncEnd   = toDo.end();

	for(; itSetFuncBegin != itSetFuncEnd; itSetFuncBegin ++ )
	{
		Function * rawFunction = *itSetFuncBegin;
		Function * duplicateFunction = CloneFunction(rawFunction, VCalleeMap, false);
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
					pCall->setCalledFunction(clonedFunction);
				}
				else if(InvokeInst * pInvoke = dyn_cast<InvokeInst>(It->second))
				{
					pInvoke->setCalledFunction(clonedFunction);
				}
			}
		}
	}

	errs() << "Instruction inside callee: " << setMonitoredInstInCallee.size() << "\n";

	int iMemSet = 0;
	set<Instruction *>::iterator itMonInstBegin = setMonitoredInstInCallee.begin();
	set<Instruction *>::iterator itMonInstEnd   = setMonitoredInstInCallee.end();

	for(; itMonInstBegin != itMonInstEnd ; itMonInstBegin ++ )
	{
		ValueToValueMapTy::iterator It = VCalleeMap.find(*itMonInstBegin);
		assert(It != VCalleeMap.end());
		
		if(isa<LoadInst>(It->second))
		{
			BasicBlock::iterator next = cast<Instruction>(It->second);
			next ++;

			InlineHookLoad(cast<LoadInst>(It->second), next);
		}
		else if(isa<MemSetInst>(It->second) )
		{
			iMemSet ++;
			continue;
		}
		else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(It->second))
		{
			BasicBlock::iterator next = cast<Instruction>(It->second);
			next ++;

			InlineHookMem(pMem, next);
		}
		else if(isa<CallInst>(It->second))
		{
			BasicBlock::iterator next = cast<Instruction>(It->second);
			next ++;

			InlineHookInst(cast<Instruction>(It->second), next);
		}
		else if(InvokeInst * pInvoke = dyn_cast<InvokeInst>(It->second))
		{
			InlineHookInst(cast<Instruction>(It->second), pInvoke->getNormalDest()->getTerminator());
		}	
		else
		{
			assert(0);
		}
	}

	errs() << "MemSet: " << iMemSet << "\n";
}

void CrossInterationInstrument::InstrumentMain(Module * pModule)
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

			pStore = new StoreInst(this->ConstantLong32, this->iRecordSize_CPI, false, II);
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



bool CrossInterationInstrument::runOnModule(Module& M)
{
	this->pM = &M;
	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	ParseMonitoredInstFile(strMonitorInstFile, &M, this->setInstID, this->vecParaID);

	errs() << "Para size: " << this->vecParaID.size() << "\n";

	Function * pFunction = SearchFunctionByName(M, strFileName, strFuncName, uSrcLine);

	if(pFunction == NULL)
	{
		errs() << "Cannot find the function containing the inner loop!\n";
		return false;
	}

	LoopInfo * pLI = &(getAnalysis<LoopInfo>(*pFunction));
	Loop * pLoop;

	if(strLoopHeader == "")
	{
		pLoop = SearchLoopByLineNo(pFunction, pLI, uSrcLine);
	}
	else
	{
		BasicBlock * pHeader = SearchBlockByName(pFunction, strLoopHeader);

		if(pHeader == NULL)
		{
			errs() << "Cannot find the given loop header!\n";
			return false;
		}

		pLoop = pLI->getLoopFor(pHeader);
	}

	if(pLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return false;
	}

	this->AA = &getAnalysis<AliasAnalysis>();
	this->DL = getAnalysisIfAvailable<DataLayout>();

	this->CurAST = new AliasSetTracker(*(this->AA));

	vector<Instruction *> vecInst;
	CollectInstrumentedInst(pLoop, vecInst);

	SetupTypes(&M);
	SetupConstants(&M);
	SetupStruct(&M);
	SetupHooks(&M);
	SetupGlobals(&M);

	InstrumentMain(&M);

	CloneLoopBody(pLoop, vecInst);

	//BasicBlock * pNewHeader = SearchBlockByName(pFunction, ".oldheader.CPI");
	pFunction->dump();

	delete this->CurAST;
	return false;
}

