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
#include "Instrument/CLInstrument/CLInstrument.h"

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

void DumpInstructionSet( set<Instruction *> & setInst )
{
	char pPath[200];

	set<Instruction *>::iterator itSetBegin = setInst.begin();
	set<Instruction *>::iterator itSetEnd   = setInst.end();

	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		Instruction * pInst = * itSetBegin;

		MDNode *Node = pInst->getMetadata("ins_id");
		if(Node!=NULL)
		{
			assert(Node->getNumOperands() == 1);
			ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
			assert(CI);
			errs() << "Inst " << CI->getZExtValue() << ":";
		}

		pInst->dump();

		if( MDNode * N = pInst->getMetadata("dbg") )
		{
			DILocation Loc(N);
			string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
			realpath( sFileNameForInstruction.c_str() , pPath);
			sFileNameForInstruction = string(pPath);                        
			unsigned int uLineNoForInstruction = Loc.getLineNumber();
			errs() << "//---"<< sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
		}
	}
}

void DumpInstructionVector( vector<Instruction *> & vecInst )
{
	char pPath[200];

	vector<Instruction *>::iterator itVecBegin = vecInst.begin();
	vector<Instruction *>::iterator itVecEnd   = vecInst.end();

	for(; itVecBegin != itVecEnd; itVecBegin ++ )
	{
		Instruction * pInst = *itVecBegin;

		MDNode *Node = pInst->getMetadata("ins_id");
		if(Node!=NULL)
		{
			assert(Node->getNumOperands() == 1);
			ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
			assert(CI);
			errs() << "Inst " << CI->getZExtValue() << ":";
		}

		pInst->dump();

		if( MDNode * N = pInst->getMetadata("dbg") )
		{
			DILocation Loc(N);
			string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
			realpath( sFileNameForInstruction.c_str() , pPath);
			sFileNameForInstruction = string(pPath);                        
			unsigned int uLineNoForInstruction = Loc.getLineNumber();
			errs() << "//---"<< sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
		}
	}
}

void DumpLoadVector( vector<LoadInst *> & vecLoad )
{
	char pPath[200];

	vector<LoadInst *>::iterator itVecBegin = vecLoad.begin();
	vector<LoadInst *>::iterator itVecEnd   = vecLoad.end();

	for(; itVecBegin != itVecEnd; itVecBegin ++ )
	{
		LoadInst * pInst = *itVecBegin;

		MDNode *Node = pInst->getMetadata("ins_id");
		if(Node!=NULL)
		{
			assert(Node->getNumOperands() == 1);
			ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
			assert(CI);
			errs() << "Inst " << CI->getZExtValue() << ":";
		}

		pInst->dump();

		if( MDNode * N = pInst->getMetadata("dbg") )
		{
			DILocation Loc(N);
			string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
			realpath( sFileNameForInstruction.c_str() , pPath);
			sFileNameForInstruction = string(pPath);                        
			unsigned int uLineNoForInstruction = Loc.getLineNumber();
			errs() << "//---"<< sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
		}
	}
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

static cl::opt<std::string> strMainFunc("strMain",
					cl::desc("Main Function"), cl::Optional,
					cl::value_desc("strMain"));

static cl::opt<std::string> strLoopHeader("strLoopHeader",
					cl::desc("Block Name for Inner Loop"), cl::Optional,
					cl::value_desc("strLoopHeader"));

static cl::opt<std::string> strLibrary("strLibrary", 
					cl::desc("File Name for libraries"), cl::Optional, 
					cl::value_desc("strLibrary"));

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
	this->LongStarType = PointerType::get(this->LongType, 0);

}

void CrossLoopInstrument::SetupConstants(Module * pModule)
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
	ArgTypes.push_back(this->LongType);
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


/*
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
	else if(isa<PointerType>(pArg->getType()))
	{
		pCast = new PtrToIntInst(pArg, this->LongType, "", II);
		vecIndex.clear();
		vecIndex.push_back(this->ConstantInt0);
		vecIndex.push_back(this->ConstantInt1);
		const_ptr = ConstantExpr::getGetElementPtr(ParaRecord_ptr, vecIndex);
		pStore = new StoreInst(pCast, const_ptr, false, II);
		pStore->setAlignment(8);
	}
	else
	{
		assert(0);
	}

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

void CrossLoopInstrument::InlineHookPara(Argument * pArg, Instruction * II)
{

	Function * pFunction = II->getParent()->getParent();
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
	Instruction * ParaRecord_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	PointerType * stParaRecord_PT = PointerType::get(this->struct_stParaRecord, 0);
	CastInst * pParaRecord = new BitCastInst(ParaRecord_ptr, stParaRecord_PT, "", II);

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
	pStore = new StoreInst(pID, const_ptr, false, II);
	pStore->setAlignment(4);

	if(IntegerType * pIntType = dyn_cast<IntegerType>(pArg->getType()))
	{
		if(pIntType->getBitWidth() == 64)
		{
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt1);
			const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
			pStore = new StoreInst(pArg, const_ptr, false, II);
			pStore->setAlignment(8);
		}
		else
		{
			pCast = CastInst::CreateIntegerCast(pArg, this->LongType, true, "", II);
			vecIndex.clear();
			vecIndex.push_back(this->ConstantInt0);
			vecIndex.push_back(this->ConstantInt1);
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
		vecIndex.push_back(this->ConstantInt1);
		const_ptr = GetElementPtrInst::Create(pParaRecord, vecIndex, "", II);
		pStore = new StoreInst(pCast, const_ptr, false, II);
		pStore->setAlignment(8);
	}
	else
	{
		assert(0);
	}

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}


/*
void CrossLoopInstrument::InlineHookLoad(LoadInst * pLoad)
{
	BasicBlock::iterator II = pLoad;
	II ++;
	Instruction* const_ptr;
	StoreInst * pStore;
	CastInst * pCast1 = new PtrToIntInst(pLoad->getPointerOperand(), this->LongType, "", II);
	CastInst * pCast2 = NULL;

	LoadInst * pLoadPointer = new LoadInst(this->pcBuffer_CPI, "", false, II);
	pLoadPointer->setAlignment(8);
	LoadInst * pLoadIndex   = new LoadInst(this->iBufferIndex_CPI, "", false, II);
	pLoadIndex->setAlignment(8);

	GetElementPtrInst* getElementPtr = GetElementPtrInst::Create(pLoadPointer, pLoadIndex, "", II);
	CastInst * pStoreAddress = new BitCastInst(getElementPtr, this->PT_struct_stLogRecord, "", II);

	vector<Value *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
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
	const_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	pStore = new StoreInst(CI, const_ptr, false, II);
	pStore->setAlignment(4);

	LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	pLoadRecordSize->setAlignment(8);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);

}

*/


void CrossLoopInstrument::InlineHookLoad(LoadInst * pLoad)
{
	if(pLoad->getType()->isVectorTy())
	{
		return;
	}
	
	BasicBlock::iterator II = pLoad;
	II ++;
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
	else if(pLoad->getType()->isDoubleTy())
	{
		CastInst * pCast = new FPToSIInst(pLoad, this->LongType, "", II);
		pStore = new StoreInst(pCast, const_ptr, false, II);
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



void CrossLoopInstrument::InlineHookInst(Instruction * pI, Instruction * II)
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
	PointerType * stInstRecord_PT  = PointerType::get(this->struct_stInstRecord, 0);
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
		pCast = new FPToSIInst(pI, this->LongType, "", II);
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

/*
void CrossLoopInstrument::InlineHookDelimit(Instruction * II)
{
	
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

	
	LoadInst * pLoad = new LoadInst(this->numGlobalCounter, "", false, II);
	pLoad->setAlignment(8);
	

	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt1);
	Instruction * DelimitRecord_ptr = GetElementPtrInst::Create(pStoreAddress, vecIndex, "", II);
	PointerType * DelimitRecord_PT = PointerType::get(this->struct_stDelimiterRecord, 0);
	CastInst * pDelimitRecord = new BitCastInst(DelimitRecord_ptr, DelimitRecord_PT, "", II);


	vecIndex.clear();
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	const_ptr = GetElementPtrInst::Create(pDelimitRecord, vecIndex, "", II);

	pStore = new StoreInst(pLoad, const_ptr, false, II);
	pStore->setAlignment(8);

	//LoadInst * pLoadRecordSize = new LoadInst(this->iRecordSize_CPI, "", false, II);
	//pLoadRecordSize->setAlignment(8);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, this->ConstantLong32, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);
}
*/


void CrossLoopInstrument::InlineHookDelimit(Instruction * II)
{
	
	vector<Constant *> vecIndex;
	vecIndex.push_back(this->ConstantInt0);
	vecIndex.push_back(this->ConstantInt0);
	Constant* const_ptr = ConstantExpr::getGetElementPtr(this->Record_CPI, vecIndex);
	StoreInst * pStore = new StoreInst(this->ConstantInt4, const_ptr, false, II);
	pStore->setAlignment(4);

	LoadInst * pLoad = new LoadInst(this->numGlobalCounter, "", false, II);
	pLoad->setAlignment(8);
	
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

	pStore = new StoreInst(pLoad, const_ptr, false, II);
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
	//vecParam.push_back(this->ConstantLong32);
	vecParam.push_back(this->ConstantInt1);
	vecParam.push_back(this->ConstantIntFalse);

	
	CallInst * pCall = CallInst::Create(this->func_llvm_memcpy, vecParam, "", II);
	pCall->setCallingConv(CallingConv::C);
	pCall->setTailCall(false);
	AttributeSet AS;
	pCall->setAttributes(AS);

	BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, pLoadRecordSize, "", II);
	
	//BinaryOperator * pAdd = BinaryOperator::Create(Instruction::Add, pLoadIndex, this->ConstantLong32, "", II);
	pStore = new StoreInst(pAdd, this->iBufferIndex_CPI, false, II);
	pStore->setAlignment(8);
}



void CrossLoopInstrument::InlineHookMem(MemTransferInst * pMem, Instruction * II)
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
	PointerType * stMemRecord_PT = PointerType::get( this->struct_stMemRecord, 0);
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
void CrossLoopInstrument::InlineHookMem(MemTransferInst * pMem, Instruction * II)
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

void CrossLoopInstrument::InstrumentMain(Module * pModule)
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


void CrossLoopInstrument::CollectInstrumentedInst(set<int> & setIndex, Loop * pLoop, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecIn, vector<Instruction *> & vecOut, vector<MemTransferInst *> & vecMem)
{
	set<BasicBlock *> setLoopBlocks;
	set<Instruction *> setDirectlyUsedInstruction;
	for(Loop::block_iterator BB = pLoop->block_begin() ; BB != pLoop->block_end(); BB ++)
	{
		setLoopBlocks.insert(*BB);

		for(BasicBlock::iterator II = (*BB)->begin(); II != (*BB)->end(); II ++ )
		{
			for(unsigned index = 0; index < II->getNumOperands(); index ++)
			{
				if(Instruction * pI = dyn_cast<Instruction>(II->getOperand(index)))
				{
					setDirectlyUsedInstruction.insert(pI);
				}
			}
		}
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
					if(setDirectlyUsedInstruction.find(II) != setDirectlyUsedInstruction.end())
					{
						vecOut.push_back(II);
					}
				}
				else
				{
					if(isa<LoadInst>(II))
					{
						vecLoad.push_back(cast<LoadInst>(II));
					}					
					else if(isa<CallInst>(II) || isa<InvokeInst>(II))
					{
						vecIn.push_back(II);
					}
					else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(II))
					{
						vecMem.push_back(pMem);
					}
					else
					{
						assert(0);
					}
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
	pAdd = BinaryOperator::Create(Instruction::Add, pLoadnumGlobalCounter, this->ConstantLong1, "add", pHeader->getTerminator());
	pStore = new StoreInst(pAdd, this->numGlobalCounter, false, pHeader->getTerminator());
	pStore->setAlignment(8);

	//pOuterLoop->getHeader()->dump();

}


void CrossLoopInstrument::CloneFunctionCalled(set<BasicBlock *> & setBlocksInLoop, ValueToValueMapTy & VCalleeMap, map<Function *, set<Instruction *> > & FuncCallSiteMapping)
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
			
				if(this->MonitoredElems.MonitoredInst.find(CI->getZExtValue()) != this->MonitoredElems.MonitoredInst.end())
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

	set<Instruction *>::iterator itMonInstBegin = setMonitoredInstInCallee.begin();
	set<Instruction *>::iterator itMonInstEnd   = setMonitoredInstInCallee.end();

	for(; itMonInstBegin != itMonInstEnd ; itMonInstBegin ++ )
	{
		//assert(isa<LoadInst>(*itMonInstBegin));
		ValueToValueMapTy::iterator It = VCalleeMap.find(*itMonInstBegin);
		assert(It != VCalleeMap.end());
		
		if(isa<LoadInst>(It->second))
		{
			InlineHookLoad(cast<LoadInst>(It->second));
		}
		else if(isa<MemSetInst>(It->second) )
		{
			
			continue;
		}
		else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(It->second))
		{
			BasicBlock::iterator next = cast<Instruction>(It->second);
			next ++;

			InlineHookMem(pMem, next);
		}
		else if(isa<CallInst>(It->second) || isa<InvokeInst>(It->second))
		{
			BasicBlock::iterator next = cast<Instruction>(It->second);
			next ++;

			InlineHookInst(cast<Instruction>(It->second), next);
		}	
		else
		{
			assert(0);
		}
	}

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

	BasicBlock * pPostDominator = ExitBlocks[0];

	for(unsigned long i = 1; i < ExitBlocks.size(); i++ )
	{		
		if(pPostDominator == NULL)
		{
			break;
		}

		pPostDominator = pPDT->findNearestCommonDominator(pPostDominator, ExitBlocks[i]);
	}

	if(pPostDominator != NULL)
	{
		return pPostDominator;
	}

	set<BasicBlock*> setExitBlocks;

	for(unsigned long i = 0; i < ExitBlocks.size(); i ++)
	{
		setExitBlocks.insert(ExitBlocks[i]);
	}

	if(setExitBlocks.size() == 1)
	{
		pPostDominator = *(setExitBlocks.begin());
		return pPostDominator;
	}


/*
	set<BasicBlock *>::iterator itSetBegin = setExitBlocks.begin();
	set<BasicBlock *>::iterator itSetEnd   = setExitBlocks.end();

	int count = 0;
	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		set<BasicBlock *>::iterator itTmpBegin = setExitBlocks.begin();
		set<BasicBlock *>::iterator itTmpEnd   = setExitBlocks.end();

		bool bFlag = true;

		for(; itTmpBegin != itTmpEnd; itTmpBegin ++)
		{
			if(*itSetBegin == *itTmpBegin)
			{
				continue;
			}

			if(!IsReachable(*itTmpBegin, *itSetBegin))
			{
				bFlag = false;
				break;
			}
		}

		if(bFlag)
		{
			count ++;
			pPostDominator = * itSetBegin;
		}
	}

	assert(count == 1);
*/

	return NULL;

}


void CrossLoopInstrument::CreateIfElseIfBlock(Loop * pInnerLoop, vector<BasicBlock *> & vecAdded)
{
	BasicBlock * pCondition1 = NULL;
	BasicBlock * pCondition2 = NULL;
	
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

	Function * pInnerFunction = pInnerLoop->getHeader()->getParent();
	Module * pModule = pInnerFunction->getParent();

	pCondition1 = pInnerLoop->getLoopPreheader();
	BasicBlock * pHeader = pInnerLoop->getHeader();

	pCondition2 = BasicBlock::Create(pModule->getContext(), ".if2.CPI", pInnerFunction, 0);
	
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
		pAddOne = BinaryOperator::Create(Instruction::Add, pLoadnumGlobalCounter, this->ConstantLong1, "add", pTerminator);
		pStoreNew = new StoreInst(pAddOne, this->numGlobalCounter, false, pTerminator);
		pStoreNew->setAlignment(8);
	}

	pLoad1 = new LoadInst(this->numGlobalCounter, "", false, pTerminator);
	pLoad1->setAlignment(8);
	pLoad2 = new LoadInst(this->CURRENT_SAMPLE, "", false, pTerminator);
	pLoad2->setAlignment(8);
	pCmp = new ICmpInst(pTerminator, ICmpInst::ICMP_SLT, pLoad1, pLoad2, "");
	pBranch = BranchInst::Create(pHeader, pCondition2, pCmp );
	ReplaceInstWithInst(pTerminator, pBranch);

	//condition2
	pBinary = BinaryOperator::Create(Instruction::Add, pLoad2, this->ConstantLong1, "", pCondition2);
	pCmp = new ICmpInst(*pCondition2, ICmpInst::ICMP_EQ, pLoad1, pBinary, "");
	BranchInst::Create(pIfBody, pElseBody, pCmp, pCondition2);

	//
	pLoad1 = new LoadInst(this->SAMPLE_RATE, "", false, pIfBody);
	pCall = CallInst::Create(this->geo, pLoad1, "", pIfBody);
  	pCall->setCallingConv(CallingConv::C);
  	pCall->setTailCall(false);
  	pCall->setAttributes(emptySet);

  	CastInst * pCast = CastInst::CreateIntegerCast(pCall, this->LongType, true, "", pIfBody);
  	//pBinary = BinaryOperator::Create(Instruction::Add, pLoad2, pCast, "add", pIfBody);
  	pStore = new StoreInst(pCast, this->CURRENT_SAMPLE, false, pIfBody);
  	pStore->setAlignment(8);

  	pStore = new StoreInst(this->ConstantLong0, this->numGlobalCounter, false, pIfBody);
  	pStore->setAlignment(8);
  	BranchInst::Create(pElseBody, pIfBody);



	vecAdded.push_back(pCondition1);
	vecAdded.push_back(pCondition2);
	vecAdded.push_back(pIfBody);
	vecAdded.push_back(pElseBody);


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


void CrossLoopInstrument::CloneInnerLoop(Loop * pLoop, vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap)
{
	Function * pFunction = pLoop->getHeader()->getParent();

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
	BasicBlock * pCondition1 = vecAdd[0];
	BasicBlock * pElseBody   = vecAdd[3];

	BasicBlock * pClonedHeader = cast<BasicBlock>(VMap[pLoop->getHeader()]);

	BranchInst::Create(pClonedHeader, pElseBody);

	for(BasicBlock::iterator II = pClonedHeader->begin(); II != pClonedHeader->end(); II ++ )
	{
		if(PHINode * pPHI = dyn_cast<PHINode>(II))
		{
			vector<int> vecToRemoved;
			for (unsigned i = 0, e = pPHI->getNumIncomingValues(); i != e; ++i) 
			{
				if(pPHI->getIncomingBlock(i) == pCondition1)
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

void CrossLoopInstrument::AddHooksToSkippableLoad(set<LoadInst *> & setLoad, LoopInfo * pLI, ValueToValueMapTy &VMap, set<Value *> & setMonitoredValue, BasicBlock * pCondition2)
{
	set<LoadInst *>::iterator itSetLoadBegin = setLoad.begin();
	set<LoadInst *>::iterator itSetLoadEnd   = setLoad.end();

	BasicBlock * pNewHeader = pCondition2->getTerminator()->getSuccessor(0);

	Loop * pClonedLoop = pLI->getLoopFor(pNewHeader);



	for(; itSetLoadBegin != itSetLoadEnd; itSetLoadBegin ++ )
	{
		LoadInst * pCurrentLoad = *itSetLoadBegin;

		

		LoadInst * pClonedLoad = cast<LoadInst>(VMap[pCurrentLoad]);

		if(this->PossibleSkipLoadInfoMapping[pCurrentLoad][1].size() != 1 )
		{	
			InlineHookLoad(pClonedLoad);
			continue;
		}

		if(this->PossibleSkipLoadInfoMapping[pCurrentLoad][2].size() != 1)
		{
			InlineHookLoad(pClonedLoad);
			continue;
		}

		pCurrentLoad->dump();

		Loop * pCurrentLoop = pLI->getLoopFor(pClonedLoad->getParent());

		Value * pInit = *(this->PossibleSkipLoadInfoMapping[pCurrentLoad][1].begin());

		if(setMonitoredValue.find(pInit) == setMonitoredValue.end())
		{
			if(Argument * pArg = dyn_cast<Argument>(pInit))
			{
				InlineHookPara(pArg, pCondition2->getTerminator());
			}
			else if(Instruction * pInst = dyn_cast<Instruction>(pInit))
			{
				if(pCurrentLoop == pClonedLoop)
				{
					InlineHookInst(pInst, pCondition2->getTerminator());
				}
				else if(VMap.find(pInst) == VMap.end())
				{
					InlineHookInst(pInst, pCondition2->getTerminator());
				}
				else
				{
					BasicBlock * pPreHeader = pCurrentLoop->getLoopPreheader();
					Instruction * pClonedInst = cast<Instruction>(VMap[pInst]);
					InlineHookInst(pClonedInst, pPreHeader->getTerminator());
				}
			}
		}


		Value * pIndexValue = *(this->PossibleSkipLoadInfoMapping[pCurrentLoad][2].begin());

		if(setMonitoredValue.find(pIndexValue) == setMonitoredValue.end())
		{
			assert(isa<Instruction>(pIndexValue));
			Instruction * pInst = cast<Instruction>(pIndexValue);
			Instruction * pClonedInst = cast<Instruction>(VMap[pInst]);

			SmallVector<BasicBlock*, 8> ExitBlocks;
			pCurrentLoop->getExitBlocks(ExitBlocks);

			set<BasicBlock *> ExitBlockSet(ExitBlocks.begin(), ExitBlocks.end());

			set<BasicBlock *>::iterator itSetBlockBegin = ExitBlockSet.begin();
			set<BasicBlock *>::iterator itSetBlockEnd = ExitBlockSet.end();

			for(; itSetBlockBegin != itSetBlockEnd; itSetBlockBegin ++ )
			{
				if(pCurrentLoop == pClonedLoop)
				{
					BasicBlock * pExit = RewriteLoopExitBlock(pCurrentLoop, *itSetBlockBegin, this);
					InlineHookInst(pClonedInst, pExit->getFirstInsertionPt());
				}
				else
				{
					InlineHookInst(pClonedInst, (*itSetBlockBegin)->getFirstInsertionPt());
				}		
			}
		}
		
	}

}


void CrossLoopInstrument::AddHooksToInnerLoop(vector<BasicBlock *> & vecAdd, ValueToValueMapTy & VMap, vector<LoadInst *> & vecLoad, vector<Instruction *> & vecIn, vector<Instruction *> & vecOut, vector<MemTransferInst *> & vecMem)
{
	BasicBlock * pCondition2 = vecAdd[1];
	BasicBlock * pElseBody = vecAdd[3];

	Function * pCurrent = pElseBody->getParent();

	AttributeSet attSet;
	BasicBlock::iterator pFirstInsert = pCondition2->getFirstInsertionPt();

	//return;
	InlineHookDelimit(pFirstInsert);

	//return;

	TerminatorInst * pTerminator = pElseBody->getTerminator();
	vector<pair<Function *, int> >::iterator itParaBegin = this->MonitoredElems.MonitoredPara.begin();
	vector<pair<Function *, int> >::iterator itParaEnd   = this->MonitoredElems.MonitoredPara.end();

	set<Value *> setMonitoredValue;

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
			setMonitoredValue.insert(pArg);
			InlineHookPara(pArg, pTerminator);
		}
	}

	vector<Instruction *>::iterator itInstVecBegin = vecOut.begin();
	vector<Instruction *>::iterator itInstVecEnd = vecOut.end();
	
	for(; itInstVecBegin != itInstVecEnd; itInstVecBegin ++ )
	{
		InlineHookInst(*itInstVecBegin, pTerminator);
		setMonitoredValue.insert(*itInstVecBegin);
	}



	vector<Instruction *>::iterator itInstInBegin = vecIn.begin();
	vector<Instruction *>::iterator itInstInEnd   = vecIn.end();

	set<Instruction *> setMonitoredInInst;

	for(; itInstInBegin != itInstInEnd; itInstInBegin ++ )
	{
		Instruction * pInst = cast<Instruction>(VMap[*itInstInBegin]);
		InlineHookInst(pInst, pInst->getParent()->getTerminator());
		setMonitoredValue.insert(*itInstInBegin);
	}

	vector<MemTransferInst *>::iterator itMemBegin = vecMem.begin();
	vector<MemTransferInst *>::iterator itMemEnd   = vecMem.end();

	for(; itMemBegin != itMemEnd; itMemBegin ++ )
	{
		MemTransferInst * pMem = cast<MemTransferInst>(VMap[*itMemBegin]);
		InlineHookMem(pMem, pMem->getParent()->getTerminator());
	}

	vector<LoadInst *>::iterator itLoadVecBegin = vecLoad.begin();
	vector<LoadInst *>::iterator itLoadVecEnd = vecLoad.end();

	set<LoadInst *> setSkippedLoad;

	for(; itLoadVecBegin != itLoadVecEnd; itLoadVecBegin++ )
	{
		LoadInst * pLoad = cast<LoadInst>(VMap[*itLoadVecBegin]);

		if(this->PossibleSkipLoadInfoMapping.find(*itLoadVecBegin) != this->PossibleSkipLoadInfoMapping.end())
		{
			setSkippedLoad.insert(*itLoadVecBegin);
		}
		else
		{ 
			InlineHookLoad(pLoad);
		}
	}

	if(setSkippedLoad.size() > 0)
	{
		LoadInst * bFirstLoad = (*setSkippedLoad.begin());
		Function * pCurrentFunction = bFirstLoad->getParent()->getParent();
		LoopInfo * pCurrentLI = &(getAnalysis<LoopInfo>(*pCurrentFunction));
		
		AddHooksToSkippableLoad(setSkippedLoad, pCurrentLI, VMap, setMonitoredValue, pElseBody);

	}
}


void CrossLoopInstrument::InstrumentInnerLoop(Loop * pInnerLoop, PostDominatorTree * PDT)
{
	set<BasicBlock *> setBlocksInLoop;

	for(Loop::block_iterator BB = pInnerLoop->block_begin(); BB != pInnerLoop->block_end(); BB ++ )
	{
		setBlocksInLoop.insert(*BB);
	}

	ValueToValueMapTy VCalleeMap;
	map<Function *, set<Instruction *> > FuncCallSiteMapping;

	//add hooks to function called inside the loop
	CloneFunctionCalled(setBlocksInLoop, VCalleeMap, FuncCallSiteMapping);

	vector<LoadInst *> vecLoad;
	vector<Instruction *> vecIn;
	vector<Instruction *> vecOut;
	vector<MemTransferInst *> vecMem;

	CollectInstrumentedInst(this->MonitoredElems.MonitoredInst, pInnerLoop, vecLoad, vecIn, vecOut, vecMem);

	//created auxiliary basic block
	vector<BasicBlock *> vecAdd;
	CreateIfElseIfBlock(pInnerLoop, vecAdd);
	
	//clone loop
	ValueToValueMapTy VMap;
	CloneInnerLoop(pInnerLoop, vecAdd, VMap);

	//add loop related hooks
	AddHooksToInnerLoop(vecAdd, VMap, vecLoad, vecIn, vecOut, vecMem);

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

void CrossLoopInstrument::ParseInstFile(Function * pInnerFunction, Module * pModule)
{
	//errs() << strMonitorInstFile << "\n";
	ParseFeaturedInstFile(strMonitorInstFile, pModule, this->MonitoredElems);

	//errs() << this->MonitoredElems.vecFileContent.size() << "\n";

	for(size_t i = 0; i < this->MonitoredElems.vecFileContent.size(); i ++ )
	{
		vector<vector<pair<int, int > > > vecIndex;
		if(PossibleArrayAccess(this->MonitoredElems.vecFileContent[i], vecIndex))
		{
			LoadInst * pLoad = cast<LoadInst>(SearchLineValue(this->MonitoredElems.vecFileContent[i][0], pInnerFunction));

			//pLoad->dump();

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

	//exit(0);
}

bool CrossLoopInstrument::runOnModule(Module& M)
{

	if(strLibrary != "" )
	{
		ParseLibraryFunctionFile(strLibrary, &M, this->LibraryTypeMapping);
	}

	if(strOuterFileName != "")
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
		return true;
	}

	ParseInstFile(pInnerFunction, &M);

	PostDominatorTree * PDT = &getAnalysis<PostDominatorTree>(*pInnerFunction);
	LoopInfo * pInnerLI = &(getAnalysis<LoopInfo>(*pInnerFunction));
	Loop * pInnerLoop;

	if(strLoopHeader == "")
	{
		pInnerLoop = SearchLoopByLineNo(pInnerFunction, pInnerLI, uInnerSrcLine);
	}
	else
	{
		BasicBlock * pHeader = SearchBlockByName(pInnerFunction, strLoopHeader);
		if(pHeader == NULL)
		{
			errs() << "Cannot find the given loop header!\n";
			return true;
		}

		pInnerLoop = pInnerLI->getLoopFor(pHeader);
	}

	if(pInnerLoop == NULL)
	{
		errs() << "Cannot find the inner loop!\n";
		return true;
	}

	BasicBlock * pInnerHeader = pInnerLoop->getHeader();

	LoopSimplify(pInnerLoop, this);

	pInnerLoop = pInnerLI->getLoopFor(pInnerHeader);

	InstrumentInnerLoop(pInnerLoop, PDT);

	pInnerFunction->dump();
	return true;
}

