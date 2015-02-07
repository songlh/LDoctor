#include "llvm-Commons/Search/Search.h"
#include "llvm-Commons/Utility/Utility.h"
#include "llvm-Commons/Config/Config.h"
#include "llvm-Commons/Invariant/InvariantAnalysis.h"

#include "Redundancy/FFR-Redundancy/FFRRedundancy.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/Use.h"

using namespace std;
using namespace llvm;
using namespace llvm_Commons;


bool OnlyWrite(Argument * pArg)
{

	vector<Instruction *> vecWorkList;
	set<Instruction *> setProcessed;

	for(Value::use_iterator ub = pArg->use_begin(); ub != pArg->use_end(); ub ++ )
	{
		if(isa<LoadInst>(*ub))
		{
			return false;
		}
		else if(isa<CastInst>(*ub))
		{
			setProcessed.insert(cast<Instruction>(*ub));
			vecWorkList.push_back(cast<Instruction>(*ub));
		}
		else if(isa<GetElementPtrInst>(*ub))
		{
			setProcessed.insert(cast<Instruction>(*ub));
			vecWorkList.push_back(cast<Instruction>(*ub));
		}
		else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(*ub))
		{
			if(pMem->getOperand(1) == pArg )
			{
				return false;
			}
		}
		
	}

	while(vecWorkList.size() > 0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		for(Value::use_iterator ub = pCurrent->use_begin(); ub != pCurrent->use_end(); ub ++ )
		{
			if(isa<LoadInst>(*ub))
			{
				
				return false;
			}
			else if(isa<CastInst>(*ub))
			{
				if(setProcessed.find(cast<Instruction>(*ub)) == setProcessed.end() )
				{
					setProcessed.insert(cast<Instruction>(*ub));
					vecWorkList.push_back(cast<Instruction>(*ub));
				}
			}
			else if(isa<GetElementPtrInst>(*ub))
			{
				if(setProcessed.find(cast<Instruction>(*ub)) == setProcessed.end() )
				{
					setProcessed.insert(cast<Instruction>(*ub));
					vecWorkList.push_back(cast<Instruction>(*ub));
				}
			}
			else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(*ub))
			{
				if(pMem->getOperand(1) == pCurrent )
				{

					return false;
				}
			}
			
			
		}
	}

	return true;
}


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


static RegisterPass<FFRRedundancy> X(
		"ff-recursive-redundancy",
		"ff recursive redundancy analysis",
		false,
		true);

char FFRRedundancy::ID = 0;

void FFRRedundancy::getAnalysisUsage(AnalysisUsage &AU) const 
{
	AU.setPreservesAll();
	AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfo>();
	AU.addRequired<DataLayout>();
	AU.addRequired<InterProcDep>();
}

FFRRedundancy::FFRRedundancy(): ModulePass(ID) 
{
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	initializeDataLayoutPass(Registry);
	initializePostDominatorTreePass(Registry);
	
}

void FFRRedundancy::print(raw_ostream &O, const Module *M) const
{
	return;
}




//get all side effect instruction
//check and prune the dependence 
void FFRRedundancy::DependenceAnalysis(set<Value *> & setDependingValues, Function * pFunction )
{
	set<StoreInst *>::iterator itStoreSetBegin = this->IPD->StartEffectStoreMapping[pFunction].begin();
	set<StoreInst *>::iterator itStoreSetEnd   = this->IPD->StartEffectStoreMapping[pFunction].end();

	for(; itStoreSetBegin != itStoreSetEnd; itStoreSetBegin ++)
	{
		Function * pContain = (*itStoreSetBegin)->getParent()->getParent();

		set<Value *>::iterator itValSetBegin   = this->IPD->StartFuncValueDependenceMappingMappingMapping[pFunction][pContain][*itStoreSetBegin].begin();
		set<Value *>::iterator itValSetEnd     = this->IPD->StartFuncValueDependenceMappingMappingMapping[pFunction][pContain][*itStoreSetBegin].end();

		for(; itValSetBegin != itValSetEnd; itValSetBegin++)
		{
			setDependingValues.insert(*itValSetBegin);
		}
	}


	set<MemIntrinsic *>::iterator itMemSetBegin = this->IPD->StartEffectMemMapping[pFunction].begin();
	set<MemIntrinsic *>::iterator itMemSetEnd   = this->IPD->StartEffectMemMapping[pFunction].end();

	for(; itMemSetBegin != itMemSetEnd; itMemSetBegin ++ )
	{
		if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(*itMemSetBegin))
		{
			if(this->IPD->StartMemTypeMappingMapping[pFunction][pMem].second != MO_LOCAL )
			{
				setDependingValues.insert(*itMemSetBegin);
				continue;
			}

		}


		Function * pContain = (*itMemSetBegin)->getParent()->getParent();

		set<Value *>::iterator itValSetBegin   = this->IPD->StartFuncValueDependenceMappingMappingMapping[pFunction][pContain][*itMemSetBegin].begin();
		set<Value *>::iterator itValSetEnd     = this->IPD->StartFuncValueDependenceMappingMappingMapping[pFunction][pContain][*itMemSetBegin].end();

		for(; itValSetBegin != itValSetEnd; itValSetBegin++)
		{
			setDependingValues.insert(*itValSetBegin);				
		}
	}

	set<Instruction *>::iterator itCallSetBegin = this->IPD->StartLibraryCallMapping[pFunction].begin();
	set<Instruction *>::iterator itCallSetEnd   = this->IPD->StartLibraryCallMapping[pFunction].end();

	for(; itCallSetBegin != itCallSetEnd; itCallSetBegin ++ )
	{
		Function * pContain = (*itCallSetBegin)->getParent()->getParent();

		set<Value *>::iterator itValSetBegin   = this->IPD->StartFuncValueDependenceMappingMappingMapping[pFunction][pContain][*itCallSetBegin].begin();
		set<Value *>::iterator itValSetEnd     = this->IPD->StartFuncValueDependenceMappingMappingMapping[pFunction][pContain][*itCallSetBegin].end();

		for(; itValSetBegin != itValSetEnd; itValSetBegin++)
		{				
			setDependingValues.insert(*itValSetBegin);
		}
	}

}

void FFRRedundancy::PruneDependenceResult(set<Value *> & setDependingValues, Function * pFunction)
{
	set<Function *> setLibraries;

	map<Function *, LibraryFunctionType>::iterator itMapLibraryBegin = LibraryTypeMapping.begin();
	map<Function *, LibraryFunctionType>::iterator itMapLibraryEnd   = LibraryTypeMapping.end();

	for(; itMapLibraryBegin != itMapLibraryEnd; itMapLibraryBegin ++ )
	{
		setLibraries.insert(itMapLibraryBegin->first);
	}

	set<Function *> setScope;

	BuildScope(pFunction, setScope, setLibraries);

	set<Value *> setInvariantGV;
	set<Value *> setArray;
	IndentifyInvariantGlobalVariable(pFunction, setInvariantGV, setScope);
	IndentifyInvariantArray(pFunction, setArray, setScope);

	set<Value *> setTOBERemoved;

	set<Value *>::iterator itSetValueBegin = setDependingValues.begin();
	set<Value *>::iterator itSetValueEnd   = setDependingValues.end();

	for(; itSetValueBegin != itSetValueEnd; itSetValueBegin ++ )
	{
		if(LoadInst * pLoad = dyn_cast<LoadInst>(*itSetValueBegin))
		{
			Value * pBase = GetUnderlyingObject(pLoad->getPointerOperand(), this->pDL);

			if(setInvariantGV.find(pBase) != setInvariantGV.end() || setArray.find(pBase) != setArray.end())
			{
				setTOBERemoved.insert(pLoad);
			}
		}
		else if(MemTransferInst * pMem = dyn_cast<MemTransferInst>(*itSetValueBegin))
		{
			Value * pBase = GetUnderlyingObject(pMem->getRawSource(), this->pDL);

			if(setInvariantGV.find(pBase) != setInvariantGV.end() || setArray.find(pBase) != setArray.end())
			{
				setTOBERemoved.insert(pMem);
			}
		}
	}


	itSetValueBegin = setTOBERemoved.begin();
	itSetValueEnd   = setTOBERemoved.end();

	for(; itSetValueBegin != itSetValueEnd; itSetValueBegin++)
	{
		setDependingValues.erase(*itSetValueBegin);
	}
}

void FFRRedundancy::PruneArgument(set<Value *> & setDependingValues, Function * pFunction)
{
	for(Function::arg_iterator argBegin = pFunction->arg_begin(); argBegin != pFunction->arg_end(); argBegin ++ )
	{
		if(isa<PointerType>(argBegin->getType()))
		{
			if(OnlyWrite(argBegin))
			{
				argBegin->dump();
			}

			break;
		}
	}
}



bool FFRRedundancy::runOnModule(Module& M)
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

	this->pDL = &getAnalysis<DataLayout>();


	set<Function *> setFunctions;
	setFunctions.insert(pFunction);



	this->IPD = &getAnalysis<InterProcDep>();
	this->IPD->InitlizeStartFunctionSet(setFunctions);
	this->IPD->LibraryTypeMapping = this->LibraryTypeMapping;
	this->IPD->InterProcDependenceAnalysis();


	set<Value *> setValue;

	DependenceAnalysis(setValue, pFunction );

	PruneDependenceResult(setValue, pFunction);

	set<Value *>::iterator itSetBegin = setValue.begin();
	set<Value *>::iterator itSetEnd   = setValue.end();

	char pPath[100];

	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		if(Instruction * pInst = dyn_cast<Instruction>(*itSetBegin))
		{
			if(isa<AllocaInst>(pInst))
			{
				continue;
			}


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
		else if(Argument * pArg = dyn_cast<Argument>(*itSetBegin))
		{
			Function * pFunction = pArg->getParent();
			MDNode *Node = pFunction->begin()->begin()->getMetadata("func_id");
			if(Node!=NULL)
			{
				assert(Node->getNumOperands() == 1);
				ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
				assert(CI);
				errs() << "Func " << pFunction->getName() << " " << CI->getZExtValue() << " " << pArg->getArgNo() << ": ";
			}

			pArg->dump();
		}
		else
		{
			if(isa<Function>(*itSetBegin))
			{
				continue;
			}

			(*itSetBegin)->dump();
		}
	}



	return false;
}
