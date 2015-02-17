
#include <fstream>

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Metadata.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm-Commons/Config/Config.h"

using namespace llvm;
using namespace std;


namespace llvm_Commons
{

Function * CloneFunctionWithExtraArguments(const Function * F, ValueToValueMapTy & VMap, bool ModuleLevelChanges, 
	vector<Type *> & ExtraArguments, ClonedCodeInfo * CodeInfo )
{

	vector<Type *> ArgTypes;

	for(Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; ++ I)
	{
		if(VMap.count(I) == 0 )
		{
			ArgTypes.push_back(I->getType());
		}
	}

	vector<Type *>::iterator itTypeBegin = ExtraArguments.begin();
	vector<Type *>::iterator itTypeEnd   = ExtraArguments.end();

	for(;itTypeBegin != itTypeEnd; itTypeBegin ++)
	{
		ArgTypes.push_back(*itTypeBegin);
	}

	// Create a new function type...
	FunctionType *FTy = FunctionType::get(F->getFunctionType()->getReturnType(), ArgTypes, F->getFunctionType()->isVarArg());

	// Create the new function...
	Function *NewF = Function::Create(FTy, F->getLinkage(), F->getName());

	// Loop over the arguments, copying the names of the mapped arguments over...
	Function::arg_iterator DestI = NewF->arg_begin();
	for (Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; ++I)
		if (VMap.count(I) == 0) {   // Is this argument preserved?
			DestI->setName(I->getName()); // Copy the name over...
			VMap[I] = DestI++;        // Add mapping to VMap
		}

	SmallVector<ReturnInst*, 8> Returns;  // Ignore returns cloned.
	CloneFunctionInto(NewF, F, VMap, ModuleLevelChanges, Returns, "", CodeInfo);
	return NewF;
}

/*
void RemapInstruction(Instruction *I, ValueToValueMapTy &VMap) 
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
*/
}

