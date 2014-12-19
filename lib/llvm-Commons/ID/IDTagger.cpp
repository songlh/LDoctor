

#include "llvm/IR/LLVMContext.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"

using namespace llvm;

#include "llvm-Commons/ID/IDTagger.h"

using namespace llvm_Commons;

static RegisterPass<IDTagger> X("tag-id",
                                "Assign each instruction a unique ID",
                                false,
                                false);

STATISTIC(NumInstructions, "Number of instructions");
STATISTIC(NumFunctions, "Number of functions");

char IDTagger::ID = 0;

IDTagger::IDTagger(): ModulePass(ID) {}

void IDTagger::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesCFG();
}

bool IDTagger::runOnModule(Module &M) 
{
	IntegerType *IntType = IntegerType::get(M.getContext(), 32);
	
	for (Module::iterator F = M.begin(); F != M.end(); ++F) 
	{
		if(F->begin() != F->end() && F->begin()->begin() != F->begin()->end())
		{
			Constant * FunID = ConstantInt::get(IntType, NumFunctions);
			F->begin()->begin()->setMetadata("func_id", MDNode::get(M.getContext(), FunID));
			++NumFunctions;
		}

		for (Function::iterator BB = F->begin(); BB != F->end(); ++BB) 
		{
			for (BasicBlock::iterator I = BB->begin(); I != BB->end(); ++I) 
			{
				Constant *InsID = ConstantInt::get(IntType, NumInstructions);
				I->setMetadata("ins_id", MDNode::get(M.getContext(), InsID));
				++NumInstructions;
			}
		}
	}
	return true;
}

