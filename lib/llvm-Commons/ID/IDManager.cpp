#include "llvm-Commons/ID/IDManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Constants.h"


using namespace llvm_Commons;

static RegisterPass<IDManager> X("manage-id",
                                 "Find the instruction with a particular ID; "
                                 "Lookup the ID of an instruction",
                                 false, true);

char IDManager::ID = 0;

void IDManager::getAnalysisUsage(AnalysisUsage &AU) const {
	AU.setPreservesAll();
}

IDManager::IDManager(): ModulePass(ID) {}

bool IDManager::runOnModule(Module &M) 
{
	InstIDMapping.clear();

	for (Module::iterator F = M.begin(); F != M.end(); ++F) 
	{
		unsigned FuncID = getFunctionID(F);
		if(FuncID != INVALID_ID)
		{
			FuncIDMapping[FuncID].push_back(F);
		}

		for (Function::iterator B = F->begin(); B != F->end(); ++B) 
		{
			for (BasicBlock::iterator I = B->begin(); I != B->end(); ++I) 
			{
				unsigned InsID = getInstructionID(I);

				if (InsID != INVALID_ID)
				{
					InstIDMapping[InsID].push_back(I);
				}
			}
		}
	}

	if (InstIDMapping_size() == 0)
		errs() << "[Warning] No ID information in this program.\n";

	return false;
}

unsigned IDManager::getInstructionID(Instruction *I) const 
{
	MDNode *Node = I->getMetadata("ins_id");
	if (!Node)
		return INVALID_ID;
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
	assert(CI);
	return CI->getZExtValue();
}

unsigned IDManager::getFunctionID(Function * F) const
{
	Function::iterator  BB = F->begin();
	if(BB == F->end() )
		return INVALID_ID;
	BasicBlock::iterator II = BB->begin();
	if(II == BB->end())
		return INVALID_ID;
	MDNode * Node = II->getMetadata("func_id");
	if(!Node)
		return INVALID_ID;
	assert(Node->getNumOperands() == 1);
	ConstantInt *CI = dyn_cast<ConstantInt>(Node->getOperand(0));
	assert(CI);
	return CI->getZExtValue();

}

Instruction *IDManager::getInstruction(unsigned InsID) const 
{
	InstList Insts = getInstructions(InsID);
	if (Insts.size() == 0 || Insts.size() > 1)
		return NULL;
	else
		return Insts[0];
}

InstList IDManager::getInstructions(unsigned InsID) const 
{
	return InstIDMapping.lookup(InsID);
}

Function * IDManager::getFunction(unsigned FuncID) const
{
	FuncList Funcs = getFunctions(FuncID);
	if(Funcs.size() == 0 || Funcs.size() > 1)
		return NULL;
	else
		return Funcs[0];
}

FuncList IDManager::getFunctions(unsigned FuncID) const
{
	return FuncIDMapping.lookup(FuncID);
}


void IDManager::print(raw_ostream &O, const Module *M) const {

}

