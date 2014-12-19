#ifndef _H_SONGLH_IDASSIGNER
#define _H_SONGLH_IDASSIGNER
//copy the following codes from https://github.com/wujingyue/rcs


#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;


namespace llvm_Commons {

struct IDAssigner: public ModulePass {
	static char ID;
	static const unsigned InvalidID = -1;

	IDAssigner();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;

	unsigned getInstructionID(const Instruction *I) const;
	unsigned getValueID(const Value *V) const;
	// Returns whether <V> is in this module.
	bool exists(const Value *V) const {
		return getValueID(V) != InvalidID;
	}
	unsigned getFunctionID(const Function *F) const;
	Instruction *getInstruction(unsigned ID) const;
	Value *getValue(unsigned ID) const;
	Function *getFunction(unsigned ID) const;
	/** Requires IDs to be consecutive. */
	unsigned getNumValues() const { return ValueIDMapping.size(); }
	void printValue(raw_ostream &O, const Value *V) const;

private:
	bool addValue(Value *V);
	bool addIns(Instruction *I);
	bool addFunction(Function *F);
	void extractValuesInUser(User *U);

	void printInstructions(raw_ostream &O, const Module *M) const;
	void printValues(raw_ostream &O, const Module *M) const;

	DenseMap<const Instruction *, unsigned> InsIDMapping;
	DenseMap<const Value *, unsigned> ValueIDMapping;
	DenseMap<unsigned, Instruction *> IDInsMapping;
	DenseMap<unsigned, Value *> IDValueMapping;
	DenseMap<const Function *, unsigned> FunctionIDMapping;
	DenseMap<unsigned, Function *> IDFunctionMapping;
};


}






#endif

