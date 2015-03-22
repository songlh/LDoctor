#ifndef _H_SONGLH_LS_WORKLESS
#define _H_SONGLH_LS_WORKLESS

#include "llvm/Pass.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;

struct WorklessLSInstrument : public ModulePass
{
	static char ID;
	WorklessLSInstrument();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;	


	void SetupTypes(Module * );
	void SetupConstants(Module * pModule);
	void SetupHooks(Module * );

	void ParseWorkingBlocks(set<string> & setWorkingBlocks);

	void InstrumentWorkless0Star1(Module * pModule, Loop * pLoop);
	void InstrumentWorkless0Or1Star(Module * pModule, Loop * pLoop, set<string> & setWorkingBlocks);

//type
	IntegerType *CharType ;
	IntegerType *BoolType ;
	IntegerType *LongType ;
	IntegerType *IntType  ;
	PointerType *CharStarType ;
	Type * VoidType ;
	Type * VoidPointerType;

//function
	Function * PrintLoopInfo;
	Function * PrintWorkingRatio ;

//globalvariable
	GlobalVariable * numIterations;
	GlobalVariable * numInstances ;
	GlobalVariable * numWorkingIterations ;
	GlobalVariable * bWorkingIteration ;

//constants
	ConstantInt * ConstantInt0;
	ConstantInt * ConstantInt1;
	ConstantInt * ConstantInt2;
	ConstantInt * ConstantInt3;
	ConstantInt * ConstantInt4;
	ConstantInt * ConstantInt10;
	ConstantInt * ConstantInt32;
	ConstantInt * ConstantInt_1;

	ConstantInt * ConstantLong_1;
	ConstantInt * ConstantLong0;
	ConstantInt * ConstantLong1;

	ConstantInt * ConstantCharFalse;
	ConstantInt * ConstantCharTrue;

	ConstantInt * ConstantBoolFalse;
	ConstantInt * ConstantBoolTrue;

	ConstantPointerNull * ConstantNULL;


};

#endif

