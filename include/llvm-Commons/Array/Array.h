#ifndef _H_SONGLH_ARRAY
#define _H_SONGLH_ARRAY


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"

#include <set>
#include <map>

using namespace llvm;
using namespace std;

namespace llvm_Commons
{
	/*
	bool getSignedValue(const SCEV * pSCEV, int64_t & res, DataLayout * DL);
	bool decodeSCEV(const SCEV * pSCEV, set<Value *> & setValue);

	bool hasConstantStride(PHINode * pPHI, ScalarEvolution * SE, DataLayout * DL);

	bool isArrayLoop(Loop * pLoop, map<Instruction *, set<Value *> > & ArrayAccessBoundayMapping, ScalarEvolution * SE);
	bool isArrayLoop(Loop * pLoop, set<Value *> &  setArrayBoundary, ScalarEvolution * SE, DataLayout * pDL);

	void collectIterativeVariable(Loop * pLoop, map<Instruction *, vector<Value * > > & mapBoundary, ScalarEvolution * SE, DataLayout * pDL);
	*/

	bool BeArrayAccess(Loop * pLoop, LoadInst * pLoad, ScalarEvolution * SE, DataLayout * DL);
	void AnalyzeArrayAccess(LoadInst * pLoad, Loop * pLoop, ScalarEvolution * SE, DataLayout * DL, vector<set<Value *> > & vecResult);
	//void CalCulateIndex(LoadInst * pLoad, Loop * pLoop, ScalarEvolution * SE, set<Value *> & setIndex, set<Value * > & setArrayBase);

}


#endif

