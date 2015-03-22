#ifndef _H_SONGLH_SEWRAPPER
#define _H_SONGLH_SEWRAPPER


#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"

#include <set>
#include <map>

using namespace llvm;
using namespace std;

namespace llvm_Commons
{
	const SCEV * CalculateLoopTripCounter(Loop * pLoop, ScalarEvolution * SE);

	void DecodeTripCounterSCEV(const SCEV * pSCEV, Loop * pLoop, set<Value *> & setTripCounter);
	const SCEV * DecondeTripCounterSCEV(const SCEV * pSCEV, Loop * pLoop, ScalarEvolution * SE);

	void SearchContainedValue(const SCEV * pSCEV, set<Value *> & setValue);


	void CalCulateLoopTripCounter(Loop * pLoop, ScalarEvolution * SE, set<Value *> & setTripCounter);
	bool IsIterativeVariable(PHINode * pPHI, Loop * pLoop,  ScalarEvolution * SE);
	bool IsIterativeVariable(const SCEV * pSCEV, Loop * pLoop, ScalarEvolution * SE);

	int64_t CalculateSignedValue(const SCEV * pSCEV, DataLayout * DL);
	int64_t CalculateStride(PHINode * pPHI, Loop * pLoop, ScalarEvolution * SE, DataLayout * DL);
	int64_t CalculateStride(Value * pValue, Loop * pLoop, ScalarEvolution * SE, DataLayout * DL);

	Value * CalculateLoopTripCounter(Loop * pLoop);

}


#endif

