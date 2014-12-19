#ifndef _H_SONGLH_SFREACHABILITY
#define _H_SONGLH_SFREACHABILITY


#include <vector>
#include <map>
#include <set>


#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"

using namespace llvm;
using namespace std;

namespace llvm_Commons
{

static uint64_t const UnknownSize = ~UINT64_C(0);

enum ExtensionKind {
	EK_NotExtended,
	EK_SignExt,
	EK_ZeroExt
};

struct VariableGEPIndex {
	const llvm::Value *V;
	ExtensionKind Extension;
	int64_t Scale;

	bool operator==(const VariableGEPIndex &Other) const {
		return V == Other.V && Extension == Other.Extension &&
		Scale == Other.Scale;
	}

	bool operator!=(const VariableGEPIndex &Other) const {
		return !operator==(Other);
	}
};

enum MemRelationKind
{
	MR_NO,
	MR_OVERLAP,
	MR_IDENTICAL,
	MR_COVER,
	MR_COVERED,
	MR_UNKNOWN
};

typedef struct stMemFootPrint
{
	Instruction * pI;
	Value * pBaseObject;
	Value * pPointer;
	Value * pLength;
	uint64_t uLength;
	Value * pOffset;
	uint64_t uOffset;
	uint64_t uMaxLength;
	SmallVector<VariableGEPIndex, 4> GEPVariableIndices;
	bool bInput;
	bool bLocal;
	set<Type *> setSubTypes;
	bool bReturn;

} MemFootPrint;




struct StructFieldReach : public ModulePass
{
	static char ID;
	StructFieldReach();
	virtual void getAnalysisUsage(AnalysisUsage &AU) const;
	virtual bool runOnModule(Module& M);
	virtual void print(raw_ostream &O, const Module *M) const;


private:
	//confirmed
	void BuildMemFootPrintMapping(Function * pFunction);
	void InitBeforeAfterSet(Function * pF);
	MemRelationKind CalIntraMemWriteRelation(MemFootPrint* pPrint1, MemFootPrint * pPrint2);
	MemRelationKind CalInterMemWriteRelation(MemFootPrint* pPrint1, MemFootPrint * pPrint2);
	void CalIntraAfterSet( set<MemFootPrint *> & beforeSet, set<MemFootPrint *> & afterSet, Instruction * pCurrent );
	void IntraFieldReachAnalysis(Function * pF);
	void CollectLiveInput(Function * pFunction, vector< pair<MemFootPrint *, int> > & vecLiveInput );
	void CalAfterExtendSet( set<MemFootPrint *> & beforeSet, set<MemFootPrint *> & afterSet, Instruction * pCurrent, Function * pFunction, vector<pair<MemFootPrint *, int> > & vecLiveInput );
	void InterFieldReachAnalysis(Function * pFunction, vector<pair<MemFootPrint *, int> > & vecLiveInput);
	void CalLoadDependentStore(Function * pFunction);
	void CalMemIntrinsicDependence(Function * pFunction);
	void RefineIntraMemFootPrintSet(set<MemFootPrint *> & setMemFootPrint, MemFootPrint * pFoot);
	void RefineInterMemFootPrintSet(set<MemFootPrint *> & setMemFootPrint, set<MemFootPrint *> & beforeSet, MemFootPrint * pFoot);

	//debug
	void DumpMemFootPrint();
	void AssignID();
	void DumpCachedRelation();
	void DumpCachedInterRelation();
	void DumpLoadDependingStore();
	void DumpMemInstDependingStore();

	void DebugResult(Function * pFunction);
	void TestDriver(Module & M);

public:
	void visit(Function * pFunction);



private:
	//before and after instruction
	map<Instruction*, vector< Instruction *> > InstPredInstVecMapping;
	map<Instruction*, vector< Instruction *> > InstSuccInstVecMapping;


	//before and after set for live analysis
	map<Instruction*, set< MemFootPrint *> > InstBeforeSetMapping;
	map<Instruction*, set< MemFootPrint *> > InstAfterSetMapping;

	map<Instruction *, set<MemFootPrint *> > InstBeforeExtendSetMapping;
	map<Instruction *, set<MemFootPrint *> > InstAfterExtendSetMapping;

	//Gen Set for store, Memintris and call
	map<Instruction*, MemFootPrint> InstMemFootPrintMapping;
	map<Instruction*, vector<MemFootPrint> > CallInstMemFootPrintMapping;
	map<MemTransferInst *, MemFootPrint > MemInstMemFootPrintMapping;

	//debug
	map<MemFootPrint *, int> MemFootPrintIDMapping;
	map<int, MemFootPrint *> IDMemFootPrintMapping;

	//cache
	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind> FootPrintPairRelationMapping;
	map<pair<MemFootPrint *, MemFootPrint *>, MemRelationKind> InterFootPrintPairRelationMapping;
	//map<Instruction *, vector<MemFootPrint> > CallInstMemFootPrintMapping;

	//map<LoadInst *, set<MemFootPrint *> > LoadFootPrintMapping;

public:
	map<LoadInst *, set<Instruction *> > LoadDependentInstMapping;
	map<MemTransferInst *, set<Instruction *> > MemInstDependentInstMapping;

private:
	AliasAnalysis * pAA;
	DataLayout * pDL;
	TargetLibraryInfo * pTLI;


};



}

#endif

