#ifndef _H_SONGLH_MEMFOOTPRINTUTILITY
#define _H_SONGLH_MEMFOOTPRINTUTILITY


#include "SFReach.h"
#include <vector>
#include <set>

using namespace std;
using namespace llvm;

namespace llvm_Commons
{

bool BeInputArgument(Value * V);
bool BeLocalObject(Value * V);
void CollectContainedType(set<Type *> & setContainedType, Type * pType);
bool BeValuePropagation(Instruction * I, Value * V);
bool BeSameBaseObject(MemFootPrint * pPrint1, MemFootPrint * pPrint2);
bool BeDifferentBaseObject(MemFootPrint * pPrint1, MemFootPrint * pPrint2, DataLayout * pDL);

void InitMemFootPrint(MemFootPrint * pFoot );
void CopyMemFootPrint(MemFootPrint * p1, MemFootPrint * p2);
void ChangeBaseObject(MemFootPrint * pFoot, Value * pV, DataLayout * pDL);
void PrintMemFootPrint(MemFootPrint * pFoot);
void CalMemFootPrint(Instruction *, MemFootPrint *, DataLayout * pDL );
void CalMemFootPrintForMemInstSrc(MemTransferInst * pMem, MemFootPrint * pFoot, DataLayout * pDL);



MemRelationKind CmpMemFootPrintOffset(MemFootPrint * pPrint1, MemFootPrint * pPrint2);
MemRelationKind CmpMemFootPrintForSameBase(MemFootPrint * pPrint1, MemFootPrint * pPrint2);
MemRelationKind CmpInterMemFootPrintForSameBase(MemFootPrint * pPrint1, MemFootPrint * pPrint2);


bool CmpMemFootPrintSet( set<MemFootPrint *> & SA, set<MemFootPrint *> & SB );




}



#endif

