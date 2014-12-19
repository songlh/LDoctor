#include "llvm-Commons/SFReach/MemFootPrintUtility.h"

#include "llvm/DebugInfo.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/InstructionSimplify.h"

namespace llvm_Commons
{


//using namespace llvm_Commons;

/// GetLinearExpression - Analyze the specified value as a linear expression:
/// "A*V + B", where A and B are constant integers.  Return the scale and offset
/// values as APInts and return V as a Value*, and return whether we looked
/// through any sign or zero extends.  The incoming Value is known to have
/// IntegerType and it may already be sign or zero extended.
///
/// Note that this looks through extends, so the high bits may not be
/// represented in the result.
static Value *GetLinearExpression(Value *V, APInt &Scale, APInt &Offset,
									ExtensionKind &Extension,
									const DataLayout &TD, unsigned Depth) 
{
	assert(V->getType()->isIntegerTy() && "Not an integer value");

	// Limit our recursion depth.
	if (Depth == 6) {
		Scale = 1;
		Offset = 0;
		return V;
	}

	if (BinaryOperator *BOp = dyn_cast<BinaryOperator>(V)) {
		if (ConstantInt *RHSC = dyn_cast<ConstantInt>(BOp->getOperand(1))) {
			switch (BOp->getOpcode()) {
			default: break;
			case Instruction::Or:
				// X|C == X+C if all the bits in C are unset in X.  Otherwise we can't
				// analyze it.
				if (!MaskedValueIsZero(BOp->getOperand(0), RHSC->getValue(), &TD))
				break;
				// FALL THROUGH.
			case Instruction::Add:
				V = GetLinearExpression(BOp->getOperand(0), Scale, Offset, Extension, TD, Depth+1);
				Offset += RHSC->getValue();
				return V;
			case Instruction::Mul:
				V = GetLinearExpression(BOp->getOperand(0), Scale, Offset, Extension, TD, Depth+1);
				Offset *= RHSC->getValue();
				Scale *= RHSC->getValue();
				return V;
			case Instruction::Shl:
				V = GetLinearExpression(BOp->getOperand(0), Scale, Offset, Extension, TD, Depth+1);
				Offset <<= RHSC->getValue().getLimitedValue();
				Scale <<= RHSC->getValue().getLimitedValue();
				return V;
			}
		}
	}

	// Since GEP indices are sign extended anyway, we don't care about the high
	// bits of a sign or zero extended value - just scales and offsets.  The
	// extensions have to be consistent though.
	if ((isa<SExtInst>(V) && Extension != EK_ZeroExt) ||
		(isa<ZExtInst>(V) && Extension != EK_SignExt)) 
	{
		Value *CastOp = cast<CastInst>(V)->getOperand(0);
		unsigned OldWidth = Scale.getBitWidth();
		unsigned SmallWidth = CastOp->getType()->getPrimitiveSizeInBits();
		Scale = Scale.trunc(SmallWidth);
		Offset = Offset.trunc(SmallWidth);
		Extension = isa<SExtInst>(V) ? EK_SignExt : EK_ZeroExt;

		Value *Result = GetLinearExpression(CastOp, Scale, Offset, Extension, TD, Depth+1);
		Scale = Scale.zext(OldWidth);
		Offset = Offset.zext(OldWidth);
		return Result;
	}

	Scale = 1;
	Offset = 0;
	return V;

}

/// DecomposeGEPExpression - If V is a symbolic pointer expression, decompose it
/// into a base pointer with a constant offset and a number of scaled symbolic
/// offsets.
///
/// The scaled symbolic offsets (represented by pairs of a Value* and a scale in
/// the VarIndices vector) are Value*'s that are known to be scaled by the
/// specified amount, but which may have other unrepresented high bits. As such,
/// the gep cannot necessarily be reconstructed from its decomposed form.
///
/// When DataLayout is around, this function is capable of analyzing everything
/// that GetUnderlyingObject can look through.  When not, it just looks
/// through pointer casts.
///

static const Value *
DecomposeGEPExpression(const Value *V, uint64_t &BaseOffs,
                       SmallVectorImpl<VariableGEPIndex> &VarIndices,
                       const DataLayout *TD) 
{
	// Limit recursion depth to limit compile time in crazy cases.
	unsigned MaxLookup = 6;

	BaseOffs = 0;
	do
	{
		// See if this is a bitcast or GEP.
		const Operator *Op = dyn_cast<Operator>(V);
		if (Op == 0) {
			// The only non-operator case we can handle are GlobalAliases.
			if (const GlobalAlias *GA = dyn_cast<GlobalAlias>(V)) {
				if (!GA->mayBeOverridden()) {
					V = GA->getAliasee();
					continue;
				}
			}
			return V;
    	}

		if (Op->getOpcode() == Instruction::BitCast) {
			V = Op->getOperand(0);
			continue;
		}

		const GEPOperator *GEPOp = dyn_cast<GEPOperator>(Op);
		if (GEPOp == 0) {
			// If it's not a GEP, hand it off to SimplifyInstruction to see if it
			// can come up with something. This matches what GetUnderlyingObject does.
			if (const Instruction *I = dyn_cast<Instruction>(V))
				// TODO: Get a DominatorTree and use it here.
				if (const Value *Simplified = SimplifyInstruction(const_cast<Instruction *>(I), TD)) {
					V = Simplified;
					continue;
				}
			return V;
		}

		// Don't attempt to analyze GEPs over unsized objects.
		if (!GEPOp->getOperand(0)->getType()->getPointerElementType()->isSized())
			return V;

		// If we are lacking DataLayout information, we can't compute the offets of
		// elements computed by GEPs.  However, we can handle bitcast equivalent
		// GEPs.
		if (TD == 0) {
			if (!GEPOp->hasAllZeroIndices())
				return V;
			V = GEPOp->getOperand(0);
			continue;
		}

		unsigned AS = GEPOp->getPointerAddressSpace();
		// Walk the indices of the GEP, accumulating them into BaseOff/VarIndices.
		gep_type_iterator GTI = gep_type_begin(GEPOp);


		for (User::const_op_iterator I = GEPOp->op_begin()+1, E = GEPOp->op_end(); I != E; ++I) 
		{
			Value *Index = *I;
			
			// Compute the (potentially symbolic) offset in bytes for this index.
			if (StructType *STy = dyn_cast<StructType>(*GTI++)) {
				unsigned FieldNo = cast<ConstantInt>(Index)->getZExtValue();
        		if (FieldNo == 0) continue;

        		BaseOffs += TD->getStructLayout(STy)->getElementOffset(FieldNo);
        		continue;
			}

			// For an array/pointer, add the element offset, explicitly scaled.
			if (ConstantInt *CIdx = dyn_cast<ConstantInt>(Index)) {
				if (CIdx->isZero()) continue;
				BaseOffs += TD->getTypeAllocSize(*GTI)*CIdx->getSExtValue();
				continue;
			}

			uint64_t Scale = TD->getTypeAllocSize(*GTI);
			ExtensionKind Extension = EK_NotExtended;

			// If the integer type is smaller than the pointer size, it is implicitly
			// sign extended to pointer size.
			unsigned Width = Index->getType()->getIntegerBitWidth();
			if (TD->getPointerSizeInBits(AS) > Width)
				Extension = EK_SignExt;

			// Use GetLinearExpression to decompose the index into a C1*V+C2 form.
			APInt IndexScale(Width, 0), IndexOffset(Width, 0);
			Index = GetLinearExpression(Index, IndexScale, IndexOffset, Extension, *TD, 0);

			// The GEP index scale ("Scale") scales C1*V+C2, yielding (C1*V+C2)*Scale.
			// This gives us an aggregate computation of (C1*Scale)*V + C2*Scale.
			BaseOffs += IndexOffset.getSExtValue()*Scale;
			Scale *= IndexScale.getSExtValue();

			// If we already had an occurrence of this index variable, merge this
			// scale into it.  For example, we want to handle:
			//   A[x][x] -> x*16 + x*4 -> x*20
			// This also ensures that 'x' only appears in the index list once.
			for (unsigned i = 0, e = VarIndices.size(); i != e; ++i) {
				if (VarIndices[i].V == Index && VarIndices[i].Extension == Extension) {
					Scale += VarIndices[i].Scale;
					VarIndices.erase(VarIndices.begin()+i);
					break;
				}
			}

			// Make sure that we have a scale that makes sense for this target's
			// pointer size.
			if (unsigned ShiftBits = 64 - TD->getPointerSizeInBits(AS)) {
				Scale <<= ShiftBits;
				Scale = (int64_t)Scale >> ShiftBits;
			}

			if (Scale) {
				VariableGEPIndex Entry = {Index, Extension, static_cast<int64_t>(Scale)}; 
				VarIndices.push_back(Entry);
			}

		}
		// Analyze the base pointer next.
		V = GEPOp->getOperand(0);
	} while (--MaxLookup);

	return V;

}


/// GetIndexDifference - Dest and Src are the variable indices from two
/// decomposed GetElementPtr instructions GEP1 and GEP2 which have common base
/// pointers.  Subtract the GEP2 indices from GEP1 to find the symbolic
/// difference between the two pointers.
static void GetIndexDifference( SmallVectorImpl<VariableGEPIndex> &Dest,
								const SmallVectorImpl<VariableGEPIndex> &Src) 
{
	if (Src.empty())
		return;


	for (unsigned i = 0, e = Src.size(); i != e; ++i) {
		const Value *V = Src[i].V;
		ExtensionKind Extension = Src[i].Extension;
		int64_t Scale = Src[i].Scale;

		// Find V in Dest.  This is N^2, but pointer indices almost never have more
		// than a few variable indexes.
		for (unsigned j = 0, e = Dest.size(); j != e; ++j) {
			if (Dest[j].V != V ||
				Dest[j].Extension != Extension)
				continue;

			// If we found it, subtract off Scale V's from the entry in Dest.  If it
			// goes to zero, remove the entry.
			if (Dest[j].Scale != Scale)
				Dest[j].Scale -= Scale;
			else
				Dest.erase(Dest.begin() + j);
			Scale = 0;
			break;
		}
		// If we didn't consume this entry, add it to the end of the Dest list.
		if (Scale) {
			VariableGEPIndex Entry = { V, Extension, -Scale };
			Dest.push_back(Entry);
		}
	}
}


void InitMemFootPrint(MemFootPrint * pFoot )
{
	pFoot->pI = NULL;
	pFoot->pBaseObject = NULL;
	pFoot->pPointer = NULL;
	pFoot->pLength = NULL;
	pFoot->uLength = UnknownSize;
	pFoot->pOffset = NULL;
	pFoot->uOffset = UnknownSize;
	pFoot->uMaxLength = UnknownSize;
	pFoot->bInput = false;
	pFoot->bLocal = false;
	pFoot->bReturn = false;
}

void CopyMemFootPrint(MemFootPrint * p1, MemFootPrint * p2)
{
	p2->pI = p1->pI;
	p2->pBaseObject = p1->pBaseObject;
	p2->pPointer = p1->pPointer;
	p2->pLength = p1->pLength;
	p2->uLength = p1->uLength;
	p2->pOffset = p1->pOffset;
	p2->uOffset = p1->uOffset;
	p2->uMaxLength = p1->uMaxLength;
	p2->bInput = p1->bInput;
	p2->bLocal = p1->bLocal;
	p2->bReturn = p1->bReturn;

	p2->GEPVariableIndices.clear();
	SmallVector<VariableGEPIndex, 4>::iterator itVecBegin = p1->GEPVariableIndices.begin();
	SmallVector<VariableGEPIndex, 4>::iterator itVecEnd = p1->GEPVariableIndices.end();

	for(; itVecBegin != itVecEnd; itVecBegin++)
	{
		p2->GEPVariableIndices.push_back(*itVecBegin);
	}

	set<Type *>::iterator itSetBegin = p1->setSubTypes.begin();
	set<Type *>::iterator itSetEnd = p1->setSubTypes.end();

	p2->setSubTypes.clear();
	for(; itSetBegin != itSetEnd; itSetBegin ++)
	{
		p2->setSubTypes.insert(*itSetBegin);
	}

}





bool BeInputArgument(Value * V)
{
	if(isa<Argument>(V))
	{
		return true;
	}

	if(!isa<Instruction>(V))
	{
		return false;
	}

	vector<Instruction *> vecWorkList;
	set<Instruction *> setProcessedInst;

	vecWorkList.push_back(cast<Instruction>(V));
	setProcessedInst.insert(cast<Instruction>(V));

	while(vecWorkList.size()>0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		if(PHINode * pPHINode = dyn_cast<PHINode>(pCurrent))
		{
			for(unsigned i = 0 ; i < pPHINode->getNumIncomingValues() ; i ++ )
			{
				if(Instruction * pI = dyn_cast<Instruction>(pPHINode->getIncomingValue(i)))
				{
					if(setProcessedInst.find(pI) == setProcessedInst.end() )
					{
						setProcessedInst.insert(pI);
						vecWorkList.push_back(pI);
					}
				}
				else if(!isa<Argument>(pPHINode->getIncomingValue(i)))
				{
					return false;
				}
			}
		}
		else if(CastInst * pCast = dyn_cast<CastInst>(pCurrent))
		{
			if(Instruction * pI = dyn_cast<Instruction>(pCast->getOperand(0)))
			{
				if(setProcessedInst.find(pI) == setProcessedInst.end() )
				{
					setProcessedInst.insert(pI);
					vecWorkList.push_back(pI);
				}
			}
			else if(!isa<Argument>(pCast->getOperand(0)))
			{
				return false;
			}
		}
		else if(GetElementPtrInst * pGet = dyn_cast<GetElementPtrInst>(pCurrent))
		{
			if(Instruction * pI = dyn_cast<Instruction>(pGet->getPointerOperand() ) )
			{
				if(setProcessedInst.find(pI) == setProcessedInst.end() )
				{
					setProcessedInst.insert(pI);
					vecWorkList.push_back(pI);
				}

			}
			else if(!isa<Argument>(pGet->getPointerOperand()))
			{
				return false;
			}
		}
		else
		{
			return false;
		}
	}

	return true;

}

bool BeLocalObject(Value * V)
{
	if(isa<AllocaInst>(V))
	{
		return true;
	}

	if(!isa<Instruction>(V))
	{
		return false;
	}

	vector<Instruction *> vecWorkList;
	set<Instruction *> setProcessedInst;

	vecWorkList.push_back(cast<Instruction>(V));
	setProcessedInst.insert(cast<Instruction>(V));

	while(vecWorkList.size()>0)
	{
		Instruction * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		if(isa<AllocaInst>(pCurrent))
		{

		}
		else if(PHINode * pPHINode = dyn_cast<PHINode>(pCurrent))
		{
			for(unsigned i = 0 ; i < pPHINode->getNumIncomingValues() ; i ++ )
			{
				if(Instruction * pI = dyn_cast<Instruction>(pPHINode->getIncomingValue(i)))
				{
					if(setProcessedInst.find(pI) == setProcessedInst.end() )
					{
						setProcessedInst.insert(pI);
						vecWorkList.push_back(pI);
					}
				}
				else
				{
					return false;
				}

			}
		}
		else if(CastInst * pCast = dyn_cast<CastInst>(pCurrent))
		{
			if(Instruction * pI = dyn_cast<Instruction>(pCast->getOperand(0)))
			{
				if(setProcessedInst.find(pI) == setProcessedInst.end() )
				{
					setProcessedInst.insert(pI);
					vecWorkList.push_back(pI);
				}
			}
			else
			{
				return false;
			}
		}
		else if(GetElementPtrInst * pGet = dyn_cast<GetElementPtrInst>(pCurrent))
		{
			if(Instruction * pI = dyn_cast<Instruction>(pGet->getPointerOperand() ) )
			{
				if(setProcessedInst.find(pI) == setProcessedInst.end() )
				{
					setProcessedInst.insert(pI);
					vecWorkList.push_back(pI);
				}

			}
			else
			{
				return false;
			}
		}
		else
		{
			return false;
		}
	}

	return true;
}

void CollectContainedType(set<Type *> & setContainedType, Type * pType)
{
	assert(isa<PointerType>(pType));
	setContainedType.clear();
	Type * pPointerType = cast<PointerType>(pType)->getElementType();

	vector<Type *> vecWorkList;

	setContainedType.insert(pPointerType);
	vecWorkList.push_back(pPointerType);

	while(vecWorkList.size()>0)
	{
		Type * pCurrent = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		if(CompositeType * pCType = dyn_cast<CompositeType>(pCurrent))
		{
			for(unsigned i = 0 ; i < pCType->getNumContainedTypes(); i++)
			{
				if(setContainedType.find(pCType->getContainedType(i)) == setContainedType.end() )
				{
					setContainedType.insert(pCType->getContainedType(i));
					vecWorkList.push_back(pCType->getContainedType(i));
				}
			}
		}
	}
}



void CalMemFootPrint(Instruction * pInstruction, MemFootPrint * pFoot, DataLayout * pDL )
{
	InitMemFootPrint(pFoot);

	pFoot->pI = pInstruction;

	if(LoadInst * pLoad = dyn_cast<LoadInst>(pInstruction))
	{
		pFoot->pPointer = pLoad->getPointerOperand();

		if(IntegerType * pType = dyn_cast<IntegerType>(pLoad->getType()) )
		{
			pFoot->uLength = pType->getBitWidth()/8;
		}
		else
		{
			assert(0);
		}

	}
	else if(StoreInst * pStore = dyn_cast<StoreInst>(pInstruction))
	{
		pFoot->pPointer = pStore->getPointerOperand();
		Value * pV = pStore->getValueOperand();

		if(IntegerType * pType = dyn_cast<IntegerType>(pV->getType()) )
		{
			pFoot->uLength = pType->getBitWidth()/8;
		}
		else
		{
			assert(0);
		}
	}
	else if(MemIntrinsic * pMemIntrin = dyn_cast<MemIntrinsic>(pInstruction))
	{
		pFoot->pPointer = pMemIntrin->getRawDest();
		pFoot->pLength = pMemIntrin->getLength();

		if(ConstantInt * pConstant = dyn_cast<ConstantInt>(pFoot->pLength))
		{
			pFoot->uLength = pConstant->getLimitedValue();
		}
		
	}
	else
	{
		pInstruction->dump();
		errs() << "Unhandled Memory Instruction\n";
	}

	pFoot->pBaseObject = GetUnderlyingObject(pFoot->pPointer, pDL);

	if(CastInst * pCast = dyn_cast<CastInst>(pFoot->pPointer))
	{
		Type * pSrcType = pCast->getOperand(0)->getType();
		Type * pDestType = pCast->getType();

		if(isa<PointerType>(pSrcType) && isa<PointerType>(pDestType))
		{
			PointerType * pSrcPointerType = cast<PointerType>(pSrcType);
			PointerType * pDestPointerType = cast<PointerType>(pDestType);
			if(isa<IntegerType>(pDestPointerType->getElementType()) && isa<CompositeType>(pSrcPointerType->getElementType()))
			{
				pFoot->pPointer = pCast->getOperand(0);
			}
		}

	}

	if(GetElementPtrInst * pGet = dyn_cast<GetElementPtrInst>(pFoot->pPointer))
	{
		if(pGet->getNumOperands() > 2)
		{
			if(ConstantInt * pInt = dyn_cast<ConstantInt>(pGet->getOperand(1)))
			{
				if(pInt->getLimitedValue() == 0)
				{
					PointerType * pPointerType = cast<PointerType>(pGet->getPointerOperand()->getType());

					if( ArrayType * pArrayType = dyn_cast<ArrayType>(pPointerType->getElementType()))
					{
						pFoot->uMaxLength = pDL->getTypeStoreSize(pArrayType) ;
					}
					else if(StructType * pStructType = dyn_cast<StructType>(pPointerType->getElementType()))
					{
						if(ConstantInt * pInt2 = dyn_cast<ConstantInt>(pGet->getOperand(2)))
						{
							const StructLayout * pStructLayout = pDL->getStructLayout(pStructType);
							
							uint64_t uStructSize = pStructLayout->getSizeInBytes();
							unsigned uMaxFieldNo = pStructLayout->getElementContainingOffset(uStructSize-1);
							uint64_t uCurrentIndex = pInt2->getLimitedValue();

							if(uCurrentIndex == uMaxFieldNo)
							{
								pFoot->uMaxLength = pStructLayout->getSizeInBytes() - pStructLayout->getElementOffset(uCurrentIndex);
							} 
							else
							{
								pFoot->uMaxLength = pStructLayout->getElementOffset(uCurrentIndex+1) - pStructLayout->getElementOffset(uCurrentIndex);
							}
							
						}
					}
									
				}
			}
		}
	}
	else if(GlobalVariable * pGV = dyn_cast<GlobalVariable>(pFoot->pPointer))
	{
		PointerType * pPointerType = cast<PointerType>(pGV->getType());
		if(IntegerType * pIType = dyn_cast<IntegerType>(pPointerType->getElementType()))
		{
			pFoot->uMaxLength = pDL->getTypeStoreSize(pIType);
		}
		
	}
	else if(AllocaInst * pAlloc = dyn_cast<AllocaInst>(pFoot->pPointer))
	{
		pFoot->uMaxLength = pDL->getTypeStoreSize(pAlloc->getAllocatedType());
	}


	if(AllocaInst * pAlloc = dyn_cast<AllocaInst>(pFoot->pBaseObject))
	{
		if(pAlloc->hasOneUse())
		{
			if(CastInst * pCast = dyn_cast<CastInst>(*(pAlloc->use_begin())))
			{
				Type * pSrcType = pCast->getOperand(0)->getType();
				Type * pDestType = pCast->getType();

				if(isa<PointerType>(pSrcType) && isa<PointerType>(pDestType))
				{
					PointerType * pSrcPointerType = cast<PointerType>(pSrcType);
					PointerType * pDestPointerType = cast<PointerType>(pDestType);
					if(isa<IntegerType>(pSrcPointerType->getElementType()) && isa<CompositeType>(pDestPointerType->getElementType()))
					{
						pFoot->pBaseObject = pCast;
					}
				}
			}
		}
	}

	DecomposeGEPExpression(pFoot->pPointer, pFoot->uOffset, pFoot->GEPVariableIndices, pDL);
	pFoot->bLocal = BeLocalObject(pFoot->pBaseObject);
	pFoot->bInput = BeInputArgument(pFoot->pBaseObject);
	CollectContainedType( pFoot->setSubTypes, pFoot->pBaseObject->getType());
}


void CalMemFootPrintForMemInstSrc(MemTransferInst * pMem, MemFootPrint * pFoot, DataLayout * pDL)
{
	InitMemFootPrint(pFoot);
	pFoot->pI = pMem;

	pFoot->pPointer = pMem->getRawSource();
	pFoot->pLength = pMem->getLength();

	if(ConstantInt * pConstant = dyn_cast<ConstantInt>(pFoot->pLength))
	{
		pFoot->uLength = pConstant->getLimitedValue();
	}

	pFoot->pBaseObject = GetUnderlyingObject(pFoot->pPointer, pDL);

	if(CastInst * pCast = dyn_cast<CastInst>(pFoot->pPointer))
	{
		Type * pSrcType = pCast->getOperand(0)->getType();
		Type * pDestType = pCast->getType();

		if(isa<PointerType>(pSrcType) && isa<PointerType>(pDestType))
		{
			PointerType * pSrcPointerType = cast<PointerType>(pSrcType);
			PointerType * pDestPointerType = cast<PointerType>(pDestType);
			if(isa<IntegerType>(pDestPointerType->getElementType()) && isa<CompositeType>(pSrcPointerType->getElementType()))
			{
				pFoot->pPointer = pCast->getOperand(0);
			}
		}

	}

	if(GetElementPtrInst * pGet = dyn_cast<GetElementPtrInst>(pFoot->pPointer))
	{
		if(pGet->getNumOperands() > 2)
		{
			if(ConstantInt * pInt = dyn_cast<ConstantInt>(pGet->getOperand(1)))
			{
				if(pInt->getLimitedValue() == 0)
				{
					PointerType * pPointerType = cast<PointerType>(pGet->getPointerOperand()->getType());

					if( ArrayType * pArrayType = dyn_cast<ArrayType>(pPointerType->getElementType()))
					{
						pFoot->uMaxLength = pDL->getTypeStoreSize(pArrayType) ;
					}
					else if(StructType * pStructType = dyn_cast<StructType>(pPointerType->getElementType()))
					{
						if(ConstantInt * pInt2 = dyn_cast<ConstantInt>(pGet->getOperand(2)))
						{
							const StructLayout * pStructLayout = pDL->getStructLayout(pStructType);
							
							uint64_t uStructSize = pStructLayout->getSizeInBytes();
							unsigned uMaxFieldNo = pStructLayout->getElementContainingOffset(uStructSize-1);
							uint64_t uCurrentIndex = pInt2->getLimitedValue();

							if(uCurrentIndex == uMaxFieldNo)
							{
								pFoot->uMaxLength = pStructLayout->getSizeInBytes() - pStructLayout->getElementOffset(uCurrentIndex);
							} 
							else
							{
								pFoot->uMaxLength = pStructLayout->getElementOffset(uCurrentIndex+1) - pStructLayout->getElementOffset(uCurrentIndex);
							}
							
						}
					}
									
				}
			}
		}
	}
	else if(GlobalVariable * pGV = dyn_cast<GlobalVariable>(pFoot->pPointer))
	{
		PointerType * pPointerType = cast<PointerType>(pGV->getType());
		if(IntegerType * pIType = dyn_cast<IntegerType>(pPointerType->getElementType()))
		{
			pFoot->uMaxLength = pDL->getTypeStoreSize(pIType);
		}
		
	}
	else if(AllocaInst * pAlloc = dyn_cast<AllocaInst>(pFoot->pPointer))
	{
		pFoot->uMaxLength = pDL->getTypeStoreSize(pAlloc->getAllocatedType());
	}


	if(AllocaInst * pAlloc = dyn_cast<AllocaInst>(pFoot->pBaseObject))
	{
		if(pAlloc->hasOneUse())
		{
			if(CastInst * pCast = dyn_cast<CastInst>(*(pAlloc->use_begin())))
			{
				Type * pSrcType = pCast->getOperand(0)->getType();
				Type * pDestType = pCast->getType();

				if(isa<PointerType>(pSrcType) && isa<PointerType>(pDestType))
				{
					PointerType * pSrcPointerType = cast<PointerType>(pSrcType);
					PointerType * pDestPointerType = cast<PointerType>(pDestType);
					if(isa<IntegerType>(pSrcPointerType->getElementType()) && isa<CompositeType>(pDestPointerType->getElementType()))
					{
						pFoot->pBaseObject = pCast;
					}
				}
			}
		}
	}

	DecomposeGEPExpression(pFoot->pPointer, pFoot->uOffset, pFoot->GEPVariableIndices, pDL);
	pFoot->bLocal = BeLocalObject(pFoot->pBaseObject);
	pFoot->bInput = BeInputArgument(pFoot->pBaseObject);
	CollectContainedType( pFoot->setSubTypes, pFoot->pBaseObject->getType());



}




void ChangeBaseObject(MemFootPrint * pFoot, Value * pV, DataLayout * pDL)
{
	Value * pBaseObject = GetUnderlyingObject(pV, pDL);
	if(AllocaInst * pAlloc = dyn_cast<AllocaInst>(pBaseObject))
	{
		if(pAlloc->hasOneUse())
		{
			if(CastInst * pCast = dyn_cast<CastInst>(*(pAlloc->use_begin())))
			{
				Type * pSrcType = pCast->getOperand(0)->getType();
				Type * pDestType = pCast->getType();

				if(isa<PointerType>(pSrcType) && isa<PointerType>(pDestType))
				{
					PointerType * pSrcPointerType = cast<PointerType>(pSrcType);
					PointerType * pDestPointerType = cast<PointerType>(pDestType);
					if(isa<IntegerType>(pSrcPointerType->getElementType()) && isa<CompositeType>(pDestPointerType->getElementType()))
					{
						pBaseObject = pCast;
					}
				}
			}
		}
	}

	//assert(pBaseObject == pV);
	if(pBaseObject != pV)
	{
		pBaseObject->dump();
		pV->dump();
		exit(0);
	}


	pFoot->pBaseObject = pBaseObject;

	if(AllocaInst * pAlloc = dyn_cast<AllocaInst>(pFoot->pBaseObject))
	{
		if(pAlloc->hasOneUse())
		{
			if(CastInst * pCast = dyn_cast<CastInst>(*(pAlloc->use_begin())))
			{
				Type * pSrcType = pCast->getOperand(0)->getType();
				Type * pDestType = pCast->getType();

				if(isa<PointerType>(pSrcType) && isa<PointerType>(pDestType))
				{
					PointerType * pSrcPointerType = cast<PointerType>(pSrcType);
					PointerType * pDestPointerType = cast<PointerType>(pDestType);
					if(isa<IntegerType>(pSrcPointerType->getElementType()) && isa<CompositeType>(pDestPointerType->getElementType()))
					{
						pFoot->pBaseObject = pCast;
					}
				}
			}
		}
	}

	pFoot->bLocal = BeLocalObject(pFoot->pBaseObject);
	pFoot->bInput = BeInputArgument(pFoot->pBaseObject);
	CollectContainedType( pFoot->setSubTypes, pFoot->pBaseObject->getType());

} 


void PrintMemFootPrint(MemFootPrint * pFoot)
{
	char pPath[1000];

	if( MDNode *N = pFoot->pI->getMetadata("dbg") )
	{
		DILocation Loc(N);
		string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
		realpath( sFileNameForInstruction.c_str() , pPath);
		sFileNameForInstruction = string(pPath);                        
		unsigned int uLineNoForInstruction = Loc.getLineNumber();
		errs() << sFileNameForInstruction << ": " << uLineNoForInstruction << "\n";
	}
	pFoot->pI->dump();
	pFoot->pPointer->dump();    
	pFoot->pBaseObject->dump();
	pFoot->pLength->dump();
	errs() << "uLength: " << pFoot->uLength << "\n";
	errs() << "uOffset: " << pFoot->uOffset << "\n";
	errs() << "uMaxLength: " << pFoot->uMaxLength << "\n";
	errs() << "IndexSize: " << pFoot->GEPVariableIndices.size() << "\n";

	SmallVector<VariableGEPIndex, 4>::iterator itVecBegin = pFoot->GEPVariableIndices.begin();
	SmallVector<VariableGEPIndex, 4>::iterator itVecEnd = pFoot->GEPVariableIndices.end();

	for(; itVecBegin != itVecEnd; itVecBegin++)
	{
		itVecBegin->V->dump();
		errs() << itVecBegin->Scale << "\n";

		switch(itVecBegin->Extension)
		{
			case EK_NotExtended:
				errs() << "EK_NotExtended\n";
				break;
			case EK_SignExt:
				errs() << "EK_SignExt\n";
				break;
			case EK_ZeroExt:
				errs() << "EK_ZeroExt\n";
				break;
		}
	}

	set<Type *>::iterator itSetBegin = pFoot->setSubTypes.begin();
	set<Type *>::iterator itSetEnd = pFoot->setSubTypes.end();

	for(; itSetBegin != itSetEnd; itSetBegin++)
	{
		(*itSetBegin)->dump();
		errs() << " ";
	}

	errs() << "\n";

	if(pFoot->bLocal)
	{
		errs() << "Local\n";
	}

	if(pFoot->bInput)
	{
		errs() << "Input\n";
	}

	if(pFoot->bReturn)
	{
		errs() << "Return\n";
	}

	errs() << "*********************************************\n";
}


bool CmpMemFootPrintSet( set<MemFootPrint *> & SA, set<MemFootPrint *> & SB )
{
	if(SA.size() != SB.size())
	{
		return false;
	}

	set<MemFootPrint *>::iterator itSetBegin = SA.begin();
	set<MemFootPrint *>::iterator itSetEnd = SA.end();

	for(; itSetBegin != itSetEnd; itSetBegin++ )
	{
		if(SB.find(*itSetBegin) == SB.end() )
		{
			return false;
		}
	}

	return true;

}


bool BeValuePropagation(Instruction * I, Value * V)
{
	if(isa<Instruction>(V))
	{
		if(I == cast<Instruction>(V))
		{
			return true;
		}
	}

	set<Value *> setDependentValue;
	vector<Instruction *> vecWorkList;

	setDependentValue.insert(I);
	vecWorkList.push_back(I);

	while(vecWorkList.size() >0)
	{
		Instruction * pInstruction = vecWorkList[vecWorkList.size()-1];
		vecWorkList.pop_back();

		if(PHINode * pPHI = dyn_cast<PHINode>(pInstruction))
		{
			for (unsigned i = 0, e = pPHI->getNumIncomingValues(); i != e; ++i) 
			{
				if(Instruction * pI = dyn_cast<Instruction>(pPHI->getIncomingValue(i)) )
				{
					if(setDependentValue.find(pI) == setDependentValue.end())
					{
						setDependentValue.insert(pI);
						vecWorkList.push_back(pI);
					}
				}
				else
				{
					setDependentValue.insert(pPHI->getIncomingValue(i));
				}
			}
		}
		else if(CastInst * pCast = dyn_cast<CastInst>(pInstruction))
		{
			if(Instruction * pI = dyn_cast<Instruction>(pCast->getOperand(0)) )
			{
				if(setDependentValue.find(pI) == setDependentValue.end())
				{
					setDependentValue.insert(pI);
					vecWorkList.push_back(pI);
				}
			}
			else
			{
				setDependentValue.insert(pCast->getOperand(0));
			}

		}
		else if(GetElementPtrInst * pGet = dyn_cast<GetElementPtrInst>(pInstruction))
		{
			if(pGet->hasAllZeroIndices())
			{
				if(Instruction * pI = dyn_cast<Instruction>(pGet->getPointerOperand() ) )
				{
					if(setDependentValue.find(pI) == setDependentValue.end())
					{
						setDependentValue.insert(pI);
						vecWorkList.push_back(pI);
					}
				}
				else
				{
					setDependentValue.insert(pGet->getPointerOperand());
				}
			}
		}
	}

	if(setDependentValue.find(V) != setDependentValue.end())
	{
		return true;
	}

	return false;
}


bool BeSameBaseObject(MemFootPrint * pPrint1, MemFootPrint * pPrint2)
{
	if(pPrint1->pBaseObject == pPrint2->pBaseObject)
	{
		return true;
	}

	if(!isa<Instruction>(pPrint1->pBaseObject) && !isa<Instruction>(pPrint2->pBaseObject))
	{
		return false;
	}

	if(isa<Instruction>(pPrint1->pBaseObject))
	{
		if(BeValuePropagation(cast<Instruction>(pPrint1->pBaseObject), pPrint2->pBaseObject))
		{
			return true;
		}
	}
	
	if(isa<Instruction>(pPrint2->pBaseObject))
	{
		if(BeValuePropagation(cast<Instruction>(pPrint2->pBaseObject), pPrint1->pBaseObject))
		{
			return true;
		}
	}

	return false;
}

bool BeDifferentBaseObject(MemFootPrint * pPrint1, MemFootPrint * pPrint2, DataLayout * pDL)
{
	if(pPrint1->bLocal && pPrint2->bInput )
	{
		return true;
	}

	if(pPrint1->bInput && pPrint2->bLocal )
	{
		return true;
	}

	Type * pPointerType1 = cast<PointerType>(pPrint1->pBaseObject->getType())->getElementType();
	Type * pPointerType2 = cast<PointerType>(pPrint2->pBaseObject->getType())->getElementType();

	if(pPrint1->setSubTypes.find(pPointerType2) == pPrint1->setSubTypes.end() && pPrint2->setSubTypes.find(pPointerType1) == pPrint2->setSubTypes.end())
	{
		return true;
	}

	if(pPrint1->bLocal && pPrint2->bLocal)
	{
		if(pDL->getTypeStoreSize(pPointerType1) < pDL->getTypeStoreSize(pPointerType2))
		{
			if(isa<AllocaInst>(pPrint1->pBaseObject))
			{
				return true;
			}
			else if(CastInst * pCast = dyn_cast<CastInst>(pPrint1->pBaseObject))
			{
				if(isa<AllocaInst>(pCast->getOperand(0)))
				{
					return true;
				}
			}
		}
		else if(pDL->getTypeStoreSize(pPointerType1) > pDL->getTypeStoreSize(pPointerType2))
		{
			if(isa<AllocaInst>(pPrint2->pBaseObject))
			{
				return true;
			}
			else if(CastInst * pCast = dyn_cast<CastInst>(pPrint2->pBaseObject))
			{
				if(isa<AllocaInst>(pCast->getOperand(0)))
				{
					return true;
				}
			}
		}
	}

	return false;
}

MemRelationKind CmpMemFootPrintOffset(MemFootPrint * pPrint1, MemFootPrint * pPrint2)
{
	if(pPrint1->uOffset == pPrint2->uOffset)
	{
		if(pPrint1->uLength != UnknownSize && pPrint2->uLength != UnknownSize )
		{
			if(pPrint1->uLength < pPrint2->uLength)
			{
				return MR_COVERED;
			}
			else if(pPrint1->uLength == pPrint2->uLength)
			{
				return MR_IDENTICAL;
			}
			else
			{
				return MR_COVER;
			}
		}
		else
		{
			return MR_OVERLAP;
		}

	}
	else if(pPrint1->uOffset < pPrint2->uOffset)
	{
		if(pPrint1->uLength != UnknownSize)
		{
			if(pPrint1->uOffset + pPrint1->uLength <= pPrint2->uOffset)
			{
				return MR_NO;
			}
			else
			{
				if(pPrint2->uLength != UnknownSize )
				{
					if(pPrint1->uOffset + pPrint1->uLength < pPrint2->uOffset + pPrint2->uLength)
					{
						return MR_OVERLAP;
					}
					else //if(pPrint1->uOffset + pPrint1->uLength >= pPrint2->uOffset + pPrint2->uLength)
					{
						return MR_COVER;
					}
				}
				else if(pPrint2->uMaxLength != UnknownSize)
				{
					if(pPrint1->uOffset + pPrint1->uLength >= pPrint2->uOffset + pPrint2->uMaxLength)
					{
						return MR_COVER;
					}
					else
					{
						return MR_OVERLAP;
					}
				}
				else
				{
					return MR_OVERLAP;
				}
			}
		}
		else if(pPrint1->uMaxLength != UnknownSize)
		{
			if(pPrint1->uOffset + pPrint1->uMaxLength <= pPrint2->uOffset)
			{
				return MR_NO;
			}
			else
			{
				return MR_UNKNOWN;
			}
		}
		else
		{
			return MR_UNKNOWN;
		}
	}
	else  //pPrint2->uOffset < pPrint1->uOffset
	{
		if(pPrint2->uLength != UnknownSize)
		{
			if(pPrint2->uOffset + pPrint2->uLength <= pPrint1->uOffset)
			{
				return MR_NO;
			}
			else
			{
				if(pPrint1->uLength != UnknownSize )
				{
					if(pPrint2->uOffset + pPrint2->uLength < pPrint1->uOffset + pPrint1->uLength)
					{
						return MR_OVERLAP;
					}
					else //if(pPrint2->uOffset + pPrint2->uLength >= pPrint1->uOffset + pPrint1->uLength)
					{
						return MR_COVERED;
					}
				}
				else if(pPrint1->uMaxLength != UnknownSize)
				{
					if(pPrint2->uOffset + pPrint2->uLength >= pPrint1->uOffset + pPrint1->uMaxLength)
					{
						return MR_COVERED;
					}
					else
					{
						return MR_OVERLAP;
					}
				}
				else
				{
					return MR_OVERLAP;
				}
			}
		}
		else if(pPrint2->uMaxLength != UnknownSize)
		{
			if(pPrint2->uOffset + pPrint2->uMaxLength <= pPrint1->uOffset)
			{
				return MR_NO;
			}
			else
			{
				return MR_UNKNOWN;
			}
		}
		else
		{
			return MR_UNKNOWN;
		}
	}
}

MemRelationKind CmpMemFootPrintForSameBase(MemFootPrint * pPrint1, MemFootPrint * pPrint2)
{
	if(pPrint1->GEPVariableIndices.size() == 0 && pPrint2->GEPVariableIndices.size() == 0 )
	{
		return CmpMemFootPrintOffset(pPrint1, pPrint2);
	}

	SmallVector<VariableGEPIndex, 4> GEP1VariableIndices;
	int64_t GEP1BaseOffset = pPrint1->uOffset - pPrint2->uOffset;

	if(pPrint1->GEPVariableIndices.size() > 0 && pPrint2->GEPVariableIndices.size() > 0)
	{
		
		SmallVector<VariableGEPIndex, 4>::iterator itIndicesBegin = pPrint1->GEPVariableIndices.begin();
		SmallVector<VariableGEPIndex, 4>::iterator itIndecesEnd = pPrint1->GEPVariableIndices.end();

		for(; itIndicesBegin != itIndecesEnd; itIndicesBegin ++)
		{
			GEP1VariableIndices.push_back(*itIndicesBegin);
		}

		SmallVector<VariableGEPIndex, 4> GEP2VariableIndices;
		itIndicesBegin = pPrint2->GEPVariableIndices.begin();
		itIndecesEnd = pPrint2->GEPVariableIndices.end();

		for(; itIndicesBegin != itIndecesEnd; itIndicesBegin ++)
		{
			GEP2VariableIndices.push_back(*itIndicesBegin);
		}

		GetIndexDifference(GEP1VariableIndices, GEP2VariableIndices);

		if(GEP1VariableIndices.size() == 0)
		{
			return CmpMemFootPrintOffset(pPrint1, pPrint2);
		}
	}
	else if(pPrint1->GEPVariableIndices.size() > 0 )
	{

		if(pPrint2->uOffset < pPrint1->uOffset)
		{
			if(pPrint2->uLength != UnknownSize)
			{
				if(pPrint2->uLength + pPrint2->uOffset <= pPrint1->uOffset)
				{
					return MR_NO;
				}
			}
			else if(pPrint2->uMaxLength != UnknownSize)
			{
				if(pPrint2->uOffset + pPrint2->uMaxLength <= pPrint1->uOffset)
				{
					return MR_NO;
				}
			}
		}


		SmallVector<VariableGEPIndex, 4>::iterator itIndicesBegin = pPrint1->GEPVariableIndices.begin();
		SmallVector<VariableGEPIndex, 4>::iterator itIndecesEnd = pPrint1->GEPVariableIndices.end();

		for(; itIndicesBegin != itIndecesEnd; itIndicesBegin ++)
		{
			GEP1VariableIndices.push_back(*itIndicesBegin);
		}
	}
	else
	{
		if(pPrint1->uOffset < pPrint2->uOffset )
		{
			if(pPrint1->uLength != UnknownSize )
			{
				if(pPrint1->uOffset + pPrint1->uLength <= pPrint2->uOffset)
				{
					return MR_NO;
				}
			}
			else if(pPrint1->uMaxLength != UnknownSize)
			{
				if(pPrint1->uOffset + pPrint1->uMaxLength <= pPrint2->uOffset)
				{
					return MR_NO;
				}
			}
		}


		SmallVector<VariableGEPIndex, 4>::iterator itIndicesBegin = pPrint2->GEPVariableIndices.begin();
		SmallVector<VariableGEPIndex, 4>::iterator itIndecesEnd = pPrint2->GEPVariableIndices.end();

		for(; itIndicesBegin != itIndecesEnd; itIndicesBegin ++)
		{
			GEP1VariableIndices.push_back(*itIndicesBegin);
		}

	}

	if (!GEP1VariableIndices.empty()) {
		uint64_t Modulo = 0;
		for (unsigned i = 0, e = GEP1VariableIndices.size(); i != e; ++i)
			Modulo |= (uint64_t)GEP1VariableIndices[i].Scale;
		Modulo = Modulo ^ (Modulo & (Modulo - 1));

		// We can compute the difference between the two addresses
		// mod Modulo. Check whether that difference guarantees that the
		// two locations do not alias.
		uint64_t ModOffset = (uint64_t)(GEP1BaseOffset) & (Modulo - 1);
		if (pPrint1->uLength != UnknownSize && pPrint2->uLength != UnknownSize &&
			ModOffset >= pPrint2->uLength && pPrint1->uLength <= Modulo - ModOffset)
			return MR_NO;
	}


	if(pPrint1->uOffset < pPrint2->uOffset)
	{
		if(pPrint1->uMaxLength != UnknownSize)
		{
			if(pPrint1->uOffset + pPrint1->uMaxLength <= pPrint2->uOffset)
			{
				return MR_NO;
			}
		}
	}
	else if(pPrint1->uOffset > pPrint2->uOffset)
	{
		if(pPrint2->uMaxLength != UnknownSize)
		{
			if(pPrint2->uOffset + pPrint2->uMaxLength <= pPrint1->uOffset)
			{
				return MR_NO;
			}

		}
	}

	return MR_UNKNOWN;
}

MemRelationKind CmpInterMemFootPrintForSameBase(MemFootPrint * pPrint1, MemFootPrint * pPrint2)
{
	if(pPrint1->GEPVariableIndices.size() == 0 && pPrint2->GEPVariableIndices.size() == 0 )
	{
		return CmpMemFootPrintOffset(pPrint1, pPrint2);
	}

	SmallVector<VariableGEPIndex, 4> GEP1VariableIndices;
	int64_t GEP1BaseOffset = pPrint1->uOffset - pPrint2->uOffset;

	if(pPrint1->GEPVariableIndices.size() > 0 && pPrint2->GEPVariableIndices.size() == 0)
	{
		if(pPrint2->uOffset < pPrint1->uOffset)
		{
			if(pPrint2->uLength != UnknownSize)
			{
				if(pPrint2->uLength + pPrint2->uOffset <= pPrint1->uOffset)
				{
					return MR_NO;
				}
			}
			else if(pPrint2->uMaxLength != UnknownSize)
			{
				if(pPrint2->uOffset + pPrint2->uMaxLength <= pPrint1->uOffset)
				{
					return MR_NO;
				}
			}
		}


		SmallVector<VariableGEPIndex, 4>::iterator itIndicesBegin = pPrint1->GEPVariableIndices.begin();
		SmallVector<VariableGEPIndex, 4>::iterator itIndecesEnd = pPrint1->GEPVariableIndices.end();

		for(; itIndicesBegin != itIndecesEnd; itIndicesBegin ++)
		{
			GEP1VariableIndices.push_back(*itIndicesBegin);
		}
	}
	else if(pPrint1->GEPVariableIndices.size() == 0 && pPrint2->GEPVariableIndices.size() > 0 )
	{
		if(pPrint1->uOffset < pPrint2->uOffset )
		{
			if(pPrint1->uLength != UnknownSize )
			{
				if(pPrint1->uOffset + pPrint1->uLength <= pPrint2->uOffset)
				{
					return MR_NO;
				}
			}
			else if(pPrint1->uMaxLength != UnknownSize)
			{
				if(pPrint1->uOffset + pPrint1->uMaxLength <= pPrint2->uOffset)
				{
					return MR_NO;
				}
			}
		}


		SmallVector<VariableGEPIndex, 4>::iterator itIndicesBegin = pPrint2->GEPVariableIndices.begin();
		SmallVector<VariableGEPIndex, 4>::iterator itIndecesEnd = pPrint2->GEPVariableIndices.end();

		for(; itIndicesBegin != itIndecesEnd; itIndicesBegin ++)
		{
			GEP1VariableIndices.push_back(*itIndicesBegin);
		}
	}

	if (!GEP1VariableIndices.empty()) {
		uint64_t Modulo = 0;
		for (unsigned i = 0, e = GEP1VariableIndices.size(); i != e; ++i)
			Modulo |= (uint64_t)GEP1VariableIndices[i].Scale;
		Modulo = Modulo ^ (Modulo & (Modulo - 1));

		// We can compute the difference between the two addresses
		// mod Modulo. Check whether that difference guarantees that the
		// two locations do not alias.
		uint64_t ModOffset = (uint64_t)(GEP1BaseOffset) & (Modulo - 1);
		if (pPrint1->uLength != UnknownSize && pPrint2->uLength != UnknownSize &&
			ModOffset >= pPrint2->uLength && pPrint1->uLength <= Modulo - ModOffset)
			return MR_NO;
	}


	if(pPrint1->uOffset < pPrint2->uOffset)
	{
		if(pPrint1->uMaxLength != UnknownSize)
		{
			if(pPrint1->uOffset + pPrint1->uMaxLength <= pPrint2->uOffset)
			{
				return MR_NO;
			}
		}
	}
	else if(pPrint1->uOffset > pPrint2->uOffset)
	{
		if(pPrint2->uMaxLength != UnknownSize)
		{
			if(pPrint2->uOffset + pPrint2->uMaxLength <= pPrint1->uOffset)
			{
				return MR_NO;
			}

		}
	}
	else
	{
		if(pPrint1->uMaxLength != UnknownSize && pPrint2->uMaxLength != UnknownSize)
		{
			return MR_OVERLAP;
		}
	}
	
	return MR_UNKNOWN;
}




}
