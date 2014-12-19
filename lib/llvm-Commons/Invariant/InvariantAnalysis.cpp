

#include "llvm-Commons/Invariant/InvariantAnalysis.h"


namespace llvm_Commons
{

void IndentifyInvariantGlobalVariable(Function * pF, set<Value *> & setGlobalVariable, set<Function *> & setScope)
{

	set<Value *> setValueToCheck;
	for(Function::iterator b = pF->begin(), be = pF->end(); b != be; b++)
	{
		if(isa<UnreachableInst>(b->getTerminator()))
		{
			continue;
		}

		for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie; i++)
		{
			if(LoadInst * pLoad = dyn_cast<LoadInst>(i))
			{
				if(Constant * pConstant = dyn_cast<Constant>( pLoad->getPointerOperand()))
				{
					setValueToCheck.insert(pConstant);
				}
			}
		}
	}


	set<Function *>::iterator itSetBegin = setScope.begin();
	set<Function *>::iterator itSetEnd = setScope.end();

	for(; itSetBegin != itSetEnd; itSetBegin++)
	{	
		Function * pFunction = *itSetBegin;
		for(Function::iterator b = pFunction->begin(), be = pFunction->end(); b != be ; b ++ )
		{
			if(isa<UnreachableInst>(b->getTerminator()))
			{	
				continue;
			}

			for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie ; i ++ )
			{
				if(StoreInst * pStore = dyn_cast<StoreInst>(i))
				{
					if(Constant * pConstant = dyn_cast<Constant>(pStore->getPointerOperand()))
					{
						if(setValueToCheck.find(pConstant) != setValueToCheck.end() )
						{
							setValueToCheck.erase(pConstant);
							if(setValueToCheck.size() == 0 )
							{
								goto DONE;
							}
						}
					}
				}
			}
		}

	}

DONE:
	set<Value *>::iterator itSetValueBegin = setValueToCheck.begin();
	set<Value *>::iterator itSetValueEnd = setValueToCheck.end();

	for(; itSetValueBegin != itSetValueEnd; itSetValueBegin++)
	{
		setGlobalVariable.insert(*itSetValueBegin);
	}
}


void GetGetElemPtrAllUses(Instruction * pGetElement, set<Instruction *> & setUse)
{
	for(Value::use_iterator u = pGetElement->use_begin(), ue = pGetElement->use_end(); u != ue ; u ++ )
	{
		if(GetElementPtrInst * pGet = dyn_cast<GetElementPtrInst>(*u))
		{
			GetGetElemPtrAllUses(pGet, setUse);
		}
		else if(CastInst * pCast = dyn_cast<CastInst>(*u))
		{
			GetGetElemPtrAllUses(pCast, setUse);
		}
		else if(Instruction * pInstruction = dyn_cast<Instruction>(*u))
		{
			setUse.insert(pInstruction);
		}
		else
		{
			(*u)->dump();
		}
	}

}

void IndentifyInvariantArray(Function * pF, set<Value *> & setArray, set<Function *> & setScope )
{
	int iGetElementNum = 0;

	set<Value *> setOneDimensionArray;
	set<Value *> setTwoDimensionArray;
	set<Value *> setStructArray;

	for(Function::iterator b = pF->begin(), be = pF->end(); b != be; b++)
	{
		if(isa<UnreachableInst>(b->getTerminator()))
		{
			continue;
		}

		for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie; i++)
		{
			if(GetElementPtrInst * pGetElement = dyn_cast<GetElementPtrInst>(i))
			{
				if(GlobalVariable * pArrayPointer = dyn_cast<GlobalVariable>(pGetElement->getPointerOperand()))
				{
					iGetElementNum += 1;
					if(PointerType * pPointerType = dyn_cast<PointerType>(pArrayPointer->getType()))
					{
						if(ArrayType * pArrayType = dyn_cast<ArrayType>(pPointerType->getElementType()))
						{
							if(isa<IntegerType>(pArrayType->getElementType()))  //one dimension array of integer
							{
								setOneDimensionArray.insert(pArrayPointer);
							}
							else if(ArrayType * pSecondDimensionArray = dyn_cast<ArrayType>(pArrayType->getElementType()))
							{
								//two dimension array of integer
								if(isa<IntegerType>(pSecondDimensionArray->getElementType()))
								{
									setTwoDimensionArray.insert(pArrayPointer);
								}
							}
							else if(isa<StructType>(pArrayType->getElementType()))
							{
								//array of structure
								setStructArray.insert(pArrayPointer);
							}
						}
					}
				}
				
			}
		}
	}

	/*
	errs() << "GetElementPtrInst Number: " << iGetElementNum << "\n";
	errs() << "Dimension One: " << setOneDimensionArray.size() << "\n";
	errs() << "Dimension Two: " << setTwoDimensionArray.size() << "\n";
	errs() << "ArrayStruct :"   << setStructArray.size() << "\n";
	*/
	set<Value *> setArrayToBeCheck;

	set<Value *>::iterator itSetBegin = setOneDimensionArray.begin();
	set<Value *>::iterator itSetEnd = setOneDimensionArray.end();
	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		setArrayToBeCheck.insert(*itSetBegin);
	}


	itSetBegin = setTwoDimensionArray.begin();
	itSetEnd = setTwoDimensionArray.end();
	for(; itSetBegin != itSetEnd; itSetBegin++ )
	{
		setArrayToBeCheck.insert(*itSetBegin);
	}

	itSetBegin = setStructArray.begin();
	itSetEnd = setStructArray.end();
	for(; itSetBegin != itSetEnd; itSetBegin ++ )
	{
		setArrayToBeCheck.insert(*itSetBegin);
	}

	itSetBegin = setArrayToBeCheck.begin();
	itSetEnd = setArrayToBeCheck.end();

	for(; itSetBegin != itSetEnd; itSetBegin++ )
	{
		Value * pArray = *itSetBegin;
		bool bChanged = false;

		for(Value::use_iterator u = pArray->use_begin(), ue = pArray->use_end(); u != ue; u++ )
		{
			if(Instruction * pInstruction = dyn_cast<Instruction>(*u))
			{
				if(setScope.find(pInstruction->getParent()->getParent()) == setScope.end() )
				{
					continue;
				}

				if(GetElementPtrInst * pGetElement = dyn_cast<GetElementPtrInst>(pInstruction))
				{
					set<Instruction *> setUse;
					GetGetElemPtrAllUses(pGetElement, setUse);

					set<Instruction *>::iterator itSetInstBegin = setUse.begin();
					set<Instruction *>::iterator itSetInstEnd = setUse.end();

					for(; itSetInstBegin != itSetInstEnd; itSetInstBegin++)
					{
						if((*itSetInstBegin)->mayWriteToMemory())
						{
							bChanged = true;
							break;
						}
					}
				}
				else
				{
					errs() << "Other Usage of Global Array\n";
					pInstruction->dump();
				}
			}

			if(bChanged)
			{
				break;
			}
		}

		if(!bChanged)
		{
			setArray.insert(*itSetBegin);
		}
	}

	//errs() << "unchanged array: " << setArray.size() << "\n";
}


}

