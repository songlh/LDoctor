
#include "llvm-Commons/Dependence/DependenceUtility.h"

using namespace std;
using namespace llvm;

namespace llvm_Commons
{

void GetDependingValue(Instruction * pInstruction, vector<Value *> & vecDependingValue)
{

	vecDependingValue.clear();
	//http://llvm.org/releases/3.4.2/docs/LangRef.html
	
	switch(pInstruction->getOpcode())
	{
		//terminal instruction
		case Instruction::Ret:
			{
				ReturnInst * pRetInst = cast<ReturnInst>(pInstruction);
				Value * pReturnValue = pRetInst->getReturnValue();
				if(pReturnValue != NULL)
				{
					vecDependingValue.push_back(pReturnValue);
				}
				break;
			}
		case Instruction::Br:
			{

				BranchInst * pBranch = cast<BranchInst>(pInstruction);
				if(pBranch->isConditional())
				{
					vecDependingValue.push_back(pBranch->getCondition());
				}
				break;
			}
		case Instruction::Switch:
			{
				SwitchInst * pSwitch = cast<SwitchInst>(pInstruction);
				Value * pCondition = pSwitch->getCondition();
				vecDependingValue.push_back(pCondition);
				break;
			}
		case Instruction::IndirectBr:
			{
				break;
			}
		case Instruction::Invoke:
			{
				InvokeInst * pInvoke = cast<InvokeInst>(pInstruction);
				for(unsigned index = 0 ; index < pInvoke->getNumArgOperands() ; index++)
				{
					vecDependingValue.push_back(pInvoke->getArgOperand(index));
				}
				break;
			}
		case Instruction::Resume:
		case Instruction::Unreachable:
			{
				break;
			}
		//binary operations
		case Instruction::Add:            // Standard binary operators...
		case Instruction::FAdd:
		case Instruction::Sub:
		case Instruction::FSub:
		case Instruction::Mul:  
		case Instruction::FMul:
		case Instruction::UDiv:
		case Instruction::SDiv:
		case Instruction::FDiv:
		case Instruction::URem:
		case Instruction::SRem:
		case Instruction::FRem:
		//Logical operators (integer operands)
		case Instruction::Shl:           
		case Instruction::LShr:
		case Instruction::AShr:
		case Instruction::And:
		case Instruction::Or:
		case Instruction::Xor:
		//vector instruction
		case Instruction::ExtractElement:
		case Instruction::InsertElement:
		case Instruction::ShuffleVector:
		//aggregate operations
		case Instruction::ExtractValue:
		case Instruction::InsertValue:
			{
				for(unsigned index = 0; index < pInstruction->getNumOperands(); index ++)
				{
					vecDependingValue.push_back(pInstruction->getOperand(index));
				}

				//errs() << "size: " << vecDependingValue.size() << "\n";
				break;
			}
		//memory instruction
		case Instruction::Alloca:
			{
				break;
			}
		case Instruction::Load:
			{
				LoadInst * pLoad = cast<LoadInst>(pInstruction);
				vecDependingValue.push_back(pLoad->getPointerOperand());
				break;
			}
		case Instruction::AtomicCmpXchg:
		case Instruction::GetElementPtr:
		case Instruction::Store:
			{
				for(unsigned index = 0; index < pInstruction->getNumOperands(); index ++)
				{
					vecDependingValue.push_back(pInstruction->getOperand(index));
				}
				break;
			}
		/*
		case Instruction::Store:
			{
				vecDependingValue.push_back(pInstruction->getOperand(0));
				break;
			}
		*/
		case Instruction::Fence:
			{
				break;
			}
		
		case Instruction::AtomicRMW:
			{
				AtomicRMWInst * pRMWInst = cast<AtomicRMWInst>(pInstruction);
				vecDependingValue.push_back(pRMWInst->getPointerOperand());
				vecDependingValue.push_back(pRMWInst->getValOperand());
				break;
			}
		//Cast operators ...
		case Instruction::Trunc:                
		case Instruction::ZExt:
		case Instruction::SExt:
		case Instruction::FPToUI:
		case Instruction::FPToSI:
		case Instruction::UIToFP:
		case Instruction::SIToFP:
		case Instruction::FPTrunc:
		case Instruction::FPExt:
		case Instruction::PtrToInt:
		case Instruction::IntToPtr:
		case Instruction::BitCast:
		case Instruction::AddrSpaceCast:
		//other instruction
		case Instruction::ICmp:
		case Instruction::FCmp:
			{
				for(unsigned index = 0; index < pInstruction->getNumOperands(); index ++)
				{
					vecDependingValue.push_back(pInstruction->getOperand(index));
				}
				break;
			}
		case Instruction::PHI:
			{

				if(PHINode * pPHI = dyn_cast<PHINode>(pInstruction))
				{
					for(unsigned index = 0; index < pPHI->getNumIncomingValues(); index++)
					{
						vecDependingValue.push_back(pPHI->getIncomingValue(index));
					}
				}		
				break;		
			}
		case Instruction::Select:
			{
				for(unsigned index = 0; index < pInstruction->getNumOperands(); index ++)
				{
					vecDependingValue.push_back(pInstruction->getOperand(index));
				}
				break;
			}
		case Instruction::Call:
			{
				CallInst * pCall = cast<CallInst>(pInstruction);
				Function * pFunction = pCall->getCalledFunction();
				if(pFunction != NULL)
				{
					if(pFunction->getName().startswith("llvm.dbg"))
					{
						break;
					}
				}
				
				for(unsigned index = 0 ; index < pCall->getNumArgOperands() ; index++)
				{
					vecDependingValue.push_back(pCall->getArgOperand(index));
				}
				break;
				
			}
		case Instruction::VAArg:
			{
				for(unsigned index = 0; index < pInstruction->getNumOperands(); index ++)
				{
					vecDependingValue.push_back(pInstruction->getOperand(index));
				}
				break;
			}
		case Instruction::LandingPad:
			{
				break;
			}
		default:
			{
				errs() << "Undefined Instruction in GetDependingValue: " << pInstruction->getOpcodeName() << "\n"; 
				pInstruction->dump();	
				break;
			}
	}

	return;

}


}

