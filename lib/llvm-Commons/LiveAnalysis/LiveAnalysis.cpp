#include "llvm-Commons/LiveAnalysis/LiveAnalysis.h"

using namespace llvm;
using namespace std;


namespace llvm_Commons
{

void GetGenKillSet(BasicBlock * b, SETGen & setGEN, SETKill & setKILL)
{
	setGEN.clear();
	setKILL.clear(); 

	for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie; i ++  )
	{
		setKILL.insert(i);
	}

	for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie; i ++  )
	{
           
		if( PHINode * p = dyn_cast<PHINode>( i ) )
		{
              
			for( User::op_iterator op = p->op_begin(), ope = p->op_end() ; op != ope ; op ++ )
			{
				if( Instruction * pInstruction = dyn_cast<Instruction>(op) )
				{
					setGEN.insert( pInstruction );
				}
			}
		}

		for( User::op_iterator op = i->op_begin(), ope = i->op_end() ; op != ope ; op ++ )
		{
			if( Instruction * pInstruction = dyn_cast<Instruction>(op) )
			{
				if( setKILL.find( pInstruction ) == setKILL.end() )
				{
					setGEN.insert( pInstruction );
				}
			}
		}
	}
} 


void LiveAnalysis( MAPBeforeAfterPair & mapBeforeAfter, Function * F)
{
	for( Function::iterator b = F->begin() , be = F->end(); b !=be ; b ++)
	{
		SETBefore setBefore;
		SETAfter setAfter;
		pair<SETBefore, SETAfter > pairTmp;
		pairTmp.first = setBefore;
		pairTmp.second = setAfter;
		mapBeforeAfter[b] = pairTmp;
	}
       
	vector< BasicBlock * > workList;

	for( Function::iterator b = F->begin() , be = F->end() ; b != be ; b ++ )
	{
		workList.push_back(b);
	}
    
	while( workList.size() != 0 )
	{
		BasicBlock * b = workList[workList.size()-1];
		workList.pop_back();           
           
		SETGen setGEN;
		SETKill setKILL;
		GetGenKillSet( b , setGEN , setKILL );
         
		SETAfter::iterator itBegin = mapBeforeAfter[b].second.begin();
		SETAfter::iterator itEnd = mapBeforeAfter[b].second.end();
            
		while( itBegin != itEnd)
		{
			mapBeforeAfter[b].first.insert(*itBegin);
			itBegin ++;
		}
		itBegin = setKILL.begin();
		itEnd = setKILL.end();
            
		while( itBegin != itEnd )
		{
			if( mapBeforeAfter[b].first.find( (* itBegin) ) != mapBeforeAfter[b].first.end() )
			{
				mapBeforeAfter[b].first.erase(*itBegin);
			}
			itBegin ++;
		}
           
		itBegin = setGEN.begin();
		itEnd = setGEN.end();
        
		while( itBegin != itEnd )
		{
			mapBeforeAfter[b].first.insert((*itBegin));
			itBegin++;
		}   
            
		for( pred_iterator PI = pred_begin(b) , E = pred_end(b); PI != E ; ++PI )
		{
			BasicBlock * pBlock = *PI;
			bool bFlag = true;
           
			SETBefore::iterator setBegin = mapBeforeAfter[b].first.begin();
			SETBefore::iterator setEnd = mapBeforeAfter[b].first.end();
                   
			while( setBegin != setEnd )
			{
				if( mapBeforeAfter[pBlock].second.find( *setBegin ) == mapBeforeAfter[pBlock].second.end() )
				{
					mapBeforeAfter[pBlock].second.insert(*setBegin);
					bFlag = false;
                         
				}
				setBegin ++;
			}

			if(!bFlag)
			{
				workList.push_back(pBlock);
			}
                 
		}

	}

}









void GetPreciseGenKillSet( MAPBlockGenKillPair & mapGenKill,  llvm::Function * F  )
{
	for(Function::iterator b = F->begin(), be = F->end(); b != be ; b ++ )
	{
		SETKill setKill;
		MAPBlockGen mapGen;
		SETGen setGen;
         
		for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie ; i ++ )
		{      
			setKill.insert(i);
  
			if( !isa<PHINode>(i) )
			{
				for( User::op_iterator op = i->op_begin() , ope = i->op_end() ; op != ope ; op ++ )
				{
					if( Instruction * pInstruction = dyn_cast<Instruction>(op) )
					{
						if(setKill.find(pInstruction) == setKill.end() )
						{
							setGen.insert(pInstruction);
						}
					}
				}
			}
		}

		for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie ; i ++ )
		{
			if( PHINode * pPHINode = dyn_cast<PHINode>(i) )
			{
				unsigned uIncomingNumber = pPHINode->getNumIncomingValues();
				unsigned uIndex = 0;

				for(; uIndex < uIncomingNumber; uIndex++)
				{
					BasicBlock * pIncomingBlock = pPHINode->getIncomingBlock(uIndex);
 
					if(mapGen.find(pIncomingBlock) == mapGen.end() )
					{
						SETGen genTmp;
						SETGen::iterator itSetGenBegin = setGen.begin();
						SETGen::iterator itSetGenEnd = setGen.end();
						while(itSetGenBegin != itSetGenEnd )
						{
							genTmp.insert(*itSetGenBegin);
							itSetGenBegin ++;
						}
                  
						if(Instruction * pInstructionResult = dyn_cast<Instruction>(pPHINode->getIncomingValue(uIndex)) )
						{
							genTmp.insert(pInstructionResult);
						}
                 
						mapGen[pIncomingBlock] = genTmp;
					}
					else
					{
						SETGen::iterator itSetGenBegin = setGen.begin();
						SETGen::iterator itSetGenEnd = setGen.end();
						while(itSetGenBegin != itSetGenEnd )
						{
							mapGen[pIncomingBlock].insert(*itSetGenBegin);
							itSetGenBegin ++;
						}

						if(Instruction * pInstructionResult = dyn_cast<Instruction>(pPHINode->getIncomingValue(uIndex)) )
						{
							mapGen[pIncomingBlock].insert(pInstructionResult);
						}
                             
					}    
                 
                     
				}
			} //if( PHINode * pPHINode = dyn_cast<PHINode>(i) )
		} //for(BasicBlock::iterator

		for(pred_iterator PI = pred_begin(b), E = pred_end(b); PI != E ; ++ PI )
		{
			if(mapGen.find(*PI) == mapGen.end() )
			{
				SETGen genTmp;
				SETGen::iterator itSetGenBegin = setGen.begin();
				SETGen::iterator itSetGenEnd = setGen.end();

				while(itSetGenBegin != itSetGenEnd )
				{
					genTmp.insert(*itSetGenBegin);
					itSetGenBegin ++;
				}

				mapGen[*PI] = genTmp;
			}
		}
             

		pair<SETKill, MAPBlockGen > pairTmp;
		pairTmp.first = setKill;
		pairTmp.second = mapGen;
        
		mapGenKill[b] = pairTmp;
	}

}


void PrintMAPBlockGenKillPair(MAPBlockGenKillPair & mapBlockGenKillPair, llvm::Function * pFunction )
{
    
	errs() << "Print Gen-Kill set for function " <<  pFunction->getName() << ":\n";
  

	MAPBlockGenKillPair::iterator itMapGenKillBegin = mapBlockGenKillPair.begin();
	MAPBlockGenKillPair::iterator itMapGenKillEnd = mapBlockGenKillPair.end();
   
	while( itMapGenKillBegin != itMapGenKillEnd )
	{
		errs() << itMapGenKillBegin->first->getName() << ":\n";

		SETKill::iterator itSetKillBegin = itMapGenKillBegin->second.first.begin();
		SETKill::iterator itSetKillEnd = itMapGenKillBegin->second.first.end();
   
		errs() << "KILL("<< itMapGenKillBegin->second.first.size()  <<"):\n";
		while(itSetKillBegin != itSetKillEnd )
		{
			errs() << (*itSetKillBegin)->getName() << " ";
			itSetKillBegin ++;
		}
		errs() << "\n";
  
		errs() << "GEN: \n";

		MAPBlockGen::iterator itMapGenBegin = itMapGenKillBegin->second.second.begin() ;
		MAPBlockGen::iterator itMapGenEnd = itMapGenKillBegin->second.second.end() ;
     
		while(itMapGenBegin != itMapGenEnd )
		{
			SETGen::iterator itSetGenBegin = itMapGenBegin->second.begin();
			SETGen::iterator itSetGenEnd = itMapGenBegin->second.end();
			errs() << itMapGenBegin->first->getName() << ": ";
			while(itSetGenBegin != itSetGenEnd )
			{
				errs() << (*itSetGenBegin)->getName() << " ";
				itSetGenBegin ++;
			}

			errs() << "\n";
			itMapGenBegin++;
		}

		errs() << "===================================\n";
		itMapGenKillBegin ++;
	}
}


void PreciseLiveAnalysis( MAPBlockBeforeAfterPair & mapBeforeAfter, Function * F )
{
	vector<BasicBlock *> vecWorkList;

	mapBeforeAfter.clear();

	for(Function::iterator b = F->begin() , be = F->end(); b != be ; b ++ )
	{
		MAPBlockBefore  mapBefore;
       
		for(pred_iterator PI = pred_begin(b), E = pred_end(b); PI != E ; ++ PI )
		{
			SETBefore before;
			mapBefore[*PI] = before;
		} 

		SETAfter setAfter;

		pair< MAPBlockBefore , SETAfter >  pairTmp;
		pairTmp.first = mapBefore;
		pairTmp.second = setAfter;

		mapBeforeAfter[b] = pairTmp;       
		vecWorkList.push_back(b);
	}

	MAPBlockGenKillPair mapPreciseGenKill;

	GetPreciseGenKillSet( mapPreciseGenKill ,  F );

	while(vecWorkList.size() > 0 )
	{
		BasicBlock * b = vecWorkList[vecWorkList.size() -1 ];
		vecWorkList.pop_back();

		SETKill kill = mapPreciseGenKill[b].first;
		MAPBlockGen mapGen = mapPreciseGenKill[b].second;

		for(pred_iterator PI = pred_begin(b), E = pred_end(b); PI != E ; ++ PI )
		{
			SETAfter::iterator itAfterBegin = mapBeforeAfter[b].second.begin();
			SETAfter::iterator itAfterEnd = mapBeforeAfter[b].second.end();
 
			while( itAfterBegin != itAfterEnd )
			{
				mapBeforeAfter[b].first[*PI].insert(*itAfterBegin);
				itAfterBegin++;
			}

			SETKill::iterator itKillBegin = kill.begin();
			SETKill::iterator itKillEnd = kill.end();

			while(itKillBegin != itKillEnd )
			{
				if(mapBeforeAfter[b].first[*PI].find(*itKillBegin) != mapBeforeAfter[b].first[*PI].end())
				{
					mapBeforeAfter[b].first[*PI].erase(*itKillBegin);
				}
				itKillBegin++;
			}

			SETGen::iterator itGenBegin = mapGen[*PI].begin();
			SETGen::iterator itGenEnd = mapGen[*PI].end();

			while(itGenBegin != itGenEnd)
			{
				mapBeforeAfter[b].first[*PI].insert(*itGenBegin);
				itGenBegin++;
			}

			SETBefore::iterator itBeforeBegin = mapBeforeAfter[b].first[*PI].begin();
			SETBefore::iterator itBeforeEnd = mapBeforeAfter[b].first[*PI].end();
             
			bool bFlag = false;
			while(itBeforeBegin != itBeforeEnd)
			{
				if(mapBeforeAfter[*PI].second.find(*itBeforeBegin) == mapBeforeAfter[*PI].second.end() )
				{
					mapBeforeAfter[*PI].second.insert(*itBeforeBegin);
					bFlag = true;
				}

				itBeforeBegin++;
			}

			if(bFlag)
			{
				vecWorkList.push_back(*PI);
			}
		}
	}

}

void PrintPreciseLiveAnalysisResult( MAPBlockBeforeAfterPair & mapBeforeAfter , Function * pFunction  )
{
  
	errs() << "\nLive Analysis Result for Function " << pFunction->getName() << ":\n" ;

	MAPBlockBeforeAfterPair::iterator itMapBeforeAfterBegin =    mapBeforeAfter.begin();
	MAPBlockBeforeAfterPair::iterator itMapBeforeAfterEnd = mapBeforeAfter.end();

	while(itMapBeforeAfterBegin != itMapBeforeAfterEnd )
	{
		errs() << itMapBeforeAfterBegin->first->getName() << ":\n";
		errs() << "Before: \n";
          
		MAPBlockBefore::iterator itMapBeforeBegin = itMapBeforeAfterBegin->second.first.begin();
		MAPBlockBefore::iterator itMapBeforeEnd = itMapBeforeAfterBegin->second.first.end();
  
		while( itMapBeforeBegin != itMapBeforeEnd )
		{
			errs() << itMapBeforeBegin->first->getName() << ": ";
			SETBefore::iterator itSetBegin = itMapBeforeBegin->second.begin();
			SETBefore::iterator itSetEnd = itMapBeforeBegin->second.end();
			while(itSetBegin != itSetEnd )
			{
				errs() << (*itSetBegin)->getName() << " ";
				itSetBegin++;
			}

			errs() << "\n";
			itMapBeforeBegin++;
		}
       
		errs() << "After: \n";
		SETAfter::iterator itAfterBegin =  itMapBeforeAfterBegin->second.second.begin();
		SETAfter::iterator itAfterEnd = itMapBeforeAfterBegin->second.second.end();

		while(itAfterBegin != itAfterEnd )
		{
			errs() << (*itAfterBegin)->getName() << " ";
			itAfterBegin++;
		}
		errs() << "\n";
		errs() << "=======================\n" ; 
		itMapBeforeAfterBegin++;
	}
}

}
