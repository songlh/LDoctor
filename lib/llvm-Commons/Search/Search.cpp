#include <stdio.h>
#include <stdlib.h>

#include "llvm/DebugInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm-Commons/Search/Search.h"


using namespace std;
using namespace llvm;

namespace llvm_Commons
{


Function * SearchFunctionByName(Module & M, string & strFileName, string & strFunctionName, unsigned uSourceCodeLine)
{
	Function * pFunction = NULL;
	char pPath[400];

	for( Module::iterator f = M.begin(), fe = M.end(); f != fe; f ++ )
	{
		if( f->getName().find(strFunctionName) != std::string::npos )
		{
			//errs() << f->getName() << "\n";
			map< string, pair<unsigned int, unsigned int> > mapFunctionBound; 
   
			for( Function::iterator b = f->begin() , be = f->end() ; b != be ; ++ b )
			{
				for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie; ++ i )
				{

					if( MDNode *N = i->getMetadata("dbg") )
					{ 
						DILocation Loc(N);
						string sFileNameForInstruction = Loc.getDirectory().str() + "/" + Loc.getFilename().str();    
						realpath( sFileNameForInstruction.c_str() , pPath);
						sFileNameForInstruction = string(pPath);                        
						unsigned int uLineNoForInstruction = Loc.getLineNumber();

						if( mapFunctionBound.find(sFileNameForInstruction) == mapFunctionBound.end() )
						{
							pair< unsigned int, unsigned int> tmpPair;
							tmpPair.first = uLineNoForInstruction;
							tmpPair.second = uLineNoForInstruction;
							mapFunctionBound[sFileNameForInstruction] = tmpPair;
						}
						else
						{
							if(mapFunctionBound[sFileNameForInstruction].first > uLineNoForInstruction )
							{
								mapFunctionBound[sFileNameForInstruction].first = uLineNoForInstruction;
							}

							if(mapFunctionBound[sFileNameForInstruction].second <  uLineNoForInstruction)
							{
								mapFunctionBound[sFileNameForInstruction].second =  uLineNoForInstruction;
							}
                         
						} //else
					} //if( MDNode *N = i->getMetadata("dbg") )     
				}//for(BasicBlock::iterator ...)
			} //for( Function::iterator ..)
            
			//if(mapFunctionBound.find(strFileName) != mapFunctionBound.end())
			//{
			//	if(mapFunctionBound[strFileName].first <= uSourceCodeLine && mapFunctionBound[strFileName].second >= uSourceCodeLine)
			//	{
			//		pFunction = f;
			//		break;
			//	}
			//}
			map< string, pair<unsigned int, unsigned int> >::iterator itMapBegin = mapFunctionBound.begin();
			map< string, pair<unsigned int, unsigned int> >::iterator itMapEnd = mapFunctionBound.end();
			while(itMapBegin != itMapEnd)
			{
				if(itMapBegin->first.find(strFileName) != string::npos)
				{
					if(itMapBegin->second.first <= uSourceCodeLine && itMapBegin->second.second >= uSourceCodeLine)
					{
						pFunction = f;
						break;
					}
				}
				itMapBegin ++;
			}
		} // if( f->getName().find(strFunctionName) != std::string::npos )
	} // for( Module::iterator ...)

	return pFunction;
}


void SearchBasicBlocksByLineNo( Function * F, unsigned uLineNo, vector<BasicBlock *> & vecBasicBlocks )
{
	for( Function::iterator b = F->begin() , be = F->end() ; b != be ; ++ b )
	{
		for(BasicBlock::iterator i = b->begin(), ie = b->end() ; i != ie; ++ i )
		{     
			if( MDNode *N = i->getMetadata("dbg") )
			{
				DILocation Loc(N);
				if( uLineNo == Loc.getLineNumber() )
				{
					vecBasicBlocks.push_back(b);
					break;
				}
			}   
		}
	}

}

Loop * SearchLoopByLineNo( Function * pFunction, LoopInfo * pLI, unsigned uLineNo )
{
	vector<BasicBlock *> vecBasicBlocks;
	SearchBasicBlocksByLineNo( pFunction, uLineNo, vecBasicBlocks);
	unsigned int uDepth = 0;
	BasicBlock * pBlock = NULL;

	for( vector<BasicBlock *>::iterator itBegin = vecBasicBlocks.begin(), itEnd = vecBasicBlocks.end(); itBegin != itEnd ; itBegin ++ )
	{
		if(pLI->getLoopDepth(*itBegin) > uDepth )
		{
			uDepth = pLI->getLoopDepth(*itBegin);
			pBlock = *itBegin;
		}
	}

	if( pBlock == NULL )
	{
		return NULL;
	}
       

	return pLI->getLoopFor(pBlock);

}

}

