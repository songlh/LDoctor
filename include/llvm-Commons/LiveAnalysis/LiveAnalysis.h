#ifndef _H_LIVEANALYSIS_SONGLH
#define _H_LIVEANALYSIS_SONGLH



namespace llvm
{
   class Function;
   class Instruction;
   class Module;
}

#include <vector>
#include <set>
#include <map>

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm_Commons {

typedef std::set<llvm::Instruction * > SETGen;
typedef std::set<llvm::Instruction * > SETKill;
typedef std::set<llvm::Instruction * > SETBefore;
typedef std::set<llvm::Instruction * > SETAfter;

typedef std::map<llvm::BasicBlock * , SETGen >  MAPBlockGen;
typedef std::map<llvm::BasicBlock *, std::pair<SETKill, MAPBlockGen > > MAPBlockGenKillPair;
typedef std::map<llvm::BasicBlock * , SETBefore> MAPBlockBefore;
typedef std::map<llvm::BasicBlock *, std::pair< SETBefore , SETAfter > > MAPBeforeAfterPair;
typedef std::map<llvm::BasicBlock *, std::pair< MAPBlockBefore , SETAfter > > MAPBlockBeforeAfterPair;


//typical live analysis

void GetGenKillSet(llvm::BasicBlock * , SETGen & setGEN, SETKill & setKILL);
void LiveAnalysis( MAPBeforeAfterPair & , llvm::Function * );

//live analysis for edge
void GetPreciseGenKillSet( MAPBlockGenKillPair & ,  llvm::Function *  );
void PrintMAPBlockGenKillPair(MAPBlockGenKillPair &, llvm::Function * );
void PreciseLiveAnalysis( MAPBlockBeforeAfterPair & , llvm::Function *  );
void PrintPreciseLiveAnalysisResult( MAPBlockBeforeAfterPair & , llvm::Function *  );

}

#endif
