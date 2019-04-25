#include <algorithm>
#include <cassert>
#include <iterator>
#include <memory>
#include <utility>
#include <vector>
#include <unordered_set>
#include <queue>
#include <stack>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/Local.h"
#include "/home/reshabh/LLVMIRCPP/LLVM-IR-Plus-Plus/include/LLVMIR++.h"

using namespace llvm;

namespace {

#define DEBUG_TYPE "vfcr"



using ExpressionSet = std::unordered_set<Expression*, std::hash<Expression*>, Expression::ExpEqual>;
using ExpressionMap = std::map<StoreInst*, ExpressionSet>;
using Alias = std::map<Expression*, ExpressionSet>;
using AliasExpressionMap = std::map<StoreInst*, Alias>;
using InstructionQueue = std::queue<Instruction*>;
using InstructionStack = std::stack<Instruction*>;
using InstructionSet = std::set<Instruction*>;

class VFCRPass : public FunctionPass {
       private:
 	InstMetaMap metaMap; 
	CFG*	grcfg;
	ExpressionMap DemandIn, DemandOut;
	AliasExpressionMap AliasIn, AliasOut;
	inst_iterator startInstIterator;
	inst_iterator endInstIterator;
	Expression* Origin;
	Instruction* StartInst;
	Instruction* EndInst;
	InstructionStack DemandWorkList;
	InstructionStack AliasWorkList;
	InstructionSet DemandWorkListSet;
	InstructionSet AliasWorkListSet;
       public:
	static char ID;
	VFCRPass() : FunctionPass(ID) {}
	bool isVirtualCallSite(CallSite cs);
	bool isVirtualCall(Instruction&);
	void analyse(Instruction &);	
	void print(Expression*);
	bool canExpressionPoint(Expression*);
	void absName(Expression*, ExpressionSet&, StoreInst*);
	bool expressionSetInDemandOut(ExpressionSet, StoreInst*);
	bool isExpressionEqual(Expression*, Expression*);
	ExpressionSet LeftDemandGen(Expression*, StoreInst*);
	bool isAddressTaken(Expression*);
	ExpressionSet findKill(Expression*);
	ExpressionSet RightDemandGen(Expression*);
	bool isExpInDout(Expression*, StoreInst*);
	void printAliasIn(StoreInst*);
	void printAliasOut(StoreInst*);
	void printAliasSet(Alias);
	void printSet(ExpressionSet);
	void printExpTrace(Expression*);
	bool isAlreadyInSet(ExpressionSet, Expression*);
	Expression* getOrigin(Instruction*);
	Instruction* getStartInst(Instruction*);
	Instruction* getEndInst(Instruction*);
	void findDemand(StoreInst*);
	void findAlias(StoreInst*);
	bool isAliasEqual(Alias, Alias);
	bool runOnFunction(Function& F) override {
		startInstIterator = inst_begin(F);
		endInstIterator = inst_end(F);
		endInstIterator--;
		// Iterate over basicblocks
		metaMap = getAnalysis<LLVMIRPlusPlusPass>().getIRPlusPlus();
		grcfg  = getAnalysis<LLVMIRPlusPlusPass>().getCFG();
		for (BasicBlock& BB : F) {
			// Iterate over Instructions
			for (Instruction& I : BB) {
				// For every store instruction
				if(isVirtualCall(I)){
					// Round-robin method "analyse"
					// One pass consists of one demand pass and one alias pass
					// though the solution if not mop after one pass
//					analyse(I);
					LLVM_DEBUG(dbgs() << "#######################################################\n\n\n";);
					Origin = getOrigin(&I);		
					Instruction* FunctionEndInst = &*endInstIterator;
					while(!isa<StoreInst>(FunctionEndInst)){
						FunctionEndInst = FunctionEndInst -> getPrevNonDebugInstruction();
					}
					EndInst = FunctionEndInst;
					Instruction* FunctionStartInst = &*startInstIterator;
					while(!isa<StoreInst>(FunctionStartInst)){
						FunctionStartInst = FunctionStartInst -> getNextNonDebugInstruction();
					}
					StartInst = FunctionStartInst;
					DemandOut[cast<StoreInst>(EndInst)].insert(Origin);
					if(EndInst && DemandWorkListSet.find(EndInst) == DemandWorkListSet.end()){
						DemandWorkList.push(EndInst);
						LLVM_DEBUG(dbgs() << "Adding " << *EndInst << " to the demand list \n";);
						DemandWorkListSet.insert(EndInst);
					}
					if(StartInst && AliasWorkListSet.find(StartInst) == AliasWorkListSet.end()){
						AliasWorkList.push(StartInst);
						LLVM_DEBUG(dbgs() << "Adding " << *StartInst << " to the alias list \n";);
						AliasWorkListSet.insert(StartInst);
					}
					while(!(DemandWorkList.empty() && AliasWorkList.empty())){
						std::map<Instruction*, Instruction*> FuncBeginInstToCallSitePrevInst;
						std::map<Instruction*, Instruction*> FuncEndInstToCallSitePrevInst;
						while(!DemandWorkList.empty()){
							Instruction* Inst = DemandWorkList.top();
							DemandWorkList.pop();
							DemandWorkListSet.erase(Inst);
							LLVM_DEBUG(dbgs() << ">>>> " << *Inst << "\n"; );
							if(false /* CallInst* callInst = dyn_cast<CallInst>(Inst) */){
								CallInst* callInst;
								LLVM_DEBUG(dbgs() << "Call encountered " << *callInst << "\n";);
								Function* calledFunction = callInst -> getCalledFunction();
								// TODO DOUBT: if it is an indirect call it will return null :(
								// TODO DOUBT: How to match function arguments passed as reference
								if(calledFunction){
									if(calledFunction -> isIntrinsic()){
										LLVM_DEBUG(dbgs() << "Gracefully ^_^ ignoring llvm intrinsic function \n");
									} else {
										LLVM_DEBUG(dbgs() << "Direct Call for function "<< *calledFunction << "\n";);
										LLVM_DEBUG(dbgs() << "~~~~~~ Damage Control ############# \n";);
										inst_iterator callEndInstIter = inst_end(calledFunction);
										callEndInstIter--;
										Instruction* callEndInst = &*callEndInstIter;
										inst_iterator callStartInstIter = inst_begin(calledFunction);
										Instruction* callStartInst = &*callStartInstIter;
										Instruction* tempPreInst = Inst -> getPrevNonDebugInstruction();
										if(tempPreInst){
											FuncBeginInstToCallSitePrevInst[callStartInst] = tempPreInst;
											LLVM_DEBUG(dbgs() << *callStartInst << " -> " << *tempPreInst << "\n";);
										}
										Instruction* tempNextInst = Inst -> getNextNonDebugInstruction();
										if(tempNextInst){
											FuncEndInstToCallSitePrevInst[callEndInst] = tempNextInst;
											LLVM_DEBUG(dbgs() << *callEndInst << " -> " << *tempNextInst << "\n";);
										}
										Inst = callEndInst;
									}
								} else {
									LLVM_DEBUG(dbgs() << "Indirect call, can't do much :(\n";);
								}
							} 
							if(Inst){
								if(StoreInst* storeInst = dyn_cast<StoreInst>(Inst)){
									ExpressionSet OldDemandIn = DemandIn[storeInst];
									findDemand(storeInst);
									if(OldDemandIn == DemandIn[storeInst]){
										// FAQ : When to stop it?
										// here :p
										continue;
									}
								}	
							}
							Instruction* PreInst = nullptr;
							if(Inst){
								PreInst = Inst -> getPrevNonDebugInstruction();
							}
							if(PreInst == nullptr){
								if(FuncBeginInstToCallSitePrevInst.find(Inst) != FuncBeginInstToCallSitePrevInst.end()){
									PreInst = FuncBeginInstToCallSitePrevInst[Inst];
								}
							}
							if(PreInst != nullptr){
								if(DemandWorkListSet.find(PreInst) == DemandWorkListSet.end()){
									DemandWorkList.push(PreInst);
									LLVM_DEBUG(dbgs() << "Adding " << *PreInst << " to the demand list \n";);
									DemandWorkListSet.insert(PreInst);
								}
								if(AliasWorkListSet.find(PreInst) == AliasWorkListSet.end()){
									if(true || isa<StoreInst>(PreInst)){
										AliasWorkList.push(PreInst);
										LLVM_DEBUG(dbgs() << "Adding " << *PreInst << " to the alias list \n";);
										AliasWorkListSet.insert(PreInst);
									}
								}
							}
						}
						std::stack<Instruction*> aliasCallsiteStack;
						while(!AliasWorkList.empty()){
							LLVM_DEBUG(dbgs() << "Size of alias worklist is " << AliasWorkList.size() << "\n";);
							Instruction* Inst = AliasWorkList.top();
							AliasWorkList.pop();
							AliasWorkListSet.erase(Inst);
							LLVM_DEBUG(dbgs() << ">>>> " << *Inst << "\n"; );
							if(false /* CallInst* callInst = dyn_cast<CallInst>(Inst) */){
								CallInst* callInst;
								LLVM_DEBUG(dbgs() << "Call encountered " << *callInst << "\n";);
								Function* calledFunction = callInst -> getCalledFunction();
								// TODO DOUBT: if it is an indirect call it will return null :(
								// TODO DOUBT: How to match function arguments passed as reference
								if(calledFunction){
									if(calledFunction -> isIntrinsic()){
										LLVM_DEBUG(dbgs() << "Gracefully ^_^ ignoring llvm intrinsic function \n");
									} else {
										LLVM_DEBUG(dbgs() << "Direct Call for function "<< *calledFunction << "\n";);
										inst_iterator callEndInstIter = inst_end(calledFunction);
										callEndInstIter--;
										Instruction* callEndInst = &*callEndInstIter;
										inst_iterator callStartInstIter = inst_begin(calledFunction);
										Instruction* callStartInst = &*callStartInstIter;
										Instruction* tempPreInst = Inst -> getPrevNonDebugInstruction();
										if(tempPreInst){
											FuncBeginInstToCallSitePrevInst[callStartInst] = tempPreInst;
										}
										Instruction* tempNextInst = Inst -> getNextNonDebugInstruction();
										if(tempNextInst){
											FuncEndInstToCallSitePrevInst[callEndInst] = tempNextInst;
											LLVM_DEBUG(dbgs() << "add " << *tempNextInst << " " << *callEndInst << "\n";);
										}
										Inst = callStartInst;
									}
								} else {
									LLVM_DEBUG(dbgs() << "Indirect call, can't do much :(\n";);
								}
							} 
							if(Inst){
								if(StoreInst* storeInst = dyn_cast<StoreInst>(Inst)){
									Alias OldAliasOut = AliasOut[storeInst];
									findAlias(storeInst);
									LLVM_DEBUG(dbgs() << "Old Alias Out \n");
									printAliasSet(OldAliasOut);
									LLVM_DEBUG(dbgs() << "Alias Out \n");
									printAliasSet(AliasOut[storeInst]);
									LLVM_DEBUG(dbgs() << "DO they look equal? ";);
									if(isAliasEqual(OldAliasOut, AliasOut[storeInst])){
										LLVM_DEBUG(dbgs() << "YES \n";);
										continue;
									}
									LLVM_DEBUG(dbgs() << "NO \n ";);
								}
							}
							Instruction* NextInst = nullptr;
							if(Inst){
								NextInst = Inst -> getNextNonDebugInstruction();
							}
							if(NextInst == nullptr){
								if(FuncEndInstToCallSitePrevInst.find(Inst) != FuncEndInstToCallSitePrevInst.end()){
									NextInst = FuncEndInstToCallSitePrevInst[Inst];
								}
							}
							if(NextInst != nullptr){
								LLVM_DEBUG(dbgs() << "Adding " << *NextInst << " into the worklist \n";);
								if(DemandWorkListSet.find(NextInst) == DemandWorkListSet.end()){
									if(true || isa<StoreInst>(NextInst)){
										DemandWorkList.push(NextInst);
										LLVM_DEBUG(dbgs() << "Adding " << *NextInst << " to the demand list \n";);
										DemandWorkListSet.insert(NextInst);
									}
								}
								if(AliasWorkListSet.find(NextInst) == AliasWorkListSet.end()){
									AliasWorkList.push(NextInst);
									LLVM_DEBUG(dbgs() << "Adding " << *NextInst << " to the alias list \n";);
									AliasWorkListSet.insert(NextInst);
								}
							}
						}
					}
				}
			}
		}
		return false;
	}

	void getAnalysisUsage(AnalysisUsage &AU) const override {
	    AU.addRequired<LLVMIRPlusPlusPass>();
	}
};

bool VFCRPass::isVirtualCall(Instruction &I) {
	if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
		CallSite cs(&I);
		if (isVirtualCallSite(cs)) {
			return true;
		}
	}
	return false;
}

bool VFCRPass::isVirtualCallSite(CallSite cs) {
	if (cs.getCalledFunction() != NULL) return false;
	const Value *vfunc = cs.getCalledValue();
	if (const LoadInst *vfuncloadinst = dyn_cast<LoadInst>(vfunc)) {
		const Value *vfuncptr =
		    vfuncloadinst->getPointerOperand();
		if (const GetElementPtrInst *vfuncptrgepinst =
			dyn_cast<GetElementPtrInst>(vfuncptr)) {
			if (vfuncptrgepinst->getNumIndices() != 1)
				return false;
			const Value *vtbl =
			    vfuncptrgepinst->getPointerOperand();
			if (isa<LoadInst>(vtbl)) {
				return true;
			}
		}
	}
	return false;
}

Expression* VFCRPass::getOrigin(Instruction* I){
	LLVM_DEBUG(dbgs() << "Analysing call " << *I <<  "\n";);
	Value* callValue = I -> getOperand(0);
	LoadInst* inst = dyn_cast<LoadInst>(callValue);
	Expression* Origin = new RHSExpression(inst -> getPointerOperand());
	LLVM_DEBUG(dbgs() << "Set Origin to ";);
	print(Origin);
	LLVM_DEBUG(dbgs() << "\n";);
	return Origin;
}

Instruction* VFCRPass::getStartInst(Instruction* I){
	Instruction* StartInst = I;
	LLVM_DEBUG(dbgs() << "Setting start instruction as " << *StartInst << "\n";);
	return StartInst;
}

Instruction* VFCRPass::getEndInst(Instruction* I){
	Instruction*  EndInst = dyn_cast<Instruction>(I);
	// FAQ: Do I need to start from the top of function, probably yes as there
	// might be some call?
	// NO: We need this, demand is stored against the store instruction, so we
	// need to make sure that we start with a store.
	//
	// TODO: DOUBT: How to handle the case with calls before the stores
	while(!isa<StoreInst>(EndInst)){
		EndInst = EndInst -> getPrevNonDebugInstruction();
	}
	LLVM_DEBUG(dbgs() << "Setting end instruction as " << *EndInst << "\n";);
	return EndInst;
}

void VFCRPass::findDemand(StoreInst* storeInst){
	LLVM_DEBUG(dbgs() << "----------------------------------------------\n" ;);
	LLVM_DEBUG(dbgs() << "Analysing Instruction " << *storeInst << "\n";);
	LLVM_DEBUG(dbgs() << "Decoded Instruction " ;);
	// TODO: This is not good!
	if(!metaMap[storeInst]){
		return;
	}
	LLVM_DEBUG(dbgs() << metaMap[storeInst] << "\n";);
	print(metaMap[storeInst] -> LHS);
	LLVM_DEBUG(dbgs() << " = ";);
	print(metaMap[storeInst] -> RHS);
	LLVM_DEBUG(dbgs() << "\n";);
	// ln and rn
	ExpressionSet LHSExpressions;
	ExpressionSet RHSExpressions;
	Expression* LHSExp = metaMap[storeInst] -> LHS;
	Expression* RHSExp = metaMap[storeInst] -> RHS;
	// calculate ln(bar) and rn(bar)
	if(!isAlreadyInSet(LHSExpressions, LHSExp)){
		LHSExpressions.insert(LHSExp);
	}
	if(canExpressionPoint(LHSExp)){
		absName(LHSExp, LHSExpressions, storeInst);
	}
	if(!isAlreadyInSet(RHSExpressions, RHSExp)){
		RHSExpressions.insert(RHSExp);
	}
	if(canExpressionPoint(RHSExp)){
		absName(RHSExp, RHSExpressions, storeInst);
	}
	LLVM_DEBUG(dbgs() << "Values in LBar set \n";);
	printSet(LHSExpressions);
	LLVM_DEBUG(dbgs() << "Values in RBar set \n";);
	printSet(RHSExpressions);

	// calculate demand gen
	bool LBarInDemandOut = expressionSetInDemandOut(LHSExpressions, storeInst);		
	bool RBarInDemandOut = expressionSetInDemandOut(RHSExpressions, storeInst);

	ExpressionSet LDemandGen;
	ExpressionSet RDemandGen;
	if(LBarInDemandOut && RBarInDemandOut){
		LLVM_DEBUG(dbgs() << "LBar and RBar both are in demand out \n" ;);
		LDemandGen = LeftDemandGen(RHSExp, storeInst);
		RDemandGen = RightDemandGen(LHSExp);
	} else if(LBarInDemandOut){
		LLVM_DEBUG(dbgs() << "Only LBar is in demand out \n" ;);
		LLVM_DEBUG(dbgs() << "Running LDGen over RHSExp \n" ;);
		LDemandGen = LeftDemandGen(RHSExp, storeInst);	
	} else if(RBarInDemandOut){
		LLVM_DEBUG(dbgs() << "Only RBar is in demand out \n" ;);
		RDemandGen = RightDemandGen(LHSExp);	
	}
	ExpressionSet DemandGen;
	LLVM_DEBUG(dbgs() << "Value in LDGen: \n" ;);
	for(auto Exp : LDemandGen){
		print(Exp);
		LLVM_DEBUG(dbgs() << "\n" ;);
		DemandGen.insert(Exp);
	}
	for(auto Exp : RDemandGen){
		LLVM_DEBUG(dbgs() << "Value in RDGen: \n" ;);
		print(Exp);
		LLVM_DEBUG(dbgs() << "\n" ;);
		DemandGen.insert(Exp);
	}
	DemandIn[storeInst] = DemandOut[storeInst];
	if(LHSExp -> symbol == simple){
		// TODO PLEASE optimize this
		ExpressionSet tempDemand;
		for(Expression* tempExp : DemandIn[storeInst]){
			if(!isExpressionEqual(tempExp, LHSExp)){
				tempDemand.insert(tempExp);
			}
		}
		DemandIn[storeInst] = tempDemand;
		LLVM_DEBUG(dbgs() << "Value in Demand kill: \n" ;);
		print(LHSExp);
		LLVM_DEBUG(dbgs() << "\n" ;);
	}
	for(auto Exp : DemandGen){
		if(!isAlreadyInSet(DemandIn[storeInst], Exp)){
			DemandIn[storeInst].insert(Exp);		
		}
	}
	LLVM_DEBUG(dbgs() << "DemandIn: \n" ;);
	printSet(DemandIn[storeInst]);
	LLVM_DEBUG(dbgs() << "DemandOut: \n" ;);
	printSet(DemandOut[storeInst]);
}

void VFCRPass::findAlias(StoreInst* storeInst){
	LLVM_DEBUG(dbgs() << "----------------------------------------------\n" ;);
	Alias AliasGen;
	LLVM_DEBUG(dbgs() << "Running for instruction " << *storeInst << "\n";);
	// TODO: take print to llvmir++
	if(!metaMap[storeInst]){
		return;
	}
	LLVM_DEBUG(dbgs() << "Decoded instruction "; ); 
	print(metaMap[storeInst] -> LHS); 
	LLVM_DEBUG(dbgs() << " = " ;);
	print(metaMap[storeInst] -> RHS);
	LLVM_DEBUG(dbgs() << "\n";);
	// LBar and RBar set
	ExpressionSet LHSExpressions;
	ExpressionSet RHSExpressions;
	// L and R 
	Expression* LHSExp = metaMap[storeInst] -> LHS;
	Expression* RHSExp = metaMap[storeInst] -> RHS;
	// calculate ln(bar) and rn(bar)
	if(canExpressionPoint(LHSExp)){
		absName(LHSExp, LHSExpressions, storeInst);
	}
	if(canExpressionPoint(RHSExp)){
		absName(RHSExp, RHSExpressions, storeInst);
	}
	if(LHSExpressions.empty()){
		LHSExpressions.insert(LHSExp);
	}
	if(RHSExpressions.empty()){
		RHSExpressions.insert(RHSExp);
	}
	LLVM_DEBUG(dbgs() << "Values in LBar set \n";);
	printSet(LHSExpressions);	
	LLVM_DEBUG(dbgs() << "Values in RBar set \n";);
	printSet(RHSExpressions);	
	for(auto LBar : LHSExpressions){
		for(auto RBar : RHSExpressions){
			bool LBarInDemandOut = isExpInDout(LBar, storeInst);
			if(LBarInDemandOut){
				LLVM_DEBUG(dbgs() << "LBar present in demand out\n";);
			}
			bool RBarInDemandOut = isExpInDout(RBar, storeInst);
			if(RBarInDemandOut){
				LLVM_DEBUG(dbgs() << "RBar present in demand out\n";);
			}
			// TODO find a good name
			bool toughCondition = false;
			for(auto DemandExp : DemandOut[storeInst]){
				if(AliasIn.find(storeInst) != AliasIn.end() && AliasIn[storeInst].find(DemandExp) != AliasIn[storeInst].end()){
					for(auto AliasExp : AliasIn[storeInst][DemandExp]){
						if(AliasExp == DemandExp){
							toughCondition = true;
							break;
						}
					}
					if(toughCondition){
						break;
					}
				}
			}
			if(toughCondition){
				LLVM_DEBUG(dbgs() << "Third condition is true\n";);
			}
			if(LBarInDemandOut || RBarInDemandOut || toughCondition){
				Expression* tempExp = new Expression(RBar);
				if(tempExp -> symbol == address){
					tempExp -> symbol = simple;
				}
				AliasGen[LBar].insert(tempExp);
			}
		}	
	}
	LLVM_DEBUG(dbgs() << "Alias gen set \n";);
	printAliasSet(AliasGen);
	LLVM_DEBUG(dbgs() << "Alias TEST \n";);
	printAliasIn(storeInst);
	if(AliasIn.find(storeInst) != AliasIn.end()){
		AliasOut[storeInst] = AliasIn[storeInst];
	}
	if(LHSExp -> symbol == simple && RHSExp -> symbol == address){
		AliasOut[storeInst].erase(LHSExp);
	}
	AliasOut[storeInst].insert(AliasGen.begin(), AliasGen.end());
	LLVM_DEBUG(dbgs() << "Alias In \n";);
	printAliasIn(storeInst);
	LLVM_DEBUG(dbgs() << "Alias Out \n";);
	printAliasOut(storeInst);
}

// map StoreInst DemandIn
// map StoreInst DemandOut
// vector Demand 

void  VFCRPass::analyse(Instruction& I){
	LLVM_DEBUG(dbgs() << "Analysing call " << I <<  "\n";);
	Value* v = I.getOperand(0);
	LoadInst* inst = dyn_cast<LoadInst>(v);
	RHSExpression* Origin = new RHSExpression(inst -> getPointerOperand());
	StoreInst* lastStoreInst = nullptr;
	LLVM_DEBUG(dbgs() << "Origin is set to " ;);
	print(Origin);
	LLVM_DEBUG(dbgs() << "\n" ;);
	// TODO Find a better way to do this
	Instruction* LastInst = dyn_cast<Instruction>(v);
	Instruction* StartInst = &*startInstIterator;
	LLVM_DEBUG(dbgs() << "**********************************************\n" ;);
	LLVM_DEBUG(dbgs() << "Running demand loop \n";);
	LLVM_DEBUG(dbgs() << "From " << *LastInst << "\n";);
	LLVM_DEBUG(dbgs() << "To " << *StartInst << "\n";);
	while((LastInst = LastInst -> getPrevNonDebugInstruction())){
		if(StoreInst* storeInst = dyn_cast<StoreInst>(LastInst)){
			if(lastStoreInst){
//				DemandOut[storeInst].insert(DemandIn[lastStoreInst].begin(), DemandIn[lastStoreInst].end());
				DemandOut[storeInst] = DemandIn[lastStoreInst];
			} else {
				if(!isAlreadyInSet(DemandOut[storeInst], Origin)){
					DemandOut[storeInst].insert(Origin);
				}
			}
			findDemand(storeInst);
			lastStoreInst = storeInst;
		}
	}
	LLVM_DEBUG(dbgs() << "*********************************************\n" ;);
	LastInst = dyn_cast<Instruction>(v);
	StartInst = &*startInstIterator;
	LLVM_DEBUG(dbgs() << "Running alias loop \n";);
	LLVM_DEBUG(dbgs() << "From " << *StartInst << "\n";);
	LLVM_DEBUG(dbgs() << "To " << *LastInst << "\n";);
	lastStoreInst = nullptr;
	while(StartInst != LastInst){
		if(StoreInst* storeInst = dyn_cast<StoreInst>(StartInst)){
			if(lastStoreInst){
			//	AliasIn[storeInst].insert(AliasIn[lastStoreInst].begin(), AliasIn[lastStoreInst].end());
				if(AliasIn.find(storeInst) != AliasIn.end()){
					for(auto AliasMap : AliasIn[storeInst]){
						AliasIn[storeInst][AliasMap.first].insert(AliasIn[lastStoreInst][AliasMap.first].begin(), 
							AliasIn[lastStoreInst][AliasMap.first].end());
					}
				}
			}
			findAlias(storeInst);
			lastStoreInst = storeInst;
		}
		StartInst = StartInst -> getNextNonDebugInstruction();
	}
}

bool VFCRPass::isAlreadyInSet(ExpressionSet expressions, Expression* Exp){
	return expressions.find(Exp) != expressions.end();
//	for(auto E : expressions){
//		if(isExpressionEqual(E, Exp)){
//			return true;
//		}
//	}
//	return false;
}

void VFCRPass::printExpTrace(Expression* Exp){
	LLVM_DEBUG(dbgs() << "\n";);
	LLVM_DEBUG(dbgs() << "################## Expression Trace ###### " << "\n" ;);
	if(Exp -> base)
	LLVM_DEBUG(dbgs() << "#Base Instruction: " << *(Exp -> base) << "\n";);
	if(Exp -> optional)
	LLVM_DEBUG(dbgs() << "#Optional Part " << *(Exp -> optional) << "\n" ;);
	if(Exp -> type)
	LLVM_DEBUG(dbgs() << "#Type " << *(Exp -> type) << "\n" ;);
	LLVM_DEBUG(dbgs() << "#Symbol " << Exp -> symbol << "\n" ;);
	if(Exp -> functionArg)
	LLVM_DEBUG(dbgs() << "#Function Argument " << *(Exp -> functionArg) << "\n" ;);
}

void VFCRPass::printSet(ExpressionSet Expressions){
	for(auto Exp : Expressions){
		print(Exp);            
	}
	LLVM_DEBUG(dbgs() << "\n";);
}

void VFCRPass::printAliasSet(Alias AliasGen){
	for(auto AliasExp : AliasGen){
		print(AliasExp.first);
		LLVM_DEBUG(dbgs() << " : " ;);
		for(auto AliasExpGen : AliasExp.second){
			print(AliasExpGen);
			LLVM_DEBUG(dbgs() << " ";);
		}
		LLVM_DEBUG(dbgs() << "\n";);
	}
}

void VFCRPass::printAliasOut(StoreInst* storeInst){
	printAliasSet(AliasOut[storeInst]);
}

void VFCRPass::printAliasIn(StoreInst* storeInst){
	printAliasSet(AliasIn[storeInst]);
}

bool VFCRPass::isAliasEqual(Alias A, Alias B){
	if(A.empty() && B.empty()){
		return true;
	}
	for(auto alias1 : A){
		for(auto alias2 : B){
			if(isExpressionEqual(alias1.first, alias2.first)){
				for(auto exp1 : alias1.second){
					for(auto exp2 : alias2.second){
						if(!isExpressionEqual(exp1, exp2)){
							return false;
						}
						break;
					}
				}
			} else {
				return false;
			}
			break;
		}
	}
	return true;
}

bool VFCRPass::isExpInDout(Expression* Exp, StoreInst* storeInst){
	LLVM_DEBUG(dbgs() << "Is ";);
	print(Exp);
	LLVM_DEBUG(dbgs() << " in demand out? \n";);
	for(Expression* DemandExp : DemandOut[storeInst]){
		if(isExpressionEqual(Exp, DemandExp)){
			LLVM_DEBUG(dbgs() << "YES \n";);
			return true;
		}
	}
	LLVM_DEBUG(dbgs() << "NO \n";);
	return false;
}

ExpressionSet VFCRPass::findKill(Expression* Exp){
	ExpressionSet expressions;
	if(Exp -> symbol == simple){
		expressions.insert(Exp);
	}
	return expressions;
}

ExpressionSet VFCRPass::RightDemandGen(Expression* LHSExp){
	ExpressionSet expressions;
	if(canExpressionPoint(LHSExp)){
		Expression* SimpleLHSExpression = new Expression(LHSExp);
		SimpleLHSExpression -> symbol = simple;
		SimpleLHSExpression -> optional = nullptr;
		SimpleLHSExpression -> RHSisAddress = false;
		expressions.insert(SimpleLHSExpression);
	}
	Expression* AddrExp = new Expression(LHSExp);
	AddrExp -> RHSisAddress = true;
	AddrExp -> symbol = address;
	if(isAddressTaken(AddrExp)){
		expressions.insert(AddrExp);
	}
	return expressions;
}

ExpressionSet VFCRPass::LeftDemandGen(Expression* RHSExp,StoreInst* Inst){
	ExpressionSet expressions;
	if(canExpressionPoint(RHSExp)){
		LLVM_DEBUG(dbgs() << "Expression if of type *x or x -> f \n";);
		Expression* VarRHSExp = new Expression(RHSExp);
		VarRHSExp -> symbol = simple;
		VarRHSExp -> optional = nullptr;
		VarRHSExp -> RHSisAddress = false;
		expressions.insert(VarRHSExp);
		Expression* AddrRHSExp = new Expression(VarRHSExp);
		AddrRHSExp -> RHSisAddress = true;
		AddrRHSExp -> symbol = address;
		if(isAddressTaken(AddrRHSExp)){
			expressions.insert(AddrRHSExp);
		}
		absName(RHSExp, expressions, Inst);
	} else if(RHSExp -> symbol == address){
		LLVM_DEBUG(dbgs() << "Expression of type &x \n" ;);
		Expression* SimpleRHSExp = new Expression(RHSExp);
		expressions.insert(SimpleRHSExp);
	} else if(RHSExp -> symbol == simple || RHSExp -> symbol == dot){
		LLVM_DEBUG(dbgs() << "Expression of type x and x.f \n" ;);
		expressions.insert(RHSExp);
		if(canExpressionPoint(RHSExp)){
			absName(RHSExp, expressions, Inst);
		}
		Expression* AddrRHSExp = new Expression(RHSExp);
		AddrRHSExp -> RHSisAddress = true;
		AddrRHSExp -> symbol = address;
		if(isAddressTaken(AddrRHSExp)){
			expressions.insert(AddrRHSExp);
		}
	}
	return expressions;
}

bool VFCRPass::isAddressTaken(Expression* Exp){
	// TODO
	return false;
}

bool VFCRPass::expressionSetInDemandOut(ExpressionSet Expressions, StoreInst* Inst){
	for(auto Exp : Expressions){
		for(auto DemandExp : DemandOut[Inst]){
			if(isExpressionEqual(Exp, DemandExp)){
				return true;
			}
		}
	}
	return false;
}

bool VFCRPass::isExpressionEqual(Expression* exp1, Expression* exp2){
	if(exp1 -> base != exp2 -> base){
		return false;
	}
	if(exp1 -> type != exp2 -> type){
		return false;
	}
	if(exp1 -> symbol != exp2 -> symbol){
		return false;
	}
	if(exp1 -> functionArg != exp2 -> functionArg){
		return false;
	}
	if(exp1 -> RHSisAddress != exp2 -> RHSisAddress){
		return false;
	}
	if(exp1 -> optional != exp2 -> optional){
		return false;
	}
	return true;
}

bool VFCRPass::canExpressionPoint(Expression* Exp){
	LLVM_DEBUG(dbgs() << "Is ";);
	print(Exp);
	LLVM_DEBUG(dbgs() << " of type x -> f or x* ? \n" ;);
	SymbolType ExpSymbol;
	ExpSymbol = Exp -> symbol;
	if(ExpSymbol == pointer || ExpSymbol == arrow){
		LLVM_DEBUG(dbgs() << "YES\n" ;);
		return true;
	}
	LLVM_DEBUG(dbgs() << "NO\n" ;);
	return false;
}
void VFCRPass::absName(Expression* Exp, ExpressionSet& expressions, StoreInst* StoreInstruction){
	SymbolType ExpSymbol;
	ExpSymbol = Exp -> symbol;
	if(AliasIn.find(StoreInstruction) != AliasIn.end() && AliasIn[StoreInstruction].find(Exp) != AliasIn[StoreInstruction].end()){
		for(Expression* AliasExpression : AliasIn[StoreInstruction][Exp]){
			if(!AliasExpression){
				continue;
			}
			SymbolType AliasExpSymbol;
			AliasExpSymbol = AliasExpression -> symbol;
			Expression *AliasExp = nullptr;
			if(ExpSymbol == pointer){
				AliasExp = new Expression(AliasExpression);
				AliasExp -> base = Exp -> base;
				AliasExp -> type = Exp -> type;
				AliasExp -> symbol = simple;
			} else if(ExpSymbol == arrow){
				AliasExp = new Expression(AliasExpression);
				AliasExp -> base = Exp -> base;
				AliasExp -> type = Exp -> type;
				AliasExp -> symbol = dot;
			}	
			if(AliasExp){
				expressions.insert(AliasExp);
			} else {
				expressions.insert(Exp);
			}
		}
	}
	return;
}

void VFCRPass::print(Expression* L) {
	if(L == nullptr){
		return;
	}
	// prints the expression in formal LHS = RHS
	if (L->symbol == constant) {
		LLVM_DEBUG(dbgs() << "constant";);
		return;
	}
	if (L -> symbol == address){
		LLVM_DEBUG(dbgs() << " (&) " ;);
	}
	if (L->type) {
		LLVM_DEBUG(dbgs() << " [ " << *(L->type) << " ] "
				  << " ";);
	}
	if (L->symbol == pointer) {
		LLVM_DEBUG(dbgs() << "*";);
	}
	if (L->base) {
		LLVM_DEBUG(dbgs() << L->base->getName() << " ";);
	} else if (L->functionArg) {
		LLVM_DEBUG(dbgs() << L->functionArg->getName() << " ";);
	}
	if (L->symbol == arrow) {
		LLVM_DEBUG(dbgs() << " -> ";);
	}
	if (L->symbol == dot) {
		LLVM_DEBUG(dbgs() << " . ";);
	}
	if (L->optional) {
		LLVM_DEBUG(dbgs() << L->optional->getName(););
	}
}
}  // namespace

char VFCRPass::ID = 1;
static RegisterPass<VFCRPass> X(
    "vfcr",					     // the option name -> -mba
    "Virtual Function Call resolution",  // option description
    true,  // true as we don't modify the CFG
    true   // true if we're writing an analysis
);
/*
static void registerVFCRPass(const PassManagerBuilder &,
			     legacy::PassManagerBase &PM) {
	PM.add(new VFCRPass());
}
static RegisterStandardPasses RegisterMyPass(
    PassManagerBuilder::EP_EarlyAsPossible, registerVFCRPass);
*/
