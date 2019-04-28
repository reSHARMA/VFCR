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


enum analysisType {intraprocedural, interprocedural};

using ExpressionSet = std::unordered_set<Expression*, std::hash<Expression*>, Expression::ExpEqual>;
using ExpressionMap = std::map<Node*, ExpressionSet>;
using Alias = std::map<Expression*, ExpressionSet>;
using AliasExpressionMap = std::map<Node*, Alias>;

class VFCRPass : public ModulePass {
       private:
	FunctionToCFG	GRCfg;
	ExpressionMap DemandIn, DemandOut;
	AliasExpressionMap AliasIn, AliasOut;
	analysisType analysis; 
       public:
	static char ID;
	VFCRPass() : ModulePass(ID) {}
	void print(Expression*);
	void print(Node*);
	bool canExpressionPoint(Expression*);
	void absName(Expression*, ExpressionSet&, Node*);
	bool expressionSetInDemandOut(ExpressionSet, Node*);
	bool isExpressionEqual(Expression*, Expression*);
	ExpressionSet LeftDemandGen(Expression*, Node*);
	bool isAddressTaken(Expression*);
	ExpressionSet findKill(Expression*);
	ExpressionSet RightDemandGen(Expression*);
	bool isExpInDout(Expression*, Node*);
	void printAliasIn(Node*);
	void printAliasOut(Node*);
	void printAliasSet(Alias);
	void printSet(ExpressionSet);
	void printExpTrace(Expression*);
	bool isAlreadyInSet(ExpressionSet, Expression*);
	void findDemand(Node*);
	void findAlias(Node*);
	bool isAliasEqual(Alias, Alias);

	bool runOnModule(Module& M) override {
		analysis = intraprocedural;
		GRCfg  = getAnalysis<LLVMIRPlusPlusPass>().getCFG();
		for(Function &F : M){
			NodeList DemandWorkList, AliasWorkList;
			// Get CFG from analysis 
			Function *func = &F;
			CFG* funcCFG = nullptr;
			if(GRCfg.find(func) != GRCfg.end()){
				funcCFG = GRCfg[func];
			}
			if(!funcCFG){
				continue;
			}
			// Handle intrinsic and empty functions
			if(!(funcCFG -> getStartNode())){
				continue;
			}
			// Find virtual function call and generate demand for it's static callee
			Expression* Origin = nullptr;
			Node* VirtCallNode = nullptr;
			NodeList WorkList;
			WorkList.push_back(funcCFG -> getStartNode());
			Node* startNode = funcCFG -> getStartNode();
			while(!WorkList.empty()){
				Node* node = WorkList.back();
				WorkList.pop_back();
				print(node);
				if(node && node -> abstractedInto == call && node -> callType == virt){
					Origin = node -> Callee;
					VirtCallNode = node;
					break;
				}
				for(Node* s : node -> getSucc()){
					WorkList.push_back(s);
				}
			}
			WorkList.clear();
			// Initialize worklists and demands
			if(VirtCallNode){
				LLVM_DEBUG(dbgs() << "Found a virtual call \n";);
				DemandWorkList.push_back(VirtCallNode);
				DemandOut[VirtCallNode].insert(Origin);
				AliasWorkList.push_back(funcCFG -> getEndNode());
			}
 			while(!(DemandWorkList.empty() && AliasWorkList.empty())){
				LLVM_DEBUG(dbgs() << "Demand or Alias worklist is not empty \n";);
				while(!DemandWorkList.empty()){
					LLVM_DEBUG(dbgs() << "Demand worklist is not empty \n";);
					Node* node = DemandWorkList.back();
					DemandWorkList.pop_back();
					ExpressionSet OldDemandIn = DemandIn[node];
					// Calc stuff
					findDemand(node);
					if(OldDemandIn != DemandIn[node]){
						for(Node* s : node -> getPred()){
							LLVM_DEBUG(dbgs() << "Add ";);
							print(s);
							LLVM_DEBUG(dbgs() << " to the demand worklist \n";);
							DemandWorkList.push_back(s);
							AliasWorkList.push_back(s);
						}
					}
				}
				while(!AliasWorkList.empty()){
					LLVM_DEBUG(dbgs() << "Alias worklist is not empty \n";);
					Node* node = AliasWorkList.back();
					AliasWorkList.pop_back();
					Alias OldAliasOut = AliasOut[node];
					// Calc stuff
					findAlias(node);
					if(OldAliasOut != AliasOut[node]){
						for(Node* s : node -> getSucc()){
							LLVM_DEBUG(dbgs() << "Add ";);
							print(s);
							LLVM_DEBUG(dbgs() << " to the alias worklist \n";);
							DemandWorkList.push_back(s);
							AliasWorkList.push_back(s);
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

void VFCRPass::findDemand(Node* node){
	if(node -> abstractedInto == call){
		if(analysis == intraprocedural){
			DemandOut[node] = DemandIn[node];
			AliasIn[node] = AliasOut[node];
		} else if(analysis == interprocedural){
		
		}	
	} else if(node -> abstractedInto == update){	
	 	LLVM_DEBUG(dbgs() << "Working on node " ;);
		print(node);

		// Meet of all successors
		for(Node* s : node -> getSucc()){
			for(Expression* Exp : DemandIn[s]){
				DemandOut[node].insert(Exp);
			}
		}
		
		Expression* LHSExp = node -> LHS;
		Expression* RHSExp = node -> RHS;

		LLVM_DEBUG(dbgs() << "Value of LHS \n";);
		print(LHSExp);
		LLVM_DEBUG(dbgs() << "\n Value of RHS \n";);
		print(RHSExp);
		LLVM_DEBUG(dbgs() << "\n";);

		ExpressionSet LHSExpressions;
		ExpressionSet RHSExpressions;

		absName(LHSExp, LHSExpressions, node);
		absName(RHSExp, RHSExpressions, node);

		LLVM_DEBUG(dbgs() << "Values in LBar set \n";);
		printSet(LHSExpressions);
		LLVM_DEBUG(dbgs() << "Values in RBar set \n";);
		printSet(RHSExpressions);

		// calculate demand gen
		bool LBarInDemandOut = expressionSetInDemandOut(LHSExpressions, node);		
		bool RBarInDemandOut = expressionSetInDemandOut(RHSExpressions, node);

		ExpressionSet LDemandGen;
		ExpressionSet RDemandGen;
		if(LBarInDemandOut && RBarInDemandOut){
			LLVM_DEBUG(dbgs() << "LBar and RBar both are in demand out \n" ;);
			LDemandGen = LeftDemandGen(RHSExp, node);
			RDemandGen = RightDemandGen(LHSExp);
		} else if(LBarInDemandOut){
			LLVM_DEBUG(dbgs() << "Only LBar is in demand out \n" ;);
			LLVM_DEBUG(dbgs() << "Running LDGen over RHSExp \n" ;);
			LDemandGen = LeftDemandGen(RHSExp, node);	
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

		DemandIn[node] = DemandOut[node];
		if(LHSExp -> symbol == simple){
			// TODO PLEASE optimize this
			ExpressionSet tempDemand;
			for(Expression* tempExp : DemandIn[node]){
				if(!isExpressionEqual(tempExp, LHSExp)){
					tempDemand.insert(tempExp);
				}
			}
			DemandIn[node] = tempDemand;
			LLVM_DEBUG(dbgs() << "Value in Demand kill: \n" ;);
			print(LHSExp);
			LLVM_DEBUG(dbgs() << "\n" ;);
		}
		for(auto Exp : DemandGen){
			if(!isAlreadyInSet(DemandIn[node], Exp)){
				DemandIn[node].insert(Exp);		
			}
		}
		LLVM_DEBUG(dbgs() << "DemandIn: \n" ;);
		printSet(DemandIn[node]);
		LLVM_DEBUG(dbgs() << "DemandOut: \n" ;);
		printSet(DemandOut[node]);

	}
}

void VFCRPass::absName(Expression* Exp, ExpressionSet& expressions, Node* node){
	SymbolType ExpSymbol;
	ExpSymbol = Exp -> symbol;
	if(AliasIn.find(node) != AliasIn.end() && AliasIn[node].find(Exp) != AliasIn[node].end()){
		for(Expression* AliasExpression : AliasIn[node][Exp]){
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
	if(expressions.size() == 0){
		expressions.insert(Exp);
	}
	return;
}

bool VFCRPass::expressionSetInDemandOut(ExpressionSet Expressions, Node* node){
	for(auto Exp : Expressions){
		for(auto DemandExp : DemandOut[node]){
			if(isExpressionEqual(Exp, DemandExp)){
				return true;
			}
		}
	}
	return false;
}

ExpressionSet VFCRPass::LeftDemandGen(Expression* RHSExp,Node *node){
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
		absName(RHSExp, expressions, node);
	} else if(RHSExp -> symbol == address){
		LLVM_DEBUG(dbgs() << "Expression of type &x \n" ;);
		Expression* SimpleRHSExp = new Expression(RHSExp);
		expressions.insert(SimpleRHSExp);
	} else if(RHSExp -> symbol == simple || RHSExp -> symbol == dot){
		LLVM_DEBUG(dbgs() << "Expression of type x and x.f \n" ;);
		expressions.insert(RHSExp);
		if(canExpressionPoint(RHSExp)){
			absName(RHSExp, expressions, node);
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

void VFCRPass::findAlias(Node* node){
	LLVM_DEBUG(dbgs() << "----------------------------------------------\n" ;);
	Alias AliasGen;
	LLVM_DEBUG(dbgs() << "Running for instruction ";);
	print(node);
	// TODO: take print to llvmir++
	// LBar and RBar set
	ExpressionSet LHSExpressions;
	ExpressionSet RHSExpressions;
	// L and R 
	Expression* LHSExp = node -> LHS;
	Expression* RHSExp = node -> RHS;
	// calculate ln(bar) and rn(bar)
	if(canExpressionPoint(LHSExp)){
		absName(LHSExp, LHSExpressions, node);
	}
	if(canExpressionPoint(RHSExp)){
		absName(RHSExp, RHSExpressions, node);
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
			bool LBarInDemandOut = isExpInDout(LBar, node);
			if(LBarInDemandOut){
				LLVM_DEBUG(dbgs() << "LBar present in demand out\n";);
			}
			bool RBarInDemandOut = isExpInDout(RBar, node);
			if(RBarInDemandOut){
				LLVM_DEBUG(dbgs() << "RBar present in demand out\n";);
			}
			// TODO find a good name
			bool toughCondition = false;
			for(auto DemandExp : DemandOut[node]){
				if(AliasIn.find(node) != AliasIn.end() && AliasIn[node].find(DemandExp) != AliasIn[node].end()){
					for(auto AliasExp : AliasIn[node][DemandExp]){
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
	printAliasIn(node);

	// Find meet of all predecessors
	// TODO

	if(AliasIn.find(node) != AliasIn.end()){
		AliasOut[node] = AliasIn[node];
	}
	if(LHSExp -> symbol == simple && RHSExp -> symbol == address){
		AliasOut[node].erase(LHSExp);
	}
	AliasOut[node].insert(AliasGen.begin(), AliasGen.end());
	LLVM_DEBUG(dbgs() << "Alias In \n";);
	printAliasIn(node);
	LLVM_DEBUG(dbgs() << "Alias Out \n";);
	printAliasOut(node);
}

bool VFCRPass::isAlreadyInSet(ExpressionSet expressions, Expression* Exp){
	return expressions.find(Exp) != expressions.end();
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


void VFCRPass::printAliasOut(Node* node){
	printAliasSet(AliasOut[node]);
}

void VFCRPass::printAliasIn(Node* node){
	printAliasSet(AliasIn[node]);
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

bool VFCRPass::isExpInDout(Expression* Exp, Node* node){
	LLVM_DEBUG(dbgs() << "Is ";);
	print(Exp);
	LLVM_DEBUG(dbgs() << " in demand out? \n";);
	for(Expression* DemandExp : DemandOut[node]){
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


bool VFCRPass::isAddressTaken(Expression* Exp){
	// TODO
	return false;
}



void VFCRPass::print(Node* node){
	if(node -> abstractedInto == update){
		print(node -> LHS);
		LLVM_DEBUG(dbgs() << " = ";);
		print(node -> RHS);
		LLVM_DEBUG(dbgs() << "\n";);
	} else if(node -> abstractedInto == call){
		LLVM_DEBUG(dbgs() << "Call \n";);	
	}
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
