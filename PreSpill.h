#ifndef LLVM_CODEGEN_PRESPILL_H
#include "AllocationOrder.h"
#include "InterferenceCache.h"
#include "LiveDebugVariables.h"


#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/IndexedMap.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/LiveInterval.h"
#include "llvm/CodeGen/LiveRangeEdit.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineBlockFrequencyInfo.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/RegisterClassInfo.h"
#include "llvm/CodeGen/VirtRegMap.h"
#include "llvm/Pass.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "SplitKit.h"
#include "SpillPlacement.h"
#include "Spiller.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/MCContext.h"
#include "llvm/CodeGen/MachineSSAUpdater.h"
#include "llvm/CodeGen/TailDuplicator.h"

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <map>
#include <iterator>
#include <memory>
#include <queue>
#include <tuple>
#include <utility>
#include <iostream>

namespace llvm {
#define USES_INFINITY  10000000
class Function;
class TargetMachine;


	template<typename T>
	bool noDublicate(std::vector<T> v, T check) {
		for (auto x : v) {
			if (check == x) return false;
		}
		return true;
	}

	template<typename T>
	bool isElem(std::vector<T> vec, T check) {
		for (auto elem : vec) {
			if (check == elem) {
				return true;
			}
		}
		return false;
	}

	template<typename T>
	void without(std::vector<T> vec, T cand) {
		std::vector<unsigned> tmp;
		for (unsigned i = 0; i < vec.size(); i++) {
			if (vec[i] == cand) {
				vec.erase(vec.begin() + i);
				break;
			}
		}
	}

	template<typename T>
	std::vector<T> without(std::vector<T> vec1, std::vector<T> vec2) {
		std::vector<unsigned> tmp;
		unsigned help = 0;
		for (unsigned i = 0; i < vec1.size();i++) {
			for(unsigned j  =0; j < vec2.size(); j++){
				if(vec1[i] == vec2[j]){
					help++;
				}
			}
			if(!help) {
				tmp.push_back(vec1[i]);
			}
			help =0;
		}
		return tmp;
	}

	template<typename T>
	std::vector<T> unionVec(std::vector<T> vec1, std::vector<T> vec2) {
		std::vector<T> result (vec1);
		for (auto x : vec2) {
			if (!isElem(result, x)) {
				result.push_back(x);
			}
		}
		return result;
	}

	template<typename T>
	std::vector<T> intersecVec(std::vector<T> vec1, std::vector<T> vec2) {
		std::vector<T> result;
		for (auto x : vec2) {
			if (isElem(vec1, x)) {
				if(noDublicate(result, x))
				result.push_back(x);
			}
		}
		return result;
	}

class PreSpill : public MachineFunctionPass {

public:
	static char ID;

	PreSpill() : MachineFunctionPass(ID) {
	}
	void connectAllMBBs();
	bool runOnMachineFunction(MachineFunction &mf) override;

	void getAnalysisUsage(AnalysisUsage &AU) const override {
		AU.setPreservesCFG();
		AU.addRequired<AAResultsWrapperPass>();
		AU.addPreserved<AAResultsWrapperPass>();
		AU.addRequired<LiveIntervals>();
		AU.addPreserved<LiveIntervals>();
		AU.addRequired<LiveStacks>();
		AU.addPreserved<LiveStacks>();
		AU.addPreserved<SlotIndexes>();
		AU.addRequiredID(MachineDominatorsID);
		AU.addPreservedID(MachineDominatorsID);
		AU.addRequired<MachineBlockFrequencyInfo>();
		AU.addPreserved<MachineBlockFrequencyInfo>();
		AU.addRequired<MachineLoopInfo>();
		AU.addPreserved<MachineLoopInfo>();
		AU.addRequired<VirtRegMap>();
		AU.addPreserved<VirtRegMap>();
		AU.addRequired<LiveRegMatrix>();
		AU.addPreserved<LiveRegMatrix>();
		MachineFunctionPass::getAnalysisUsage(AU);
	}

private:
};

static RegisterPass<PreSpill> X("preSpill", "Pre Spill Pass",
                                false /* Only looks at CFG */,
                                false /* Analysis Pass */);

} // end namespace llvm

#endif // LLVM_CODEGEN_PRESPILL_H
