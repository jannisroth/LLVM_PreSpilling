#include <llvm/Target/TargetInstrInfo.h>
#include "PreSpill.h"

using namespace llvm;

//MYTRY
#define DEBUG_TYPE "preSpill"
INITIALIZE_PASS_BEGIN(PreSpill, "preSpill", "pre spilling before register allocation", false, false)
//INITIALIZE_PASS_BEGIN(RABasic, "regallocbasic", "Basic Register Allocator",false, false)
	INITIALIZE_PASS_DEPENDENCY(LiveDebugVariables)
	INITIALIZE_PASS_DEPENDENCY(SlotIndexes)
	INITIALIZE_PASS_DEPENDENCY(LiveIntervals)
	INITIALIZE_PASS_DEPENDENCY(RegisterCoalescer)
	INITIALIZE_PASS_DEPENDENCY(MachineScheduler)
	INITIALIZE_PASS_DEPENDENCY(LiveStacks)
	INITIALIZE_PASS_DEPENDENCY(MachineDominatorTree)
	INITIALIZE_PASS_DEPENDENCY(MachineLoopInfo)
	INITIALIZE_PASS_DEPENDENCY(VirtRegMap)
	INITIALIZE_PASS_DEPENDENCY(LiveRegMatrix)
INITIALIZE_PASS_END(PreSpill, "preSpill", "pre spilling before register allocation", false,
                    false)

#define endl '\n';

MachineFunctionProperties getRequiredProperties() {
	return MachineFunctionProperties().set(
			MachineFunctionProperties::Property::NoPHIs);
}

unsigned numOfSpills =0;
unsigned numOfReloads = 0;
unsigned numOfReloadsInLoop = 0;
unsigned numOfSpillsinLoop = 0;

char PreSpill::ID = 0;

unsigned didSpill = 0;
unsigned didReload = 0;
MachineFunction *MF;
MachineRegisterInfo *MRI;
const TargetRegisterInfo *TRI;
VirtRegMap *VRM;
LiveIntervals *LIS;
LiveRegMatrix *Matrix;
MachineLoopInfo *Loops;
const TargetInstrInfo *TII;
MachineInstrBuilder MIB;
std::unique_ptr<SplitAnalysis> SA;
RegisterClassInfo RegClassInfo;
SlotIndex min_slotIndex;
unsigned N = 100000;
unsigned pow231;
unsigned numberOfBBs;
unsigned numberOFVirtRegs;
unsigned numberofAvailableRegclasses;
unsigned currRegClassIdx;
unsigned k = 0;
unsigned kwithoutDefs = 0;
unsigned countFunctions = 0;

enum UseOrDef {
	GETUSE,
	GETDEF,
	BOTH
};

typedef struct machineBasicBlockInfo {
	MachineBasicBlock *mbb;
	bool isLoopHeader;
	unsigned isLoopExit;
	unsigned isLoopExiting;
} MachineBasicBlockInfo;

typedef struct edge{
	MachineBasicBlock* from;
	MachineBasicBlock* to;
	unsigned number;
} edge;
bool operator==(edge e1, edge e2){
	return e1.from->getNumber() == e2.from->getNumber() && e1.to->getNumber() == e2.to->getNumber();
}


std::unordered_map<unsigned , MachineBasicBlock*> alreadySplit;
//defUseChain[virtreg][idx]
std::vector<std::vector<SlotIndex >> defUseChain;
std::vector<unsigned > stillLive;
//w[block][idx]
std::vector<std::vector<unsigned> > w;
//s[block][idx]
std::vector<std::vector<unsigned> > s;
//cans[idx]
std::vector<unsigned> cand;
//take[idx]
std::vector<unsigned> take;
std::vector<MachineBasicBlock *> postOrder;
std::vector<MachineBasicBlock *> reversePostOrder;
std::vector<MachineBasicBlock *> visit;
std::vector<unsigned> visited;
//indicate the loop header of curr loop
std::vector<MachineBasicBlock*> loop_begin_spill;
//variables live through the loop of loop_begin_spill
std::vector<std::vector<unsigned >> liveThrough_loopdepth;
//next_instruction_use_maps[block][virtReg][number of use]
//std::vector<std::vector<std::vector<unsigned> > > next_instruction_use_maps;
std::vector<std::unordered_map<unsigned , std::vector<unsigned >>> next_instruction_use_maps;
//virtregsInInstructions[inst*]
std::unordered_map<MachineInstr*, std::vector<unsigned > > virtregsInInstructions;
//virtRegToDef[VIrtreg]
std::vector<unsigned> virtRegToDef;
//loopExits_atinstructionNr[idx]
std::vector<std::pair<MachineBasicBlock *, unsigned> > loopExits_atinstructionNr;
//registerClassOfVirtreg[virtReg]
std::vector<const TargetRegisterClass* > registerClassOfVirtreg;
//registerClassAvailable[idx], idx < |avaiable Regclasses|
std::vector<unsigned > registerClassAvailable;
//reloads_withRegClass[regclass][edgeNr][idx]
std::vector<std::unordered_map<unsigned , std::vector<unsigned > > > reloads_withRegClass;
//spill_withRegClass[regclass][edgeNr][idx]
std::vector<std::unordered_map<unsigned , std::vector<unsigned > > > spill_withRegClass;
//vregSpilledAT[vreg] = (number ob bb, offset)
std::vector<std::pair<unsigned ,unsigned >> vregSpilledAt;
//idxToMachineInstr[idx]
std::vector<MachineInstr* > idxToMachineInstr;
//map newVregs to old ones
std::unordered_map<unsigned , unsigned > mapNewVregsToOld;
//map phi-vreg to reload
std::unordered_map<unsigned ,MachineInstr*> mapPhiToReload;
//map phi-vreg to spill
std::unordered_map<unsigned , MachineInstr*> mapPhiToSpill;
//edge_mapping[idx]
std::vector<edge> edge_mapping;
//edge_matrix[block][succ]
std::vector<std::vector<unsigned >> edge_Matrix;
//blocksInformation[blockNumber]
std::vector<MachineBasicBlockInfo> blocksInformation;

//maxRegisterPressurePerBlock_withRegClass[regClass][block number]
std::vector<std::vector<unsigned> >maxRegisterPressurePerBlock_withRegClass;
//Next Use Maps
//nextUseMaps[regclass][block][virtreg]
//std::vector<std::vector<std::vector<unsigned> > > nextUseMapsEntry_withRegClass;
std::vector<std::vector<std::unordered_map<unsigned , unsigned > > > nextUseMapsEntry_withRegClass;
//std::vector<std::vector<std::vector<unsigned> > > nextUseMapsExit_withRegClass;
std::vector<std::vector<std::unordered_map<unsigned , unsigned > > > nextUseMapsExit_withRegClass;


unsigned getDistanceFromSlotIndex(SlotIndex idx) {
	if (min_slotIndex > idx) {
		return 0;
	}
	return (unsigned) min_slotIndex.distance(idx) / 16;
}

//get the next use distance of v from instruction inst
unsigned getNextUseDistance(int number, unsigned v, MachineInstr* inst){
	if(!inst){
		errs() << "inst was null!\n";
	}
	if(!inst->isDebugValue())
		if(LIS->getInterval(v+pow231).isLiveAtIndexes(ArrayRef<SlotIndex>(LIS->getInstructionIndex(*inst))) || LIS->getInterval(v+pow231).getValNumInfo(0)->def.getBaseIndex() == LIS->getInstructionIndex(*inst).getBaseIndex()){
			if(next_instruction_use_maps[number].find(v) == next_instruction_use_maps[number].end()) {
				if(nextUseMapsEntry_withRegClass[currRegClassIdx][number].find(v) != nextUseMapsEntry_withRegClass[currRegClassIdx][number].end()){
					if(MF->getBlockNumbered(number)->size()  == 0){
						return nextUseMapsEntry_withRegClass[currRegClassIdx][number][v];
					}
					if( getDistanceFromSlotIndex(LIS->getInstructionIndex(*inst)) - getDistanceFromSlotIndex(LIS->getInstructionIndex(MF->getBlockNumbered(number)->front())) > nextUseMapsEntry_withRegClass[currRegClassIdx][number][v]){
						errs() << "how is this larger?" <<endl;
					}
					return nextUseMapsEntry_withRegClass[currRegClassIdx][number][v] + getDistanceFromSlotIndex(LIS->getInstructionIndex(MF->getBlockNumbered(number)->front())) - getDistanceFromSlotIndex(LIS->getInstructionIndex(*inst)) - 1;
				}else if (nextUseMapsExit_withRegClass[currRegClassIdx][number][v] < USES_INFINITY - 1/*LIS->isLiveOutOfMBB(LIS->getInterval(v+pow231), MF->getBlockNumbered(number))*/){
					return nextUseMapsExit_withRegClass[currRegClassIdx][number][v] + getDistanceFromSlotIndex(LIS->getInstructionIndex(*inst)) - getDistanceFromSlotIndex(LIS->getInstructionIndex(MF->getBlockNumbered(number)->front())) + 1;
				} else {
					return USES_INFINITY;
				}
			}else{
				unsigned inst_distance = getDistanceFromSlotIndex(LIS->getInstructionIndex(*inst));
				for (unsigned i = 0; i < next_instruction_use_maps[number][v].size(); i++) {
					if (next_instruction_use_maps[number][v][i] > inst_distance) {
						return next_instruction_use_maps[number][v][i] - inst_distance - 1;
					}
				}
				if(nextUseMapsExit_withRegClass[currRegClassIdx][number][v] < USES_INFINITY - 1){
					return nextUseMapsExit_withRegClass[currRegClassIdx][number][v] >= USES_INFINITY - 1? USES_INFINITY : nextUseMapsExit_withRegClass[currRegClassIdx][number][v] + getDistanceFromSlotIndex(LIS->getInstructionIndex(MF->getBlockNumbered(number)->back())) - inst_distance;
				}
				return USES_INFINITY;
			}

		}else{
			return USES_INFINITY;
		}
}

unsigned getNextUseDistance(int number, unsigned v, MachineInstr* inst, bool loop){
	if(loop){
		unsigned nud = getNextUseDistance( number, v, inst);
		return  nud == USES_INFINITY? USES_INFINITY : nud + N*liveThrough_loopdepth.size();
	}else{
		return getNextUseDistance( number, v, inst);
	}
}

//------compare function---------
auto curr_mbb = (unsigned) -1;
bool loopLiveThrough = false;
MachineInstr *curr_inst = nullptr;
bool helpCompare(unsigned i, unsigned j) {
	return getNextUseDistance(curr_mbb,i, curr_inst,loopLiveThrough) < getNextUseDistance(curr_mbb,j, curr_inst,loopLiveThrough);
}

bool (*compareNextUseDistances(MachineInstr *inst, MachineBasicBlock *mbb, bool loop = false))(unsigned i, unsigned j) {
	curr_mbb = (unsigned) (inst ? inst->getParent() : mbb)->getNumber();
	if(inst){
		curr_inst = inst;
	}else{
		if(!mbb->empty())
			curr_inst = &mbb->front();
	}
	loopLiveThrough = loop;
	return helpCompare;
}
//---------------------------------


//-----initialize next use maps--------
void initSlotIndex() {
	for(unsigned i = 0; i < numberOfBBs; i++){
		std::vector<unsigned > tmp;
		edge_Matrix.push_back(tmp);
		for(unsigned j = 0; j < numberOfBBs; j++){
			edge_Matrix[i].push_back(0);
		}
	}

	int count = 0;
	int edgeCount = 0;
	int c = 0;
	for (auto &i : *MF) {
		for (auto &j : i) {
			if(j.isDebugValue()){
				continue;
			}
			idxToMachineInstr.push_back(nullptr);
			SlotIndex slotidx = LIS->getInstructionIndex(j);
			if (min_slotIndex) {
				min_slotIndex = min_slotIndex < slotidx ? min_slotIndex : slotidx;
			} else {
				min_slotIndex = slotidx;
			}
			c++;
		}
		count++;
		//initialise edge_mapping
		for(auto succ : i.successors()){
			edge e{&i,succ,edgeCount};
			if(noDublicate(edge_mapping, e)) {
				edge_Matrix[i.getNumber()][succ->getNumber()] = edgeCount;
				edge_mapping.push_back(e);
				edgeCount++;
			}
		}
	}
	for (auto &i : *MF) {
		for (auto &j : i) {
			if(j.isDebugValue()){
				continue;
			}
			idxToMachineInstr[getDistanceFromSlotIndex(LIS->getInstructionIndex(j))];
		}
	}

}

void initNextUseMaps() {
	for(unsigned i = 0; i < registerClassAvailable.size(); i++) {
		std::vector<std::unordered_map<unsigned, unsigned > > nextUseMapsEn;
		std::vector<std::unordered_map<unsigned, unsigned > > nextUseMapsEx;

		for (unsigned l = 0; l < numberOfBBs; ++l) {
			std::unordered_map<unsigned ,unsigned> nextUseEntry;
			std::unordered_map<unsigned ,unsigned> nextUseExit;
			nextUseMapsEn.push_back(nextUseEntry);
			nextUseMapsEx.push_back(nextUseExit);
		}
		nextUseMapsEntry_withRegClass.push_back(nextUseMapsEn);
		nextUseMapsExit_withRegClass.push_back(nextUseMapsEx);
	}
	for(unsigned i = 0; i < registerClassAvailable.size(); i++){
		std::vector<unsigned > tmp2;
		maxRegisterPressurePerBlock_withRegClass.push_back(tmp2);
	}
	for (auto &mb : *MF) {
		MachineBasicBlockInfo tmp = {.mbb = &mb, .isLoopHeader = Loops->isLoopHeader(&mb),};
		blocksInformation.push_back(tmp);
		for(unsigned i = 0; i < registerClassAvailable.size(); i++){
			maxRegisterPressurePerBlock_withRegClass[i].push_back(0);
		}
	}
	for (auto le : loopExits_atinstructionNr) {
		blocksInformation[le.first->getNumber()].isLoopExit++;
	}
	SmallVector<MachineBasicBlock *, 8> mbbs;
	for (auto loop : *Loops) {
		loop->getExitingBlocks(mbbs);
		for (auto bb : mbbs) {
			blocksInformation[bb->getNumber()].isLoopExiting++;
		}
	}
}

void initInstructionDistances(){
	for (unsigned i = 0; i < numberOfBBs; ++i) {
		std::unordered_map<unsigned,std::vector<unsigned> > tmp_i;
		next_instruction_use_maps.push_back(tmp_i);
	}
}

void initLoopExits() {
	for (auto loop : *Loops) {
		SmallVector<MachineBasicBlock *, 4> mbbs;
		loop->getExitBlocks(mbbs);
		MachineBasicBlock *mbb;
		if (mbbs.size() > 1) {
			for (auto block : mbbs) {
				loopExits_atinstructionNr.emplace_back(block, getDistanceFromSlotIndex(LIS->getInstructionIndex(block->front())));
			}
		} else {
			mbb = mbbs.front();
			loopExits_atinstructionNr.emplace_back(mbb, getDistanceFromSlotIndex(LIS->getInstructionIndex(mbb->front())));
		}
	}
}

unsigned minimumNextUseSucc(MachineBasicBlock *mb, unsigned regClassidx, unsigned vreg) {
	auto min = USES_INFINITY;
	if(mb->size() != 0)
		if(!LIS->isLiveOutOfMBB(LIS->getInterval(vreg+pow231), mb)  && LIS->getInterval(vreg+pow231).getValNumInfo(0)->def.getBaseIndex() != LIS->getInstructionIndex(mb->back()).getBaseIndex()){
			return USES_INFINITY;
		}
	for (auto b : mb->successors()) {
		if (blocksInformation[b->getNumber()].isLoopExit) {
			if (nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()].find(vreg) != nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()].end()) {
				if (nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()][vreg] < min) {
					min = nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()][vreg];
				}
			}
		} else {
			if(nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()].find(vreg) != nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()].end()) {
				if (nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()][vreg] < min) {
					min = nextUseMapsEntry_withRegClass[regClassidx][b->getNumber()][vreg];
				}
			}
		}
	}
	return min;
}

//call funktion with the start basic block
bool assignNextUseMaps(MachineBasicBlock *mb) {
	if (visited[mb->getNumber()])
		return true;
	visited[mb->getNumber()] ++;
	if (!mb->succ_empty()) {
		for (auto &succ : mb->successors()) {
			assignNextUseMaps(succ);
		}
	}
	for(unsigned i = 0; i < registerClassAvailable.size(); i++){
		for (unsigned j = 0; j < MRI->getNumVirtRegs(); j++) {
			if(!registerClassOfVirtreg[j] || registerClassAvailable[i] != registerClassOfVirtreg[j]->getID()){
				continue;
			}
			unsigned result = minimumNextUseSucc(mb,i ,j);
			if(result != USES_INFINITY){
				nextUseMapsExit_withRegClass[i][mb->getNumber()][j] = result;
			}
		}
	}
	for(unsigned i = 0; i < registerClassAvailable.size(); i++){
		for (unsigned j = 0; j < MRI->getNumVirtRegs(); j++) {
			if(!registerClassOfVirtreg[j] || registerClassAvailable[i] != registerClassOfVirtreg[j]->getID()){
				continue;
			}
			if (next_instruction_use_maps[mb->getNumber()].find(j) == next_instruction_use_maps[mb->getNumber()].end()) {
				if(nextUseMapsExit_withRegClass[i][mb->getNumber()].find(j) != nextUseMapsExit_withRegClass[i][mb->getNumber()].end()){
					nextUseMapsEntry_withRegClass[i][mb->getNumber()][j] = mb->size() + nextUseMapsExit_withRegClass[i][mb->getNumber()][j];
				}
			} else {
				if(LIS->getInterval(j+pow231).valnos.size() > 1){
					errs() << "how 2 defs? in SSA???\n";
				}else if(LIS->getInstructionFromIndex(LIS->getInterval(j+pow231).valnos.front()->def)->getParent()->getNumber() == mb->getNumber()){
					if(nextUseMapsEntry_withRegClass[i][mb->getNumber()].find(j) != nextUseMapsEntry_withRegClass[i][mb->getNumber()].end()){
						nextUseMapsEntry_withRegClass[i][mb->getNumber()].erase(j);
					}
					if(nextUseMapsExit_withRegClass[i][mb->getNumber()].find(j) == nextUseMapsExit_withRegClass[i][mb->getNumber()].end()){
						nextUseMapsExit_withRegClass[i][mb->getNumber()][j] = USES_INFINITY - 1;
					}
				}else {
					nextUseMapsEntry_withRegClass[i][mb->getNumber()][j] = next_instruction_use_maps[mb->getNumber()][j].front() - getDistanceFromSlotIndex(LIS->getInstructionIndex(mb->front()));
				}
				maxRegisterPressurePerBlock_withRegClass[i][mb->getNumber()]++;
			}
		}
	}
	for(unsigned i = 0; i < registerClassAvailable.size(); i++){
		for (unsigned j = 0; j < MRI->getNumVirtRegs(); j++) {
			if(!registerClassOfVirtreg[j]){
				continue;
			}
			if(registerClassAvailable[i] != registerClassOfVirtreg[j]->getID()){
				continue;
			}
			if(!mb->empty())
				if(getDistanceFromSlotIndex(LIS->getInstructionIndex(mb->back())) < virtRegToDef[j]){
					if(nextUseMapsEntry_withRegClass[i][mb->getNumber()].find(j) != nextUseMapsEntry_withRegClass[i][mb->getNumber()].end()){
						nextUseMapsEntry_withRegClass[i][mb->getNumber()].erase(j);
					}
				}
		}
	}
	return false;
}

std::vector<unsigned> getVirtRegsInInstruction(MachineInstr &instr, UseOrDef useOrDef) {
	std::vector<unsigned> vregs;
	if(instr.isDebugValue()){return vregs;}
	unsigned y =1<<31;
	if (useOrDef == GETDEF || useOrDef == BOTH) {
		if(virtregsInInstructions.find(&instr) != virtregsInInstructions.end()){
			for(auto v : virtregsInInstructions[&instr]) {
				if(registerClassOfVirtreg[v]->getID() == registerClassAvailable[currRegClassIdx])
					if(LIS->getInterval(v+y).getValNumInfo(0)->def.getBaseIndex() == LIS->getInstructionIndex(instr).getBaseIndex())
						if(noDublicate(vregs, v)){
							vregs.push_back(v);
						}
			}
		}
	}
	if (useOrDef == GETUSE || useOrDef == BOTH) {
		if(virtregsInInstructions.find(&instr) != virtregsInInstructions.end()){
			for(auto v : virtregsInInstructions[&instr]) {
				if(registerClassOfVirtreg[v]->getID() == registerClassAvailable[currRegClassIdx])
					if(LIS->getInterval(v+y).getValNumInfo(0)->def.getBaseIndex() != LIS->getInstructionIndex(instr).getBaseIndex())
						if(noDublicate(vregs, v)){
							vregs.push_back(v);
						}
			}
		}
	}
	return vregs;
}

std::vector<unsigned > getVirtRegsInMBB(MachineBasicBlock *mbb, UseOrDef uod){
	std::vector<unsigned > result;
	for(auto &i : *mbb){
		std::vector<unsigned > tmp = getVirtRegsInInstruction(i, uod);
		result = unionVec(result, tmp);
	}
	return result;
}

void fillpostOrder(MachineBasicBlock *mbb) {
	visit[mbb->getNumber()] = mbb;
	for (auto succ : mbb->successors()) {
		if (!visit[succ->getNumber()]) {
			fillpostOrder(succ);
		}
	}
	postOrder.push_back(mbb);
}

void initUsual(MachineBasicBlock *mbb) {
	std::vector<unsigned> freq;
	cand.clear();
	take.clear();
	for (unsigned i = 0; i < MRI->getNumVirtRegs(); i++) {
		freq.push_back(0);
	}
	unsigned numpreds = 0;
	if (!mbb->pred_empty())
		numpreds = mbb->pred_size();
	for (auto pred : mbb->predecessors()) {
		for(auto var : w[pred->getNumber()]) {
			freq[var] += 1;
			if (noDublicate(cand, var)) {
				cand.push_back(var);
			}
			if (freq[var] == numpreds) {
				without(cand, var);
				if (noDublicate(take,var)) {
					take.push_back(var);
				}
			}
		}
	}
	if(!cand.empty()){
		std::sort(cand.begin(), cand.end(), compareNextUseDistances(nullptr, mbb));
		unsigned check = k > take.size() ? k - (unsigned) take.size() : 0;
		while(cand.size() > check){
			cand.pop_back();
		}
		cand = unionVec(take, cand);
	}
	std::vector<unsigned > help;
	for(auto v : cand){
		if(mbb->size())
			if(nextUseMapsEntry_withRegClass[currRegClassIdx][mbb->getNumber()].find(v) != nextUseMapsEntry_withRegClass[currRegClassIdx][mbb->getNumber()].end()){
				help.push_back(v);
			}
	}
	cand = help;
}

void usedInLoop(std::vector<MachineBasicBlock *> blocks, std::vector<unsigned> &alive) {
	for (auto b : blocks) {
		std::vector<unsigned > tmp = getVirtRegsInMBB(b, BOTH);
		for(auto vreg : alive) {
			if(isElem(tmp, vreg)) {
				if (noDublicate(cand, vreg)) {
					cand.push_back(vreg);
				}
			}
		}
	}
}

std::vector<unsigned> phisOfBB(MachineBasicBlock *mbb) {
	std::vector<unsigned> result;
	for (auto &instr : *mbb) {
		if (instr.isPHI()) {
			if(instr.getOperand(0).getReg() >= pow231) {
				if(registerClassOfVirtreg[instr.getOperand(0).getReg() >= pow231]->getID() == currRegClassIdx){
					result.push_back(instr.getOperand(0).getReg() - pow231);
				}
			}else{
				errs() << "no virtreg\n";
			}
		}
	}
	return result;
}

std::vector<unsigned> liveInBlock(MachineBasicBlock *mbb) {
	std::vector<unsigned> result;
	for(auto v : nextUseMapsEntry_withRegClass[currRegClassIdx][mbb->getNumber()]){
		result.push_back(v.first);
	}
	return result;
}

unsigned maxLoopPressure(MachineLoop *l){
	unsigned max = 0;
	if(l){
		return max;
	}
	for(auto b : l->getBlocks()){
		if (max < maxRegisterPressurePerBlock_withRegClass[currRegClassIdx][b->getNumber()]) {
			max = maxRegisterPressurePerBlock_withRegClass[currRegClassIdx][b->getNumber()];
		}
	}
	return max;
}

void initLoopHeader(MachineBasicBlock *mbb) {
	loop_begin_spill.push_back(mbb);
	cand.clear();
	std::vector<unsigned> liveThrough;
	std::vector<unsigned> alive;
	std::vector<unsigned>  add;
	auto loop = Loops->getLoopFor(mbb);
	auto blocks = loop->getBlocks();
	std::vector<unsigned > phis  = phisOfBB(mbb);
	std::vector<unsigned > liveIn = liveInBlock(mbb);
	for(auto vre : phis){
		if(noDublicate(alive, vre))
			alive.push_back(vre);
	}
	for(auto vre : liveIn){
		if(noDublicate(alive, vre))
			alive.push_back(vre);
	}
	usedInLoop(blocks, alive);
	liveThrough = without(alive, cand);
	std::vector<unsigned > help;
	for(auto v : liveThrough){
		if(mbb->size())
			if(nextUseMapsEntry_withRegClass[currRegClassIdx][mbb->getNumber()].find(v) != nextUseMapsEntry_withRegClass[currRegClassIdx][mbb->getNumber()].end()){
				help.push_back(v);
			}
	}
	liveThrough = help;
	liveThrough_loopdepth.push_back(liveThrough);
	unsigned  max = maxLoopPressure(loop);
	if (cand.size() < k) {
		unsigned freeLoop = (k > max ?k - max : 0) + (unsigned) liveThrough.size();
		std::sort(liveThrough.begin(), liveThrough.end(), compareNextUseDistances(nullptr, mbb,true));
		for (unsigned j = 0; j <= freeLoop; j++) {
			if (liveThrough.size() == j) {
				break;
			}
			add.push_back(liveThrough[j]);
		}
	} else {
		std::sort(cand.begin(), cand.end(), compareNextUseDistances(nullptr, mbb,true));
		for (; cand.size() > k;) {
			cand.pop_back();
		}
		add.clear();
	}
	take = unionVec(cand, add);
	help.clear();
	for(auto v : take){
		if(mbb->size())
			if(nextUseMapsEntry_withRegClass[currRegClassIdx][mbb->getNumber()].find(v) != nextUseMapsEntry_withRegClass[currRegClassIdx][mbb->getNumber()].end()){
				help.push_back(v);
			}
	}
	take = help;
}

//name is irritating
void addSpillbefore(MachineInstr *inst, unsigned spillReg, bool beforeInstruction = true) {
	numOfSpills++;
	if(Loops->getLoopFor(inst->getParent())){
		numOfSpillsinLoop++;
	}
	unsigned stackslot = VRM->assignVirt2StackSlot(spillReg+pow231);
	if(beforeInstruction || inst->isTerminator()) {
		unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[spillReg]);
		BuildMI(*inst->getParent(),  inst, DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
		mapNewVregsToOld[newVregMI-pow231] = spillReg;
		mapPhiToSpill[newVregMI-pow231] = inst->getPrevNode();
		LIS->InsertMachineInstrInMaps(*inst->getPrevNode());
		errs() << "spillNEWMI1: "; mapPhiToSpill[newVregMI-pow231]->dump();
		errs() << "add spill before: " ;
	} else {
		unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[spillReg]);
		BuildMI(*inst->getParent(),  inst->getNextNode(), DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
		mapNewVregsToOld[newVregMI-pow231] = spillReg;
		mapPhiToSpill[newVregMI-pow231] = inst->getNextNode();
		LIS->InsertMachineInstrInMaps(*inst->getNextNode());
		errs() << "spillNEWMI3: "; mapPhiToSpill[newVregMI-pow231]->dump();
		errs() << "add spill after: " ;
	}
	inst->dump();
	didSpill++;
}

void addReloads(std::vector<unsigned> &reloads, MachineInstr *inst) {
	if(!reloads.empty()) {

		for (auto r: reloads) {
			int distance = getDistanceFromSlotIndex(LIS->getInstructionIndex(*inst)) - getDistanceFromSlotIndex(LIS->getInstructionIndex(inst->getParent()->front()));
			MachineBasicBlock::iterator Miter = inst->getParent()->begin();
			if(distance <= 1){
				if(Loops->getLoopFor(inst->getParent())){
					numOfReloadsInLoop++;
				}
				unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[r]);
				BuildMI(*inst->getParent(), inst->getParent()->front(), DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
				LIS->InsertMachineInstrInMaps(inst->getParent()->front());
				mapNewVregsToOld[newVregMI - pow231] = r;
				mapPhiToReload[newVregMI - pow231] = &inst->getParent()->front();
				errs() << "reloadNEWMI1: ";
				mapPhiToReload[newVregMI - pow231]->dump();

			}else{
				if(Loops->getLoopFor(inst->getParent())){
					numOfReloadsInLoop++;
				}
				unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[r]);
				BuildMI(*inst->getParent(), inst , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
				mapNewVregsToOld[newVregMI-pow231] = r;
				mapPhiToReload[newVregMI-pow231] = inst->getPrevNode();
				LIS->InsertMachineInstrInMaps(*inst->getPrevNode());
				errs() << "reloadNEWMI2: "; mapPhiToReload[newVregMI-pow231]->dump();
			}
			errs() << "r:" << r << "\n";
			numOfReloads++;
			didReload++;
		}
	}
}

void limit(MachineBasicBlock *mbb, MachineInstr *inst, unsigned m, bool first) {
	if(!inst){
		return;
	}

	int number = mbb->getNumber();
	std::sort(w[number].begin(), w[number].end(), compareNextUseDistances(inst, mbb));
	int loopCounter = 0;
	unsigned spill = 0;
	while (w[number].size() > m && loopCounter < liveThrough_loopdepth.size()) {
		if(!liveThrough_loopdepth[loopCounter].empty()){
			std::sort(liveThrough_loopdepth[loopCounter].begin(), liveThrough_loopdepth[loopCounter].end(), compareNextUseDistances(inst, mbb));
			spill = liveThrough_loopdepth[loopCounter].back();
			liveThrough_loopdepth[loopCounter].pop_back();
			if(VRM->getStackSlot(spill+pow231) != pow(2,30) -1){
				continue;
			}
			errs() << "before, w.size: "<<w[number].size() << " and m =" << m << " " <<" : ";
			for(auto pred : loop_begin_spill[loopCounter]->predecessors()){
				MachineInstr * spillInst;
				if(pred->size()){
					spillInst= &pred->back();
				}else{
					spillInst = &*pred->begin();
				}
				if(spillInst->isTerminator()){
					addSpillbefore(spillInst, spill, true);
				}else{
					addSpillbefore(spillInst, spill, false);
				}
			}
			for(auto i = w[number].begin(); i != w[number].end();i++){
				if(*i == spill){
					w[number].erase(i);
					break;
				}
				if(std::next(i) == w[number].end()){
					errs() << "how is liveTrough not in w?, maybe in  a loop within a loop" << endl;
				}
			}
		}else{
			loopCounter++;
		}
	}
	for (unsigned v = m /*???*/; v< w[number].size();v++) {
		if (!isElem(s[number], w[number][v]) && getNextUseDistance(number,w[number][v],inst) < USES_INFINITY) {
			errs()<< "spill " << w[number][v] << " ";
			if(inst) {
				addSpillbefore(inst, w[number][v], true);
			}
			errs() << "\n";
		}
		without(s[number], w[number][v]);
	}
	while (w[number].size() > m) {
		w[number].pop_back();
	}
	if(first){
		std::vector<unsigned> withoutInfinity;
		for(auto v : w[number]){
			if(getNextUseDistance(number,v,inst) != USES_INFINITY){
				withoutInfinity.push_back(v);
			}
		}
		w[number] = withoutInfinity;
	}
}



void minAlgorithm(MachineBasicBlock *mbb) {
	stillLive.clear();
	if(blocksInformation[mbb->getNumber()].isLoopExit)
		if(!liveThrough_loopdepth.empty()){
			liveThrough_loopdepth.pop_back();
			loop_begin_spill.pop_back();
		}
	for (auto &inst : *mbb) {
		if(inst.isDebugValue()){
			continue;
		}
		if(inst.isPHI()){
			if(mapPhiToSpill.find(inst.getOperand(0).getReg()-pow231) != mapPhiToSpill.end()){
				continue;
			}
			if(mapPhiToReload.find(inst.getOperand(0).getReg()-pow231) != mapPhiToReload.end()){
				continue;
			}
		}
		std::vector<unsigned> reloads;
		std::vector<unsigned> tmp;
		tmp = getVirtRegsInInstruction(inst, GETUSE);
		reloads = without(tmp,w[mbb->getNumber()]);
		stillLive.clear();
		for (auto use : reloads) {
			if(noDublicate(w[mbb->getNumber()],use))
				w[mbb->getNumber()].push_back(use);
			if(noDublicate(s[mbb->getNumber()],use))
				s[mbb->getNumber()].push_back(use);
		}
		limit(mbb, &inst, k,true);
		//remember the ones which where live, because they could get killed by the second limit
		for(auto v : w[mbb->getNumber()]){
			if(getNextUseDistance(mbb->getNumber(),v,&inst) == 0){
				stillLive.push_back(v);
			}
		}

		unsigned numberDefs = 0;
		for(auto def : inst.defs()){
			if (def.isReg()) {
				unsigned reg = def.getReg();
				if (reg >= pow231) {
					if(mapNewVregsToOld.find(reg-pow231) == mapNewVregsToOld.end()){ // because of the phi insertet as dummys
						if(registerClassOfVirtreg[reg-pow231]->getID() == registerClassAvailable[currRegClassIdx])
							numberDefs++;
					}
				}
			}
		}
		kwithoutDefs = k > numberDefs + stillLive.size()? k - numberDefs - stillLive.size(): 0;
		limit(mbb, inst.getNextNode(), kwithoutDefs,false);
		w[mbb->getNumber()] = unionVec(w[mbb->getNumber()], stillLive); // needed where NUD was 0
		std::vector<unsigned> tmp2;
		tmp2 = getVirtRegsInInstruction(inst, GETDEF);
		for(auto x : tmp2){
			if(getNextUseDistance(mbb->getNumber(),x,&inst) != USES_INFINITY){
				if(noDublicate(w[mbb->getNumber()], x)){
					w[mbb->getNumber()].push_back(x);
				}
			}
		}
		addReloads(reloads, &inst);
	}
}

void initForRegisterSet() {
	visit.clear();
	MachineBasicBlock *first = MF->getBlockNumbered(0);
	for (int i = 0; i < numberOfBBs; i++) {
		visit.push_back(nullptr);
	}
	fillpostOrder(first);
	for (auto start = postOrder.rbegin(); start != postOrder.rend(); start++) {
		reversePostOrder.push_back(*start);
	}
	if (reversePostOrder.size() != numberOfBBs) errs() << "reversed post order has not seen all bbs\n";
	//init spill and reload mappings
	for(unsigned i = 0; i < numberofAvailableRegclasses; i++){
		std::unordered_map<unsigned , std::vector<unsigned > > regclass_reloads;
		std::unordered_map<unsigned , std::vector<unsigned > > regclass_spill;
		spill_withRegClass.push_back(regclass_spill);
		reloads_withRegClass.push_back(regclass_reloads);
	}
}

void connectToPred(MachineBasicBlock* mbb){
	s[mbb->getNumber()].clear();
	for(auto pred : mbb->predecessors()){
		s[mbb->getNumber()] = unionVec(s[mbb->getNumber()], s[pred->getNumber()]);
	}
	s[mbb->getNumber()] = intersecVec(s[mbb->getNumber()], w[mbb->getNumber()]);
}

void computeRegisterSet(unsigned regClassidx) {
	currRegClassIdx = regClassidx;
	k = TRI->getRegClass(registerClassAvailable[currRegClassIdx])->getNumRegs();
	w.clear();
	s.clear();
	cand.clear();
	take.clear();
	for (int i = 0; i < numberOfBBs; i++) {
		std::vector<unsigned> tmp1;
		std::vector<unsigned> tmp2;
		w.push_back(tmp1);
		s.push_back(tmp2);
	}
	for (int i = 0; i < reversePostOrder.size(); i++) {
		if (Loops->isLoopHeader(reversePostOrder[i])) {
			initLoopHeader(reversePostOrder[i]);
			w[reversePostOrder[i]->getNumber()] = take;
		} else {
			initUsual(reversePostOrder[i]);
			w[reversePostOrder[i]->getNumber()] = cand;
		}
		connectToPred(reversePostOrder[i]);
		for(auto pred : reversePostOrder[i]->predecessors()){
			std::vector<unsigned > reloadOnEdgeWithINFINITY = without(w[reversePostOrder[i]->getNumber()], w[pred->getNumber()]);
			std::vector<unsigned > reloadOnEdge;
			std::vector<unsigned > spillOnEdgeWithINFINITY = without(s[reversePostOrder[i]->getNumber()], s[pred->getNumber()]);
			spillOnEdgeWithINFINITY = intersecVec(spillOnEdgeWithINFINITY, w[pred->getNumber()]);
			std::vector<unsigned > spillOnEdge;
			for(auto v : reloadOnEdgeWithINFINITY){
				// because we made some things live at exit with USES_INFINITY - 1
				if(nextUseMapsExit_withRegClass[currRegClassIdx][pred->getNumber()].find(v) != nextUseMapsExit_withRegClass[currRegClassIdx][pred->getNumber()].end()){
					if(nextUseMapsExit_withRegClass[currRegClassIdx][pred->getNumber()][v] < USES_INFINITY - 1){
						reloadOnEdge.push_back(v);
					}
				}
			}
			for(auto v : spillOnEdgeWithINFINITY){
				if(nextUseMapsExit_withRegClass[currRegClassIdx][pred->getNumber()].find(v) != nextUseMapsExit_withRegClass[currRegClassIdx][pred->getNumber()].end()){
					if(nextUseMapsExit_withRegClass[currRegClassIdx][pred->getNumber()][v] < USES_INFINITY - 1){
						spillOnEdge.push_back(v);
					}
				}
			}
			reloads_withRegClass[currRegClassIdx][edge_Matrix[pred->getNumber()][reversePostOrder[i]->getNumber()]] = reloadOnEdge;
			spill_withRegClass[currRegClassIdx][edge_Matrix[pred->getNumber()][reversePostOrder[i]->getNumber()]] = spillOnEdge;
		}
		minAlgorithm(reversePostOrder[i]);
	}
}

void initDefUseChain(){
	for (unsigned i = 0, e = MRI->getNumVirtRegs(); i != e; ++i) {
		std::vector<SlotIndex> tmp;
		defUseChain.push_back(tmp);
	}
	for(auto &block : *MF){
		for(auto &inst : block){
			if(inst.isDebugValue()){
				continue;
			}
			for(auto &operant : inst.uses()){
				if(operant.isReg()){
					if(operant.isUse()){
						if(operant.getReg() >= pow231 ){
							defUseChain[operant.getReg()-pow231].push_back(LIS->getInstructionIndex(inst));
						}
					}
				}
			}
		}
	}
}

void initVirtregsInInstructions(){
	for(unsigned i = 0; i < MRI->getNumVirtRegs(); i++){
		unsigned Reg = TargetRegisterInfo::index2VirtReg(i);
		if (MRI->reg_nodbg_empty(Reg)) {
			continue;
		}
		auto iter = MRI->use_begin(i+pow231);
		while(iter != MRI->use_end()){
			if(virtregsInInstructions.find(iter.operator*().getParent()) != virtregsInInstructions.end()){
				virtregsInInstructions[iter.operator*().getParent()].push_back(i);
			}else{
				std::vector<unsigned > tmp {i};
				virtregsInInstructions[iter.operator*().getParent()] = tmp;
			}
			iter++;
		}
		if(virtregsInInstructions.find(LIS->getInstructionFromIndex(LIS->getInterval(i+pow231).getValNumInfo(0)->def)) != virtregsInInstructions.end()){
			virtregsInInstructions[LIS->getInstructionFromIndex(LIS->getInterval(i+pow231).getValNumInfo(0)->def)].push_back(i);
		}else{
			std::vector<unsigned > tmp {i};
			virtregsInInstructions[LIS->getInstructionFromIndex(LIS->getInterval(i+pow231).getValNumInfo(0)->def)] = tmp;
		}
	}
}

void initForNextUseDistances(){
	//keep the sequence
	initSlotIndex();
	initDefUseChain();
	initLoopExits();
	initInstructionDistances();
	initVirtregsInInstructions();
}

std::vector<SlotIndex> getUseSlots(int VirtReg) {
	std::vector<SlotIndex> uses = defUseChain[VirtReg-pow231];
	return uses;
}

void computeNextUseDistances() {
	for (unsigned i = 0, e = MRI->getNumVirtRegs(); i != e; ++i) {
		vregSpilledAt.emplace_back(std::make_pair(0,0));
		std::vector<unsigned> virtRegVec;
		virtRegToDef.push_back((unsigned) -1);
		registerClassOfVirtreg.push_back(nullptr);
		unsigned Reg = TargetRegisterInfo::index2VirtReg(i);
		if (MRI->reg_nodbg_empty(Reg)) {
			continue;
		}
		LiveInterval *VirtReg = &LIS->getInterval(Reg);
		SA->analyze(VirtReg);
		ArrayRef<SlotIndex> MyUses = SA->getUseSlots();
		for (auto Use : MyUses) {
			auto mbb = LIS->getMBBFromIndex(Use);
			unsigned distance = getDistanceFromSlotIndex(Use);
			if(next_instruction_use_maps[mbb->getNumber()].find(i) == next_instruction_use_maps[mbb->getNumber()].end()){
				std::vector<unsigned > tmp {distance};
				next_instruction_use_maps[mbb->getNumber()][i] = tmp;
			}else{
				next_instruction_use_maps[mbb->getNumber()][i].push_back(distance);
			}
		}
		virtRegToDef[i] = getDistanceFromSlotIndex(VirtReg->beginIndex());
		const TargetRegisterClass *RC = MRI->getRegClass(Reg);
		registerClassOfVirtreg[i] = RC;
		if(noDublicate(registerClassAvailable, RC->getID())) registerClassAvailable.push_back(RC->getID());
	}
	for (unsigned i = 0; i < numberOfBBs; i++) {
		visited.push_back(0);
	}
	initNextUseMaps();
	assignNextUseMaps(&MF->front());
}

bool iscriticalEdge(MachineBasicBlock* from, MachineBasicBlock* to){
	if(from->succ_size() == 1 || to->pred_size() == 1){
		return false;
	}
	return true;
}

void PreSpill::connectAllMBBs(){
	for(unsigned i = 0; i < numberofAvailableRegclasses;i++){
		for(unsigned j = 0; j < edge_mapping.size();j++){
			if(reloads_withRegClass[i].find(j) == reloads_withRegClass[i].end() || spill_withRegClass[i].find(j) == spill_withRegClass[i].end()){
				continue;
			}
			if(!reloads_withRegClass[i][j].size() && !spill_withRegClass[i][j].size()){
				continue;
			}
			MachineBasicBlock *nmbb = nullptr;
			if(iscriticalEdge(edge_mapping[j].from, edge_mapping[j].to)){
				if(edge_mapping[j].from->canSplitCriticalEdge(edge_mapping[j].to)){
					errs() << "can split edge from:" << edge_mapping[j].from->getNumber() << " to:" << edge_mapping[j].to->getNumber() << endl;
				}else{
					errs() << "woa can not split the edge from " <<edge_mapping[j].from->getNumber()<< " ns:"<< edge_mapping[j].from->succ_size() << " to "<<edge_mapping[j].to->getNumber() << " np:" << edge_mapping[j].to->pred_size()<<"\n";
				}
				if(alreadySplit.find(j) != alreadySplit.end()){
					nmbb = alreadySplit[j];
				}else{
					nmbb = edge_mapping[j].from->SplitCriticalEdge(edge_mapping[j].to,*this);
					alreadySplit[j] = nmbb;
				}
			}
			if(reloads_withRegClass[i].find(j) != reloads_withRegClass[i].end())
				for(auto reload : reloads_withRegClass[i][j]){
					numOfReloads++;
					auto Original = VRM->getOriginal(reload+pow231);
					auto StackSlot = VRM->getStackSlot(Original);
					if(nmbb){
						if(Loops->getLoopFor(nmbb)){
							numOfReloadsInLoop++;
						}
						unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[reload]);
						BuildMI(*nmbb, nmbb->front() , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
						mapNewVregsToOld[newVregMI-pow231] = reload;
						mapPhiToReload[newVregMI-pow231] = &nmbb->front();
						LIS->InsertMachineInstrInMaps(nmbb->front());
						errs() << "reloadNEWMIc1: "<< reload << " "; mapPhiToReload[newVregMI-pow231]->dump();
					}else{
						if(edge_mapping[j].from->succ_size() == 1){
							if(Loops->getLoopFor(edge_mapping[j].from)){
								numOfReloadsInLoop++;
							}
							if(!edge_mapping[j].from->size()){
								unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[reload]);
								BuildMI(*edge_mapping[j].from, edge_mapping[j].from->begin() , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
								mapNewVregsToOld[newVregMI-pow231] = reload;
								mapPhiToReload[newVregMI-pow231] = &edge_mapping[j].from->front();
								LIS->InsertMachineInstrInMaps(edge_mapping[j].from->front());
								errs() << "reloadNEWMIc2a: "<< reload << " "; mapPhiToReload[newVregMI-pow231]->dump();
								continue;
							}
							MachineBasicBlock::iterator insert = edge_mapping[j].from->end();
							if(edge_mapping[j].from->back().isTerminator() && edge_mapping[j].from->size() > 1){
								insert--;
								insert--;
							}else{
								insert --;
							}
							MachineInstrSpan MIS(insert);
							unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[reload]);
							BuildMI(*edge_mapping[j].from, std::next(insert) , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
							mapNewVregsToOld[newVregMI-pow231] = reload;
							mapPhiToReload[newVregMI-pow231] = &(*std::next(insert));
							LIS->InsertMachineInstrInMaps(*std::next(insert));
							errs() << "reloadNEWMIc2: "<< reload << " "; mapPhiToReload[newVregMI-pow231]->dump();
						}else if(edge_mapping[j].to->pred_size() == 1){
							if(Loops->getLoopFor(edge_mapping[j].to)){
								numOfReloadsInLoop++;
							}
							unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[reload]);
							BuildMI(*edge_mapping[j].to, edge_mapping[j].to->front() , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
							mapNewVregsToOld[newVregMI-pow231] = reload;
							mapPhiToReload[newVregMI-pow231] = &edge_mapping[j].to->front();
							LIS->InsertMachineInstrInMaps(edge_mapping[j].to->front());
							errs() << "reloadNEWMIc3: "<< reload << " "; mapPhiToReload[newVregMI-pow231]->dump();
							errs() << "modifyed block:";
							edge_mapping[j].to->dump();
						}else {
							errs() << "reload " <<reload<< "did not work on edge from "<< edge_mapping[j].from->getNumber()<<" to "<< edge_mapping[j].to->getNumber()<<" , should not occur!!\n";
						}
					}
				}
			if(spill_withRegClass[i].find(i) != spill_withRegClass[i].end())
				for(auto spill : spill_withRegClass[i][j]){
					numOfSpills++;
					auto Original = VRM->getOriginal(spill+pow231);
					errs() << "original: " << Original << endl;
					auto StackSlot = VRM->assignVirt2StackSlot(Original);
					errs() << "stackslot_s: " << StackSlot << endl;
					if(nmbb){
						if(Loops->getLoopFor(nmbb)){
							numOfSpillsinLoop++;
						}
						unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[spill]);
						BuildMI(*nmbb,nmbb->front() , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
						mapNewVregsToOld[newVregMI-pow231] = spill;
						mapPhiToSpill[newVregMI-pow231] = &nmbb->front() ;
						LIS->InsertMachineInstrInMaps(nmbb->front());
						errs() << "spillNEWMIc: "; mapPhiToSpill[newVregMI-pow231]->dump();
					}else{
						if(edge_mapping[j].from->succ_size() == 1){
							if(Loops->getLoopFor(edge_mapping[j].from)){
								numOfSpillsinLoop++;
							}
							if(!edge_mapping[j].from->size()){
								unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[spill]);
								BuildMI(*edge_mapping[j].from,edge_mapping[j].from->begin(), DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
								mapNewVregsToOld[newVregMI-pow231] = spill;
								mapPhiToSpill[newVregMI-pow231] = &edge_mapping[j].from->front() ;
								LIS->InsertMachineInstrInMaps(edge_mapping[j].from->front());
								errs() << "spillNEWMIc: "; mapPhiToSpill[newVregMI-pow231]->dump();
								continue;
							}
							MachineBasicBlock::iterator insert = edge_mapping[j].from->end();
							if(edge_mapping[j].from->back().isTerminator() && edge_mapping[j].from->size() > 1){
								insert--;
								insert--;
							}else{
								insert--;
							}
							unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[spill]);
							BuildMI(*edge_mapping[j].from,std::next(insert) , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
							mapNewVregsToOld[newVregMI-pow231] = spill;
							mapPhiToSpill[newVregMI-pow231] = &*std::next(insert) ;
							LIS->InsertMachineInstrInMaps(*std::next(insert));
							errs() << "spillNEWMIc: "; mapPhiToSpill[newVregMI-pow231]->dump();
							errs() << "modifyed block:";
							edge_mapping[j].from->dump();
						}else if(edge_mapping[j].to->pred_size() == 1){
							if(Loops->getLoopFor(edge_mapping[j].to)){
								numOfSpillsinLoop++;
							}
							unsigned newVregMI = MRI->createVirtualRegister(registerClassOfVirtreg[spill]);
							BuildMI(*edge_mapping[j].to,edge_mapping[j].to->front() , DebugLoc(), TII->get(TargetOpcode::PHI), newVregMI);
							mapNewVregsToOld[newVregMI-pow231] = spill;
							mapPhiToSpill[newVregMI-pow231] = &edge_mapping[j].to->front() ;
							LIS->InsertMachineInstrInMaps(edge_mapping[j].to->front());
							errs() << "spillNEWMIc: "; mapPhiToSpill[newVregMI-pow231]->dump();
							errs() << "modifyed block:";
							edge_mapping[j].to->dump();
						}else {
							errs() << "spill did not work!!\n";
						}
					}
				}
		}
	}

}

unsigned getOffset(MachineInstr & inst){
	auto mbb = inst.getParent();
	unsigned offset = 0;
	for(auto &i : *mbb){
		if(i.isIdenticalTo(inst)){
			return offset;
		}
		offset++;
	}
	return USES_INFINITY;
}

//computing SSA again
//kill phi-dummys
std::vector<MachineInstr*> kill;
std::vector<bool> sealed;
std::vector<bool> filled;
std::unordered_map<unsigned , unsigned> visit_for_sealing;
std::vector<unsigned > virtRegsNeedPhi;
std::vector<std::unordered_map<unsigned, unsigned>> currentDef;
std::vector<std::pair<unsigned ,MachineOperand *>> mapping;
//phis[block][phiIDX]](virtreg, (virtregsinPhi,block))
std::vector<std::vector<std::pair<unsigned , std::vector<std::pair<unsigned , MachineBasicBlock*>>>>> phis;
//incompletePhis[idx](virtreg, block)
std::vector<std::pair<unsigned , unsigned > > incompletePhis;
std::unordered_map<unsigned ,unsigned > checkSingleDefinition;
void initComputeSSa(){
	for(unsigned i = 0; i < MF->getNumBlockIDs(); i++){
		sealed.push_back(false);
		filled.push_back(false);
		std::unordered_map<unsigned ,unsigned > tmp;
		currentDef.push_back(tmp);
		std::vector<std::pair<unsigned , std::vector<std::pair<unsigned , MachineBasicBlock*>>>> tmp2;
		phis.push_back(tmp2);
	}
	for(auto &block : *MF){
		for(auto &inst : block){
			if(inst.isDebugValue()){
				continue;
			}
			std::pair<unsigned ,MachineOperand *> tmp;
			mapping.push_back(tmp);
		}
	}
}

MachineInstrBuilder InsertNewDef(unsigned Opcode,
                                 MachineBasicBlock *BB, MachineBasicBlock::iterator I,
                                 const TargetInstrInfo *TII, unsigned val) {
	return BuildMI(*BB, I, DebugLoc(), TII->get(Opcode), val);
}

MachineInstrBuilder insertPhi(MachineBasicBlock* BB, unsigned val){
	MachineBasicBlock::iterator Loc = BB->empty() ? BB->end() : BB->begin();
	MachineInstrBuilder InsertedPHI = InsertNewDef(TargetOpcode::PHI, BB, Loc,TII, val);
	return InsertedPHI;
}

unsigned readVariableRecursive(unsigned block, unsigned virtReg);

void writeVariable(unsigned block, unsigned virtReg, unsigned value){
	currentDef[block][virtReg] = value;
}

unsigned readVariable(unsigned block, unsigned virtReg){
	if(currentDef[block].find(virtReg) != currentDef[block].end()){
		return currentDef[block][virtReg];
	}
	return readVariableRecursive(block, virtReg);
}

unsigned readVariableRecursive(unsigned block, unsigned virtReg){
	unsigned val = 0;
	if(!sealed[block]){
		const TargetRegisterClass * RC = registerClassOfVirtreg[virtReg];
		val = MRI->createVirtualRegister(RC)-pow231;
		currentDef[block][val] = val;
		incompletePhis.emplace_back(virtReg, block);
	}else if(MF->getBlockNumbered(block)->pred_size() == 1){
		val = readVariable(MF->getBlockNumbered(block)->pred_begin().operator*()->getNumber(), virtReg);
	}else{
		unsigned compare = -1;
		bool phineeded = true;
		if(phineeded){
			const TargetRegisterClass * RC = registerClassOfVirtreg[virtReg];
			val = MRI->createVirtualRegister(RC) - pow231;
			currentDef[block][val] = val;
			MachineInstrBuilder phi = insertPhi(MF->getBlockNumbered(block),val+pow231);
			writeVariable(block,virtReg,val);
			errs() << "add to phi at " << block <<": " << val  << endl;
			for(auto &pred : MF->getBlockNumbered(block)->predecessors()){
				errs() << readVariable(pred->getNumber(),virtReg) << " at BB:"<<pred->getNumber() << " ";
			}
			errs() << endl;
			for(auto &pred : MF->getBlockNumbered(block)->predecessors()){
				phi.addReg(readVariable(pred->getNumber(),virtReg)+pow231).addMBB(pred);
			}
			errs() << endl;
			//should remove trivial phis
		}
	}
	writeVariable(block,virtReg,val);
	return val;
}

bool allPredsConnected(MachineBasicBlock* block){
	for(auto &pred : block->predecessors()){
		if(visit_for_sealing.find(pred->getNumber()) == visit_for_sealing.end()){
			return false;
		}
	}
	return true;
}

MachineBasicBlock *findCorrespondingPred(const MachineInstr *MI,
                                         MachineOperand *U) {
	for (unsigned i = 1, e = MI->getNumOperands(); i != e; i += 2) {
		if (&MI->getOperand(i) == U)
			return MI->getOperand(i+1).getMBB();
	}

	llvm_unreachable("MachineOperand::getParent() failure?");
}

void computeSSA(){
	VRM->grow();
	for(auto &block : *MF){
		visit_for_sealing[block.getNumber()] = 1;
		if(allPredsConnected(&block)){
			sealed[block.getNumber()] = true;
		}
		std::vector<MachineInstr*> erease;
		for(auto &inst : block){
			if(inst.isDebugValue()){
				continue;
			}
			for(auto &op : inst.operands()){
				if(op.isReg()){
					if(op.isDef()){
						if(op.getReg() >= pow231){
							unsigned def = op.getReg()-pow231;
							if(mapNewVregsToOld.find(def) != mapNewVregsToOld.end()){
								if(mapPhiToReload.find(def) != mapPhiToReload.end()){
									if(VRM->getStackSlot(mapNewVregsToOld[def]+pow231) == pow(2,30) - 1 ){
										errs()<< "reload "<< mapNewVregsToOld[def] <<" without stackslot!\n";
										continue;
									}
									numOfReloads++;
									if(Loops->isLoopHeader(&block)){
										numOfReloadsInLoop++;
									}
									TII->loadRegFromStackSlot(block, inst ,def+pow231,VRM->getStackSlot(mapNewVregsToOld[def]+pow231),registerClassOfVirtreg[mapNewVregsToOld[def]],TRI);
									errs() << "MYDEF INST: "; inst.getPrevNode()->dump();
									LIS->InsertMachineInstrInMaps(*inst.getPrevNode());
									kill.push_back(&inst);
									writeVariable(block.getNumber(),mapNewVregsToOld[def],def);
									checkSingleDefinition[def] = 1;
								}
								else if(mapPhiToSpill.find(def) != mapPhiToSpill.end()){

									numOfSpills++;
									if(Loops->isLoopHeader(&block)){
										numOfSpillsinLoop++;
									}
									TII->storeRegToStackSlot(block,inst,mapNewVregsToOld[def]+pow231,false, VRM->getStackSlot(mapNewVregsToOld[def]+pow231),registerClassOfVirtreg[mapNewVregsToOld[def]],TRI);
									errs() << "MYUSE INST: "; inst.getPrevNode()->dump();
									LIS->InsertMachineInstrInMaps(*inst.getPrevNode());
									kill.push_back(&inst);
								} else {
									errs() << "should always be a def or an use! \n";
								}
							}else{
								if(checkSingleDefinition.find(def) == checkSingleDefinition.end()){
									writeVariable(block.getNumber(),def,def);
									checkSingleDefinition[def] = 1;
								}else{
									errs() << "i think this should never happen!\n";
									checkSingleDefinition[def] += 1;
									unsigned newVreg = MRI->createVirtualRegister(registerClassOfVirtreg[op.getReg()-pow231])-pow231;
									VRM->grow();
									writeVariable(block.getNumber(),def,newVreg);
									op.setReg(newVreg+pow231);
								}
							}
						}
					}
					if(op.isUse()){
						if(op.getReg() >= pow231){
							if(inst.isPHI()){
								auto mbb = findCorrespondingPred(&inst,&op);
								unsigned changedVreg = op.getReg()-pow231;
								if(mapNewVregsToOld.find(changedVreg) != mapNewVregsToOld.end()){
									errs() << "change " << changedVreg<< " to " << mapNewVregsToOld[changedVreg] << endl;
									changedVreg = mapNewVregsToOld[changedVreg];
								}
								unsigned newVreg = readVariable(mbb->getNumber(),changedVreg);
								op.setReg(newVreg + pow231);
							}else{
								unsigned changedVreg = op.getReg()-pow231;
								if(mapNewVregsToOld.find(changedVreg) != mapNewVregsToOld.end()){
									changedVreg = mapNewVregsToOld[changedVreg];
								}
								unsigned newVreg = readVariable(block.getNumber(),changedVreg);
								op.setReg(newVreg + pow231);
							}
						}
					}
				}
			}
		}

		for(auto &succ : block.successors()){
			if(allPredsConnected(succ)){
				sealed[succ->getNumber()] = true;
			}
		}
	}

	while(incompletePhis.size() != 0){
		auto p = incompletePhis.back();
		incompletePhis.pop_back();
		errs() << "add to incomplete phi at " << p.second <<": " << readVariable(p.second,p.first)  << endl;
		for(auto &pred : MF->getBlockNumbered(p.second)->predecessors()){
			errs() << readVariable(pred->getNumber(),p.first) << " at BB:"<<pred->getNumber() << " ";
		}

		MachineInstrBuilder phi = insertPhi(MF->getBlockNumbered(p.second), readVariable(p.second,p.first)+pow231);
		for(auto &pred : MF->getBlockNumbered(p.second)->predecessors()) {
			phi.addReg(readVariable(pred->getNumber(), p.first) + pow231).addMBB(pred);
		}
	}
	for(auto &item : kill){
		item->getParent()->erase(item);
	}
	VRM->grow();
}

void prepareNextFuntionSSA(){
	sealed.clear();
	filled.clear();
	incompletePhis.clear();
	phis.clear();
	mapping.clear();
	virtRegsNeedPhi.clear();
	currentDef.clear();
	checkSingleDefinition.clear();
	kill.clear();
	mapPhiToReload.clear();
	mapPhiToSpill.clear();
	mapNewVregsToOld.clear();
}

void prepareNextFunction(){
	MF = nullptr;
	MRI = nullptr;
	TRI = nullptr;
	VRM = nullptr;
	LIS = nullptr;
	Matrix = nullptr;
	Loops = nullptr;
	TII = nullptr;
	//MachineInstrBuilder MIB;
	SA.release();
	//RegisterClassInfo RegClassInfo;
	min_slotIndex = SlotIndex();
	numberOfBBs = 0;
	numberofAvailableRegclasses = 0;
	currRegClassIdx = 0;
	loop_begin_spill.clear();
//variables live through the loop of loop_begin_spill
	liveThrough_loopdepth.clear();
//next_instruction_use_maps[block][virtReg][number of use]
	next_instruction_use_maps.clear();
	virtregsInInstructions.clear();
//virtRegToDef[VIrtreg]
	virtRegToDef.clear();
//loopExits_atinstructionNr[idx]
	loopExits_atinstructionNr.clear();
//registerClassOfVirtreg[virtReg]
	registerClassOfVirtreg.clear();
//registerClassAvailable[idx], idx < |avaiable Regclasses|
	registerClassAvailable.clear();
//reloads_withRegClass[regclass][edgeNr][idx]
	reloads_withRegClass.clear();
//spill_withRegClass[regclass][edgeNr][idx]
	spill_withRegClass.clear();
//vregSpilledAT[vreg] = (number ob bb, offset)
	vregSpilledAt.clear();
//idxToMachineInstr[idx]
	idxToMachineInstr.clear();
//edge_mapping[idx]
	edge_mapping.clear();
//edge_matrix[block][succ]
	edge_Matrix.clear();
//blocksInformation[blockNumber]
	blocksInformation.clear();
//maxRegisterPressurePerBlock_withRegClass[regClass][block number]
	maxRegisterPressurePerBlock_withRegClass.clear();
//nextUseMaps[block][regclass][virtreg]
	nextUseMapsEntry_withRegClass.clear();
	nextUseMapsExit_withRegClass.clear();
	k = 0;
	kwithoutDefs = 0;
	stillLive.clear();
//w[block][idx]
	w.clear();
//s[block][idx]
	s.clear();
//cans[idx]
	cand.clear();
//take[idx]
	take.clear();
	postOrder.clear();
	reversePostOrder.clear();
	visited.clear();
	visit.clear();
	countFunctions++;
	alreadySplit.clear();
	defUseChain.clear();
	prepareNextFuntionSSA();
}

bool flag = true;
int go = 0;
bool PreSpill::runOnMachineFunction(MachineFunction &mf) {
	if(flag){
		std::cout << "Enter 0 for just greedy, and 1 for extra bespillbelady: ";
		std::cin >> go;
		flag=false;
	}
	if (!go){
		return false;
	}
	errs() << "begin new Function: \n";

	MF = &mf;
	TRI = MF->getSubtarget().getRegisterInfo();
	VRM = &getAnalysis<VirtRegMap>();
	LIS = &getAnalysis<LiveIntervals>();
	Matrix = &getAnalysis<LiveRegMatrix>();
	Loops = &getAnalysis<MachineLoopInfo>();
	MRI = &VRM->getRegInfo();
	TII = MF->getSubtarget().getInstrInfo();
	numberOfBBs = MF->getNumBlockIDs();
	numberOFVirtRegs = MRI->getNumVirtRegs();
	pow231 =(unsigned) 1 << 31;
	RegClassInfo.runOnMachineFunction(mf);
	SA.reset(new SplitAnalysis(*VRM, *LIS, *Loops));
	errs() << "Number of BB: " << numberOfBBs << " and vregs: "<<numberOFVirtRegs <<"\n";
	initForNextUseDistances();
	computeNextUseDistances();
	numberofAvailableRegclasses = registerClassAvailable.size();
	initForRegisterSet();
	for(unsigned i = 0; i < numberofAvailableRegclasses;i++){
		computeRegisterSet(i);
	}
	connectAllMBBs();
	initComputeSSa();
	computeSSA();
	errs() << "number of spills: "<< numOfSpills << endl;
	errs() << "Number of spills in loop: "<< numOfSpillsinLoop << endl;
	errs() << "number of reloads: " << numOfReloads << endl;
	errs() << "Number of reloads in loop: "<< numOfReloadsInLoop<< endl;
	errs() << "FINISH with Funktion " << countFunctions << "\n";
	prepareNextFunction();
	errs() << "end function!\n\n";
	return false;
}

FunctionPass *llvm::createPreSpillPass() {
	return new PreSpill();
}