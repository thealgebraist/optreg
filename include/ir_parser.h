#pragma once

#include <vector>
#include <unordered_map>
#include <string>
#include <cstdint>

namespace optreg {

// Task 1: IR representation and parsing

struct Variable {
    uint32_t id;
    std::string name;
    uint32_t def_point;  // program point where defined
    uint32_t last_use;   // last use point
};

struct Instruction {
    uint32_t id;
    std::string opcode;
    std::vector<uint32_t> operands;  // variable IDs
    uint32_t result;  // result variable ID (if any)
};

struct BasicBlock {
    uint32_t id;
    std::vector<Instruction> instructions;
    std::vector<uint32_t> successors;
    std::vector<uint32_t> predecessors;
};

struct ControlFlowGraph {
    std::vector<BasicBlock> blocks;
    std::unordered_map<uint32_t, Variable> variables;
    uint32_t entry_block;
};

// Parse IR from Agda-generated format
ControlFlowGraph parse_ir(const std::string& ir_text);

// Convert expression to CFG
void expr_to_cfg(const std::string& expr, ControlFlowGraph& cfg);

} // namespace optreg
