#include "ir_parser.h"
#include <sstream>
#include <iostream>

namespace optreg {

ControlFlowGraph parse_ir(const std::string& ir_text) {
    ControlFlowGraph cfg;
    cfg.entry_block = 0;
    
    // Simple parser: one basic block for now
    BasicBlock bb;
    bb.id = 0;
    
    std::istringstream iss(ir_text);
    std::string line;
    uint32_t instr_id = 0;
    
    while (std::getline(iss, line)) {
        if (line.empty() || line[0] == '#') continue;
        
        Instruction instr;
        instr.id = instr_id++;
        
        // Parse simple format: "result = op arg1 arg2"
        // This is a stub - full parser would handle IR format
        instr.opcode = "add"; // placeholder
        bb.instructions.push_back(instr);
    }
    
    cfg.blocks.push_back(bb);
    return cfg;
}

void expr_to_cfg(const std::string& expr, ControlFlowGraph& cfg) {
    // Convert Let expressions to basic blocks
    // Stub implementation
    cfg.entry_block = 0;
    BasicBlock bb;
    bb.id = 0;
    cfg.blocks.push_back(bb);
}

} // namespace optreg
