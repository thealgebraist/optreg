#include "live_range.h"
#include <algorithm>

namespace optreg {

LivenessInfo compute_liveness(const ControlFlowGraph& cfg) {
    LivenessInfo info;
    
    // Backward dataflow analysis
    // live_out[B] = ∪ live_in[S] for all successors S
    // live_in[B] = use[B] ∪ (live_out[B] - def[B])
    
    bool changed = true;
    while (changed) {
        changed = false;
        
        for (const auto& block : cfg.blocks) {
            std::set<uint32_t> old_live_in = info.live_in[block.id];
            
            // Compute live_out
            std::set<uint32_t> live_out;
            for (uint32_t succ_id : block.successors) {
                const auto& succ_live_in = info.live_in[succ_id];
                live_out.insert(succ_live_in.begin(), succ_live_in.end());
            }
            info.live_out[block.id] = live_out;
            
            // Compute live_in from live_out
            std::set<uint32_t> new_live_in = live_out;
            
            // Process instructions backward
            for (auto it = block.instructions.rbegin(); 
                 it != block.instructions.rend(); ++it) {
                // Remove defined variable
                if (it->result != UINT32_MAX) {
                    new_live_in.erase(it->result);
                }
                // Add used variables
                for (uint32_t operand : it->operands) {
                    new_live_in.insert(operand);
                }
            }
            
            info.live_in[block.id] = new_live_in;
            
            if (new_live_in != old_live_in) {
                changed = true;
            }
        }
    }
    
    // Convert to live ranges
    for (const auto& [var_id, var] : cfg.variables) {
        LiveRange range;
        range.var_id = var_id;
        range.start = var.def_point;
        range.end = var.last_use;
        info.ranges.push_back(range);
    }
    
    return info;
}

bool ranges_interfere(const LiveRange& r1, const LiveRange& r2) {
    // Ranges interfere if they overlap
    return !(r1.end < r2.start || r2.end < r1.start);
}

} // namespace optreg
