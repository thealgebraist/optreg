#pragma once

#include "ir_parser.h"
#include <set>

namespace optreg {

// Task 3: Live range analysis

struct LiveRange {
    uint32_t var_id;
    uint32_t start;  // first program point
    uint32_t end;    // last program point
};

struct LivenessInfo {
    std::vector<LiveRange> ranges;
    // live_in[block_id] = set of variables live at block entry
    std::unordered_map<uint32_t, std::set<uint32_t>> live_in;
    // live_out[block_id] = set of variables live at block exit
    std::unordered_map<uint32_t, std::set<uint32_t>> live_out;
};

// Compute live ranges via dataflow analysis
LivenessInfo compute_liveness(const ControlFlowGraph& cfg);

// Check if two live ranges overlap
bool ranges_interfere(const LiveRange& r1, const LiveRange& r2);

} // namespace optreg
