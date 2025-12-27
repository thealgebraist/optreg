#pragma once

#include "live_range.h"
#include <unordered_set>

namespace optreg {

// Task 4: Interference graph

struct InterferenceGraph {
    uint32_t num_variables;
    // adjacency list: var -> set of interfering vars
    std::unordered_map<uint32_t, std::unordered_set<uint32_t>> edges;
    
    // degree of each variable (for coloring heuristics)
    std::unordered_map<uint32_t, uint32_t> degree;
};

// Build interference graph from live ranges
InterferenceGraph build_interference_graph(
    const LivenessInfo& liveness,
    const ControlFlowGraph& cfg
);

// Check if two variables interfere
bool variables_interfere(
    const InterferenceGraph& graph,
    uint32_t v1,
    uint32_t v2
);

// Get neighbors of a variable
const std::unordered_set<uint32_t>& get_neighbors(
    const InterferenceGraph& graph,
    uint32_t var
);

} // namespace optreg
