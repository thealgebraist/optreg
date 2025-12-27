#pragma once

#include "interference_graph.h"
#include "branch_bound.h"

namespace optreg {

// Task 13-15: Register allocation as graph coloring IP

struct RegisterAllocation {
    // var_id -> register_id (or -1 if spilled)
    std::unordered_map<uint32_t, int32_t> assignment;
    uint32_t num_spills;
    double total_cost;
    std::vector<uint32_t> spilled_vars;
};

class GraphColoringAllocator {
public:
    GraphColoringAllocator(uint32_t num_registers) 
        : num_registers_(num_registers) {}
    
    // Task 13: Formulate as IP
    LPProblem formulate_ip(
        const InterferenceGraph& graph,
        const std::unordered_map<uint32_t, double>& spill_costs
    );
    
    // Task 14: Calculate spill costs based on loop nesting
    std::unordered_map<uint32_t, double> compute_spill_costs(
        const ControlFlowGraph& cfg,
        const LivenessInfo& liveness
    );
    
    // Task 15: Extract register assignment from IP solution
    RegisterAllocation extract_solution(
        const IPSolution& ip_solution,
        const InterferenceGraph& graph
    );
    
    // High-level interface: allocate registers optimally
    RegisterAllocation allocate_optimal(
        const ControlFlowGraph& cfg,
        const LivenessInfo& liveness,
        const InterferenceGraph& graph
    );

private:
    uint32_t num_registers_;
    
    // Helper: compute loop nesting depth for each basic block
    std::unordered_map<uint32_t, uint32_t> compute_loop_nesting(
        const ControlFlowGraph& cfg
    );
};

// Task 16: Compare with heuristic allocator
struct AllocationComparison {
    RegisterAllocation optimal;
    RegisterAllocation heuristic;
    double optimal_cost;
    double heuristic_cost;
    double improvement_pct;
    uint32_t optimal_time_ms;
    uint32_t heuristic_time_ms;
};

AllocationComparison compare_allocators(
    const ControlFlowGraph& cfg,
    uint32_t num_registers
);

} // namespace optreg
