#pragma once

#include "interference_graph.h"
#include "graph_coloring.h"
#include "ir_parser.h"
#include <vector>
#include <unordered_map>

namespace optreg {

// Global allocator works across multiple functions
// considering calling conventions and register pressure at call sites

struct CallSite {
    uint32_t caller_func;
    uint32_t callee_func;
    uint32_t call_instruction;
    std::vector<uint32_t> live_at_call;  // Variables live across call
};

struct GlobalCFG {
    std::vector<ControlFlowGraph> functions;
    std::vector<CallSite> call_sites;
    std::unordered_map<uint32_t, std::string> function_names;
};

// Global interference graph spanning multiple functions
struct GlobalInterferenceGraph {
    uint32_t num_variables;
    std::unordered_map<uint32_t, std::unordered_set<uint32_t>> edges;
    std::unordered_map<uint32_t, uint32_t> degree;
    
    // Which function each variable belongs to
    std::unordered_map<uint32_t, uint32_t> var_to_function;
    
    // Calling convention constraints
    // Variables that must be in specific registers (arguments, returns)
    std::unordered_map<uint32_t, uint32_t> required_registers;
};

class GlobalRegisterAllocator {
public:
    GlobalRegisterAllocator(uint32_t num_registers) 
        : num_registers_(num_registers) {}
    
    // Build global interference graph from multiple functions
    GlobalInterferenceGraph build_global_graph(const GlobalCFG& cfg);
    
    // Heuristic: Priority-based coloring with calling convention awareness
    RegisterAllocation allocate_heuristic_global(
        const GlobalCFG& cfg,
        const GlobalInterferenceGraph& graph
    );
    
    // Optimal: ILP with interprocedural constraints
    RegisterAllocation allocate_optimal_global(
        const GlobalCFG& cfg,
        const GlobalInterferenceGraph& graph,
        GraphColoringAllocator::SolverType solver_type = GraphColoringAllocator::SolverType::Newton
    );
    
private:
    uint32_t num_registers_;
    
    // Compute priority for global allocation
    // Higher priority for:
    // - Variables live across calls
    // - Variables in hot loops
    // - Variables with many uses
    double compute_priority(
        uint32_t var,
        const GlobalCFG& cfg,
        const GlobalInterferenceGraph& graph
    );
    
    // Formulate global allocation as ILP
    // Additional constraints:
    // - Calling convention (caller/callee-saved)
    // - Cross-function consistency
    // - Minimize spills at call boundaries
    LPProblem formulate_global_ip(
        const GlobalCFG& cfg,
        const GlobalInterferenceGraph& graph
    );
};

} // namespace optreg
