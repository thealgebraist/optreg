#include "graph_coloring.h"
#include "interior_point.h"
#include <limits>

namespace optreg {

// Formulate graph coloring as integer program
LPProblem GraphColoringAllocator::formulate_ip(
    const InterferenceGraph& graph,
    const std::unordered_map<uint32_t, double>& spill_costs
) {
    // Variables: x[v,r] for each variable v and register r
    // Minimize: sum of spill costs for unallocated variables
    
    uint32_t n_vars = graph.num_variables;
    uint32_t n_regs = num_registers_;
    uint32_t total_vars = n_vars * (n_regs + 1); // +1 for spill
    
    LPProblem prob;
    
    // Objective: minimize spill cost
    prob.c = Eigen::VectorXd::Zero(total_vars);
    for (uint32_t v = 0; v < n_vars; ++v) {
        double cost = spill_costs.count(v) ? spill_costs.at(v) : 1.0;
        prob.c(v * (n_regs + 1) + n_regs) = cost; // spill variable
    }
    
    // Constraints:
    // 1. Each variable assigned to exactly one register or spilled
    // 2. Interfering variables can't use same register
    
    std::vector<Eigen::Triplet<double>> triplets;
    std::vector<double> b_values;
    uint32_t constraint_idx = 0;
    
    // Constraint 1: sum_r x[v,r] = 1 for all v
    for (uint32_t v = 0; v < n_vars; ++v) {
        for (uint32_t r = 0; r <= n_regs; ++r) {
            triplets.push_back({static_cast<int>(constraint_idx), 
                               static_cast<int>(v * (n_regs + 1) + r), 1.0});
        }
        b_values.push_back(1.0);
        constraint_idx++;
    }
    
    // Constraint 2: x[v1,r] + x[v2,r] <= 1 for interfering v1, v2
    // (relaxed as equality with slack for LP)
    for (const auto& [v1, neighbors] : graph.edges) {
        for (uint32_t v2 : neighbors) {
            if (v1 < v2) { // avoid duplicates
                for (uint32_t r = 0; r < n_regs; ++r) {
                    triplets.push_back({static_cast<int>(constraint_idx), 
                                       static_cast<int>(v1 * (n_regs + 1) + r), 1.0});
                    triplets.push_back({static_cast<int>(constraint_idx), 
                                       static_cast<int>(v2 * (n_regs + 1) + r), 1.0});
                    b_values.push_back(1.0); // <= 1, but we'll handle as bound
                    constraint_idx++;
                }
            }
        }
    }
    
    prob.A.resize(constraint_idx, total_vars);
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob.b.resize(constraint_idx);
    for (size_t i = 0; i < b_values.size(); ++i) {
        prob.b(i) = b_values[i];
    }
    
    prob.lower_bound = Eigen::VectorXd::Zero(total_vars);
    prob.upper_bound = Eigen::VectorXd::Ones(total_vars);
    
    return prob;
}

RegisterAllocation GraphColoringAllocator::allocate_optimal(
    const ControlFlowGraph& cfg,
    const LivenessInfo& liveness,
    const InterferenceGraph& graph
) {
    // Compute spill costs
    auto spill_costs = compute_spill_costs(cfg, liveness);
    
    // Formulate as IP
    auto ip_problem = formulate_ip(graph, spill_costs);
    
    // Solve with interior point (LP relaxation for now)
    InteriorPointSolver solver;
    solver.set_max_iterations(100);
    solver.set_tolerance(1e-6);
    
    auto lp_solution = solver.solve(ip_problem);
    
    // Round fractional solution to integer
    // (Simple rounding - real implementation would use branch-and-bound)
    RegisterAllocation result;
    result.total_cost = lp_solution.objective;
    result.num_spills = 0;
    
    uint32_t n_regs = num_registers_;
    for (uint32_t v = 0; v < graph.num_variables; ++v) {
        // Find register with highest probability
        int32_t best_reg = -1;
        double best_val = 0.0;
        
        for (uint32_t r = 0; r <= n_regs; ++r) {
            double val = lp_solution.x(v * (n_regs + 1) + r);
            if (val > best_val) {
                best_val = val;
                best_reg = (r == n_regs) ? -1 : r;
            }
        }
        
        result.assignment[v] = best_reg;
        if (best_reg == -1) {
            result.num_spills++;
            result.spilled_vars.push_back(v);
        }
    }
    
    return result;
}

std::unordered_map<uint32_t, double> GraphColoringAllocator::compute_spill_costs(
    const ControlFlowGraph& cfg,
    const LivenessInfo& liveness
) {
    std::unordered_map<uint32_t, double> costs;
    
    // Simple cost model: cost = def_use_distance
    // More sophisticated: weight by loop nesting depth
    for (const auto& range : liveness.ranges) {
        double cost = double(range.end - range.start + 1);
        costs[range.var_id] = cost;
    }
    
    return costs;
}

} // namespace optreg
