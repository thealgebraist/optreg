#include "graph_coloring.h"
#include "interior_point.h"
#include "gradient_descent.h"
#include "branch_bound.h"
#include <limits>

namespace optreg {

// Formulate graph coloring as integer program
LPProblem GraphColoringAllocator::formulate_ip(
    const InterferenceGraph& graph,
    const std::unordered_map<uint32_t, double>& spill_costs
) {
    uint32_t n_vars = graph.num_variables;
    uint32_t n_regs = num_registers_;
    uint32_t n_edges = 0;
    for (const auto& [v1, neighbors] : graph.edges) {
        for (uint32_t v2 : neighbors) {
            if (v1 < v2) n_edges++;
        }
    }

    uint32_t original_vars = n_vars * (n_regs + 1);
    uint32_t n_slacks = n_edges * n_regs;
    uint32_t total_vars = original_vars + n_slacks;
    
    LPProblem prob;
    
    // Objective: minimize spill cost
    prob.c = Eigen::VectorXd::Zero(total_vars);
    for (uint32_t v = 0; v < n_vars; ++v) {
        double cost = spill_costs.count(v) ? spill_costs.at(v) : 1.0;
        prob.c(v * (n_regs + 1) + n_regs) = cost; // spill variable
    }
    // Slack variables have 0 cost
    
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
    
    // Constraint 2: x[v1,r] + x[v2,r] + slack = 1 for interfering v1, v2
    uint32_t slack_idx = original_vars;
    for (const auto& [v1, neighbors] : graph.edges) {
        for (uint32_t v2 : neighbors) {
            if (v1 < v2) {
                for (uint32_t r = 0; r < n_regs; ++r) {
                    triplets.push_back({static_cast<int>(constraint_idx), 
                                       static_cast<int>(v1 * (n_regs + 1) + r), 1.0});
                    triplets.push_back({static_cast<int>(constraint_idx), 
                                       static_cast<int>(v2 * (n_regs + 1) + r), 1.0});
                    // Add slack variable
                    triplets.push_back({static_cast<int>(constraint_idx), 
                                       static_cast<int>(slack_idx), 1.0});
                    
                    b_values.push_back(1.0);
                    constraint_idx++;
                    slack_idx++;
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

#include "branch_bound.h"

// ... (includes already there, I just need to add branch_bound.h) -> handled by manual addition or broad replace?
// I'll assume I replace the allocate_optimal function and rely on careful include add.

RegisterAllocation GraphColoringAllocator::allocate_optimal(
    const ControlFlowGraph& cfg,
    const LivenessInfo& liveness,
    const InterferenceGraph& graph,
    SolverType solver_type
) {
    // Compute spill costs
    auto spill_costs = compute_spill_costs(cfg, liveness);
    
    // Formulate as IP
    auto ip_problem = formulate_ip(graph, spill_costs);
    
    IPSolution ip_solution;
    
    // Check if it is a Newton-based solver
    bool is_newton = (solver_type == SolverType::Newton || 
                      solver_type == SolverType::Newton_AMX || 
                      solver_type == SolverType::Newton_Sparse || 
                      solver_type == SolverType::Newton_Dense);

    if (is_newton) {
        // Solve with Branch & Bound (Integer Programming) for TRUE optimality
        BranchAndBound solver;
        solver.set_max_nodes(1000); // 1000 nodes limit
        solver.set_tolerance(1e-6);
        
        // Configure backend
        if (solver_type == SolverType::Newton_AMX) 
            solver.set_linear_solver_backend(BranchAndBound::LinearBackend::AMX);
        else if (solver_type == SolverType::Newton_AMXDense)
            solver.set_linear_solver_backend(BranchAndBound::LinearBackend::AMXDense);
        else if (solver_type == SolverType::Newton_Sparse) 
            solver.set_linear_solver_backend(BranchAndBound::LinearBackend::EigenSparse);
        else if (solver_type == SolverType::Newton_Dense) 
            solver.set_linear_solver_backend(BranchAndBound::LinearBackend::EigenDense);
        else 
            solver.set_linear_solver_backend(BranchAndBound::LinearBackend::Auto);

        ip_solution = solver.solve(ip_problem);
    } else {
        // Solve with Gradient Descent (LP Relaxation)
        GradientDescentSolver solver;
        solver.set_max_iters(500);
        solver.set_rho(50.0);
        LPSolution lp_sol = solver.solve(ip_problem);
        
        // Wrap GD result into IPSolution
        ip_solution.x = lp_sol.x;
        ip_solution.objective = lp_sol.objective;
        ip_solution.optimal = lp_sol.optimal;
        // ip_solution.nodes_explored = lp_sol.iterations; // Mapping iters to nodes for stats
    }
    
    // Extract solution
    if (!ip_solution.optimal && ip_solution.x.size() == 0) {
        RegisterAllocation result;
        result.num_spills = 0; // Empty
        return result;
    }
    
    return extract_solution(ip_solution, graph);
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


RegisterAllocation GraphColoringAllocator::extract_solution(
    const IPSolution& ip_solution,
    const InterferenceGraph& graph
) {
    RegisterAllocation result;
    result.total_cost = ip_solution.objective;
    result.num_spills = 0;
    
    uint32_t n_regs = num_registers_;
    uint32_t n_vars = graph.num_variables;
    
    // Safety check for dimension
    if (ip_solution.x.size() != n_vars * (n_regs + 1)) {
        return result; 
    }

    for (uint32_t v = 0; v < n_vars; ++v) {
        int32_t best_reg = -1;
        double best_val = -1.0;
        
        for (uint32_t r = 0; r <= n_regs; ++r) {
            uint32_t idx = v * (n_regs + 1) + r;
            if (idx < ip_solution.x.size()) {
                double val = ip_solution.x(idx);
                if (val > best_val) {
                    best_val = val;
                    best_reg = (r == n_regs) ? -1 : static_cast<int32_t>(r);
                }
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

} // namespace optreg
