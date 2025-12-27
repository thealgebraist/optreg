#include "global_allocator.h"
#include "live_range.h"
#include "interior_point.h"
#include <algorithm>
#include <queue>

namespace optreg {

GlobalInterferenceGraph GlobalRegisterAllocator::build_global_graph(
    const GlobalCFG& cfg
) {
    GlobalInterferenceGraph global_graph;
    global_graph.num_variables = 0;
    
    // Build per-function interference graphs and merge
    uint32_t var_offset = 0;
    
    for (uint32_t func_idx = 0; func_idx < cfg.functions.size(); ++func_idx) {
        const auto& func = cfg.functions[func_idx];
        
        // Compute liveness for this function
        auto liveness = compute_liveness(func);
        
        // Build local interference graph
        auto local_graph = build_interference_graph(liveness, func);
        
        // Merge into global graph with offset
        for (const auto& [v, neighbors] : local_graph.edges) {
            uint32_t global_v = v + var_offset;
            global_graph.var_to_function[global_v] = func_idx;
            
            for (uint32_t n : neighbors) {
                uint32_t global_n = n + var_offset;
                global_graph.edges[global_v].insert(global_n);
                global_graph.degree[global_v]++;
            }
        }
        
        var_offset += func.variables.size();
    }
    
    global_graph.num_variables = var_offset;
    
    // Add interference edges for variables live across calls
    for (const auto& call : cfg.call_sites) {
        // All variables live at call interfere with each other
        // (simplified - real implementation would check calling convention)
        for (size_t i = 0; i < call.live_at_call.size(); ++i) {
            for (size_t j = i + 1; j < call.live_at_call.size(); ++j) {
                uint32_t v1 = call.live_at_call[i];
                uint32_t v2 = call.live_at_call[j];
                
                if (global_graph.edges[v1].insert(v2).second) {
                    global_graph.degree[v1]++;
                }
                if (global_graph.edges[v2].insert(v1).second) {
                    global_graph.degree[v2]++;
                }
            }
        }
    }
    
    return global_graph;
}

double GlobalRegisterAllocator::compute_priority(
    uint32_t var,
    const GlobalCFG& cfg,
    const GlobalInterferenceGraph& graph
) {
    double priority = 0.0;
    
    // Factor 1: Interference degree (higher degree = higher priority)
    uint32_t degree = graph.degree.count(var) ? graph.degree.at(var) : 0;
    priority += degree * 10.0;
    
    // Factor 2: Is it live across a call? (much higher priority)
    for (const auto& call : cfg.call_sites) {
        if (std::find(call.live_at_call.begin(), call.live_at_call.end(), var) 
            != call.live_at_call.end()) {
            priority += 1000.0;  // Very high priority - avoid spilling these
        }
    }
    
    // Factor 3: Is it constrained to a specific register? (highest priority)
    if (graph.required_registers.count(var)) {
        priority += 10000.0;
    }
    
    return priority;
}

RegisterAllocation GlobalRegisterAllocator::allocate_heuristic_global(
    const GlobalCFG& cfg,
    const GlobalInterferenceGraph& graph
) {
    RegisterAllocation result;
    result.num_spills = 0;
    
    // Priority queue: (priority, variable_id)
    using PriorityVar = std::pair<double, uint32_t>;
    std::priority_queue<PriorityVar> pq;
    
    // Compute priorities
    for (uint32_t v = 0; v < graph.num_variables; ++v) {
        double pri = compute_priority(v, cfg, graph);
        pq.push({pri, v});
    }
    
    // Greedy coloring with priorities
    std::vector<int32_t> color(graph.num_variables, -1);
    
    while (!pq.empty()) {
        auto [pri, v] = pq.top();
        pq.pop();
        
        // Check if constrained to specific register
        if (graph.required_registers.count(v)) {
            uint32_t req_reg = graph.required_registers.at(v);
            color[v] = req_reg;
            result.assignment[v] = req_reg;
            continue;
        }
        
        // Find smallest color not used by neighbors
        std::vector<bool> used(num_registers_ + 1, false);
        
        const auto& neighbors = graph.edges.count(v) ? 
            graph.edges.at(v) : std::unordered_set<uint32_t>{};
        
        for (uint32_t n : neighbors) {
            if (color[n] >= 0 && color[n] < static_cast<int32_t>(num_registers_)) {
                used[color[n]] = true;
            }
        }
        
        // Assign color
        int32_t assigned = -1;
        for (uint32_t c = 0; c < num_registers_; ++c) {
            if (!used[c]) {
                assigned = c;
                break;
            }
        }
        
        color[v] = assigned;
        result.assignment[v] = assigned;
        
        if (assigned == -1) {
            result.num_spills++;
            result.spilled_vars.push_back(v);
        }
    }
    
    return result;
}

LPProblem GlobalRegisterAllocator::formulate_global_ip(
    const GlobalCFG& cfg,
    const GlobalInterferenceGraph& graph
) {
    // Similar to local IP but with additional constraints:
    // 1. Calling convention (some vars must use caller/callee-saved regs)
    // 2. Cross-call consistency (minimize register shuffling at calls)
    // 3. Spill cost weighted by call frequency
    
    uint32_t n_vars = graph.num_variables;
    uint32_t n_regs = num_registers_;
    uint32_t total_vars = n_vars * (n_regs + 1);
    
    LPProblem prob;
    prob.c = Eigen::VectorXd::Zero(total_vars);
    
    // Objective: minimize spills weighted by call pressure
    for (uint32_t v = 0; v < n_vars; ++v) {
        double spill_cost = 1.0;
        
        // Higher cost for variables live across calls
        for (const auto& call : cfg.call_sites) {
            if (std::find(call.live_at_call.begin(), call.live_at_call.end(), v)
                != call.live_at_call.end()) {
                spill_cost *= 10.0;  // 10x cost for call-spanning vars
            }
        }
        
        prob.c(v * (n_regs + 1) + n_regs) = spill_cost;
    }
    
    // Constraints (same as local but with calling convention added)
    std::vector<Eigen::Triplet<double>> triplets;
    std::vector<double> b_values;
    uint32_t constraint_idx = 0;
    
    // Constraint 1: Each variable assigned exactly once
    for (uint32_t v = 0; v < n_vars; ++v) {
        for (uint32_t r = 0; r <= n_regs; ++r) {
            triplets.push_back({static_cast<int>(constraint_idx),
                               static_cast<int>(v * (n_regs + 1) + r), 1.0});
        }
        b_values.push_back(1.0);
        constraint_idx++;
    }
    
    // Constraint 2: Interfering variables different registers
    for (const auto& [v1, neighbors] : graph.edges) {
        for (uint32_t v2 : neighbors) {
            if (v1 < v2) {
                for (uint32_t r = 0; r < n_regs; ++r) {
                    triplets.push_back({static_cast<int>(constraint_idx),
                                       static_cast<int>(v1 * (n_regs + 1) + r), 1.0});
                    triplets.push_back({static_cast<int>(constraint_idx),
                                       static_cast<int>(v2 * (n_regs + 1) + r), 1.0});
                    b_values.push_back(1.0);
                    constraint_idx++;
                }
            }
        }
    }
    
    // Constraint 3: Required register assignments
    for (const auto& [v, req_reg] : graph.required_registers) {
        // Force x[v, req_reg] = 1
        triplets.push_back({static_cast<int>(constraint_idx),
                           static_cast<int>(v * (n_regs + 1) + req_reg), 1.0});
        b_values.push_back(1.0);
        constraint_idx++;
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

RegisterAllocation GlobalRegisterAllocator::allocate_optimal_global(
    const GlobalCFG& cfg,
    const GlobalInterferenceGraph& graph,
    GraphColoringAllocator::SolverType solver_type
) {
    auto ip_problem = formulate_global_ip(cfg, graph);
    
    InteriorPointSolver solver;
    solver.set_max_iterations(500);  // More iterations for global
    solver.set_tolerance(1e-6);

    // Backend configuration
    if (solver_type == GraphColoringAllocator::SolverType::Newton_AMX) 
        solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::AMX);
    else if (solver_type == GraphColoringAllocator::SolverType::Newton_Sparse) 
        solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::EigenSparse);
    else if (solver_type == GraphColoringAllocator::SolverType::Newton_Dense) 
        solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::EigenDense);
    else 
        solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::Auto);
    
    auto lp_solution = solver.solve(ip_problem);
    
    RegisterAllocation result;
    result.num_spills = 0;
    
    uint32_t expected_size = graph.num_variables * (num_registers_ + 1);
    if (!lp_solution.optimal || lp_solution.x.size() != expected_size) {
        return result;  // Failed
    }
    
    result.total_cost = lp_solution.objective;
    
    // Round to integer solution
    for (uint32_t v = 0; v < graph.num_variables; ++v) {
        int32_t best_reg = -1;
        double best_val = 0.0;
        
        for (uint32_t r = 0; r <= num_registers_; ++r) {
            uint32_t idx = v * (num_registers_ + 1) + r;
            if (idx >= lp_solution.x.size()) break;
            
            double val = lp_solution.x(idx);
            if (val > best_val) {
                best_val = val;
                best_reg = (r == num_registers_) ? -1 : r;
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
