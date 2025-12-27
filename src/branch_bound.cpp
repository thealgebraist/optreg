#include "branch_bound.h"
#include <limits>
#include <cmath>
#include <iostream>
#include <chrono>
#include <algorithm>
#include <vector>

namespace optreg {

// Stubs to be replaced
IPSolution BranchAndBound::solve(const LPProblem& problem) {
    IPSolution best_sol;
    best_sol.objective = std::numeric_limits<double>::infinity();
    best_sol.optimal = false;
    best_sol.nodes_explored = 0;
    best_sol.nodes_pruned = 0;

    std::priority_queue<BBNode> queue;

    BBNode root;
    root.depth = 0;
    root.fixed_constraints = {};
    root.lp_solution = solve_lp_relaxation(problem, root.fixed_constraints);
    
    if (root.lp_solution.optimal) {
        root.lower_bound = root.lp_solution.objective;
        queue.push(root);
    } else {
        std::cerr << "B&B: Root relaxation failed to converge (status=" << root.lp_solution.optimal << ")\n";
        return best_sol;
    }

    auto last_bb_print_time = std::chrono::steady_clock::now();

    while (!queue.empty()) {
        if (best_sol.nodes_explored >= max_nodes_) break;
        
        // Stats printing 2Hz
        auto now = std::chrono::steady_clock::now();
        if (std::chrono::duration_cast<std::chrono::milliseconds>(now - last_bb_print_time).count() >= 500) {
             std::cout << "B&B Nodes: " << best_sol.nodes_explored << "/" << max_nodes_ 
                       << " Depth: " << (queue.empty() ? 0 : queue.top().depth) 
                       << " Queue: " << queue.size()
                       << " Best: " << (best_sol.optimal ? std::to_string(best_sol.objective) : "inf") 
                       << "\r" << std::flush;
             last_bb_print_time = now;
        }


        BBNode node = queue.top();
        queue.pop();
        best_sol.nodes_explored++;

        if (should_prune(node.lower_bound, best_sol.objective)) {
            best_sol.nodes_pruned++;
            continue;
        }

        if (is_integer_solution(node.lp_solution.x)) {
            if (node.lp_solution.objective < best_sol.objective - 1e-6) {
                best_sol.x = node.lp_solution.x;
                best_sol.objective = node.lp_solution.objective;
                best_sol.optimal = true;
            }
            continue;
        }

        uint32_t var_idx = select_branching_var(node.lp_solution.x);
        if (var_idx == UINT32_MAX) continue; 
        
        BBNode child0 = node;
        child0.depth++;
        child0.fixed_constraints.push_back({var_idx, 0.0});
        child0.lp_solution = solve_lp_relaxation(problem, child0.fixed_constraints);
        if (child0.lp_solution.optimal) {
            child0.lower_bound = child0.lp_solution.objective;
            if (!should_prune(child0.lower_bound, best_sol.objective)) queue.push(child0);
            else best_sol.nodes_pruned++;
        }

        BBNode child1 = node;
        child1.depth++;
        child1.fixed_constraints.push_back({var_idx, 1.0});
        child1.lp_solution = solve_lp_relaxation(problem, child1.fixed_constraints);
        if (child1.lp_solution.optimal) {
            child1.lower_bound = child1.lp_solution.objective;
            if (!should_prune(child1.lower_bound, best_sol.objective)) queue.push(child1);
            else best_sol.nodes_pruned++;
        }
    }
    return best_sol;
}

LPSolution BranchAndBound::solve_lp_relaxation(
    const LPProblem& problem,
    const std::vector<std::pair<uint32_t, double>>& fixed_vars
) {
    LPProblem new_prob = problem;
    if (!fixed_vars.empty()) {
        uint32_t n = problem.c.size();
        uint32_t m_orig = problem.b.size();
        uint32_t k = fixed_vars.size();
        
        new_prob.b.conservativeResize(m_orig + k);
        std::vector<Eigen::Triplet<double>> triplets;
        
        for (int i=0; i < new_prob.A.outerSize(); ++i) {
            for (Eigen::SparseMatrix<double>::InnerIterator it(new_prob.A, i); it; ++it) {
                triplets.push_back({static_cast<int>(it.row()), static_cast<int>(it.col()), it.value()});
            }
        }
        
        for (size_t i = 0; i < fixed_vars.size(); ++i) {
            triplets.push_back({static_cast<int>(m_orig + i), static_cast<int>(fixed_vars[i].first), 1.0});
            new_prob.b(m_orig + i) = fixed_vars[i].second;
        }
        
        new_prob.A.resize(m_orig + k, n);
        new_prob.A.setFromTriplets(triplets.begin(), triplets.end());
    }
    
    InteriorPointSolver solver;
    solver.set_max_iterations(500); 
    solver.set_tolerance(1e-4);
    solver.set_verbose(true);
    solver.set_linear_solver_backend(linear_backend_);
    return solver.solve(new_prob);
}

uint32_t BranchAndBound::select_branching_var(const Vector& x) {
    uint32_t best_var = UINT32_MAX;
    double max_fractionality = -1.0;
    
    uint32_t n_check = (num_integer_vars_ == UINT32_MAX) ? x.size() : num_integer_vars_;
    
    for (uint32_t i = 0; i < n_check; ++i) {
        double val = x(i);
        double frac = std::abs(val - std::round(val));
        if (frac > 1e-4 && frac > max_fractionality) {
             max_fractionality = frac;
             best_var = i;
        }
    }
    return best_var;
}

bool BranchAndBound::is_integer_solution(const Vector& x) {
    uint32_t n_check = (num_integer_vars_ == UINT32_MAX) ? x.size() : num_integer_vars_;
    
    for (uint32_t i = 0; i < n_check; ++i) {
        if (std::abs(x(i) - std::round(x(i))) > 1e-4) return false;
    }
    return true;
}

bool BranchAndBound::should_prune(double node_bound, double incumbent) {
    return node_bound >= incumbent - tolerance_; 
}

}
