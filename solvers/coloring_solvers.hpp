#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <set>

namespace optsolve {

// ============================================================================
// Graph Coloring Heuristic 1: Greedy Sequential
// ============================================================================
class ColoringGreedy : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Coloring_Greedy"; }
    
protected:
    bool solve_impl(const GraphColoringProblem& problem, GraphColoringSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_vertices;
        solution.colors.assign(n, 0);
        
        // Build adjacency list
        std::vector<std::set<size_t>> adj(n);
        for (const auto& [u, v] : problem.edges) {
            adj[u].insert(v);
            adj[v].insert(u);
        }
        
        for (size_t v = 0; v < n; ++v) {
            std::set<size_t> used_colors;
            for (size_t neighbor : adj[v]) {
                if (neighbor < v) {
                    used_colors.insert(solution.colors[neighbor]);
                }
            }
            
            size_t color = 0;
            while (used_colors.count(color)) {
                color++;
            }
            solution.colors[v] = color;
        }
        
        solution.num_colors = *std::max_element(solution.colors.begin(), solution.colors.end()) + 1;
        
        metrics.iterations = n;
        metrics.objective_value = solution.num_colors;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Graph Coloring Heuristic 2: DSATUR
// ============================================================================
class ColoringDSATUR : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Coloring_DSATUR"; }
    
protected:
    bool solve_impl(const GraphColoringProblem& problem, GraphColoringSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_vertices;
        solution.colors.assign(n, 0);
        
        // Build adjacency list
        std::vector<std::set<size_t>> adj(n);
        for (const auto& [u, v] : problem.edges) {
            adj[u].insert(v);
            adj[v].insert(u);
        }
        
        std::vector<bool> colored(n, false);
        std::vector<std::set<size_t>> neighbor_colors(n);
        
        for (size_t step = 0; step < n; ++step) {
            // Find uncolored vertex with max saturation degree
            size_t max_sat = 0;
            size_t max_degree = 0;
            size_t best_v = 0;
            
            for (size_t v = 0; v < n; ++v) {
                if (colored[v]) continue;
                
                size_t sat = neighbor_colors[v].size();
                size_t degree = adj[v].size();
                
                if (sat > max_sat || (sat == max_sat && degree > max_degree)) {
                    max_sat = sat;
                    max_degree = degree;
                    best_v = v;
                }
            }
            
            // Color best_v with smallest available color
            size_t color = 0;
            while (neighbor_colors[best_v].count(color)) {
                color++;
            }
            
            solution.colors[best_v] = color;
            colored[best_v] = true;
            
            // Update neighbor saturation
            for (size_t neighbor : adj[best_v]) {
                neighbor_colors[neighbor].insert(color);
            }
        }
        
        solution.num_colors = *std::max_element(solution.colors.begin(), solution.colors.end()) + 1;
        
        metrics.iterations = n;
        metrics.objective_value = solution.num_colors;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Graph Coloring Branch and Bound
// ============================================================================
class ColoringBranchBound : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Coloring_BranchBound"; }
    
protected:
    bool solve_impl(const GraphColoringProblem& problem, GraphColoringSolution& solution, SolverMetrics& metrics) override {
        // Use DSATUR as good heuristic
        ColoringDSATUR dsatur;
        auto result = dsatur.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
