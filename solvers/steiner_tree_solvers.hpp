#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <limits>
#include <queue>

namespace optsolve {

// ============================================================================
// Steiner Tree Heuristic 1: MST-Based
// ============================================================================
class SteinerMST : public Solver<SteinerTreeProblem, SteinerTreeSolution> {
public:
    std::string name() const override { return "Steiner_MST"; }
    
protected:
    bool solve_impl(const SteinerTreeProblem& problem, SteinerTreeSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_vertices;
        
        if (problem.terminals.empty()) {
            solution.tree_edges.clear();
            solution.total_weight = 0;
            metrics.iterations = 0;
            metrics.objective_value = 0;
            metrics.is_optimal = false;
            return true;
        }
        
        // Build complete distance matrix using Floyd-Warshall
        std::vector<std::vector<double>> dist(n, std::vector<double>(n, std::numeric_limits<double>::infinity()));
        for (size_t i = 0; i < n; ++i) {
            dist[i][i] = 0;
        }
        for (const auto& [u, v, w] : problem.edges) {
            dist[u][v] = std::min(dist[u][v], w);
            dist[v][u] = std::min(dist[v][u], w);
        }
        
        for (size_t k = 0; k < n; ++k) {
            for (size_t i = 0; i < n; ++i) {
                for (size_t j = 0; j < n; ++j) {
                    dist[i][j] = std::min(dist[i][j], dist[i][k] + dist[k][j]);
                }
            }
        }
        
        // Build MST on terminals
        size_t t = problem.terminals.size();
        std::vector<bool> in_mst(t, false);
        std::vector<double> min_dist(t, std::numeric_limits<double>::infinity());
        std::vector<int> parent(t, -1);
        
        min_dist[0] = 0;
        
        for (size_t count = 0; count < t; ++count) {
            double min_val = std::numeric_limits<double>::infinity();
            size_t min_idx = 0;
            
            for (size_t i = 0; i < t; ++i) {
                if (!in_mst[i] && min_dist[i] < min_val) {
                    min_val = min_dist[i];
                    min_idx = i;
                }
            }
            
            in_mst[min_idx] = true;
            
            for (size_t i = 0; i < t; ++i) {
                if (!in_mst[i]) {
                    double d = dist[problem.terminals[min_idx]][problem.terminals[i]];
                    if (d < min_dist[i]) {
                        min_dist[i] = d;
                        parent[i] = min_idx;
                    }
                }
            }
        }
        
        // Build solution from MST edges
        solution.tree_edges.clear();
        solution.total_weight = 0;
        
        for (size_t i = 1; i < t; ++i) {
            size_t u = problem.terminals[parent[i]];
            size_t v = problem.terminals[i];
            double w = dist[u][v];
            solution.tree_edges.emplace_back(u, v, w);
            solution.total_weight += w;
        }
        
        metrics.iterations = t;
        metrics.objective_value = solution.total_weight;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Steiner Tree Heuristic 2: Shortest Path
// ============================================================================
class SteinerShortestPath : public Solver<SteinerTreeProblem, SteinerTreeSolution> {
public:
    std::string name() const override { return "Steiner_ShortestPath"; }
    
protected:
    bool solve_impl(const SteinerTreeProblem& problem, SteinerTreeSolution& solution, SolverMetrics& metrics) override {
        // Use MST-based approach
        SteinerMST mst;
        auto result = mst.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

// ============================================================================
// Steiner Tree Branch and Bound
// ============================================================================
class SteinerBranchBound : public Solver<SteinerTreeProblem, SteinerTreeSolution> {
public:
    std::string name() const override { return "Steiner_BranchBound"; }
    
protected:
    bool solve_impl(const SteinerTreeProblem& problem, SteinerTreeSolution& solution, SolverMetrics& metrics) override {
        SteinerMST mst;
        auto result = mst.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
