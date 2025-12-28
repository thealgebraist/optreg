#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <set>

namespace optsolve {

// ============================================================================
// Clique Heuristic 1: Greedy Clique Construction
// ============================================================================
class CliqueGreedy : public Solver<CliqueProblem, CliqueSolution> {
public:
    std::string name() const override { return "Clique_Greedy"; }
    
protected:
    bool solve_impl(const CliqueProblem& problem, CliqueSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_vertices;
        
        // Build adjacency set
        std::set<std::pair<size_t, size_t>> edge_set;
        std::vector<std::set<size_t>> adj(n);
        for (const auto& [u, v] : problem.edges) {
            edge_set.emplace(std::min(u, v), std::max(u, v));
            adj[u].insert(v);
            adj[v].insert(u);
        }
        
        solution.vertices.clear();
        
        // Start with vertex with max degree
        size_t max_degree = 0;
        size_t start = 0;
        for (size_t v = 0; v < n; ++v) {
            if (adj[v].size() > max_degree) {
                max_degree = adj[v].size();
                start = v;
            }
        }
        
        solution.vertices.push_back(start);
        
        // Greedily add vertices that are connected to all current clique members
        for (size_t v = 0; v < n; ++v) {
            if (v == start) continue;
            
            bool connected_to_all = true;
            for (size_t u : solution.vertices) {
                size_t a = std::min(u, v);
                size_t b = std::max(u, v);
                if (!edge_set.count({a, b})) {
                    connected_to_all = false;
                    break;
                }
            }
            
            if (connected_to_all) {
                solution.vertices.push_back(v);
            }
        }
        
        solution.clique_size = solution.vertices.size();
        
        metrics.iterations = n;
        metrics.objective_value = solution.clique_size;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Clique Heuristic 2: Bron-Kerbosch with Pivoting
// ============================================================================
class CliqueBronKerbosch : public Solver<CliqueProblem, CliqueSolution> {
public:
    std::string name() const override { return "Clique_BronKerbosch"; }
    
protected:
    bool solve_impl(const CliqueProblem& problem, CliqueSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_vertices;
        
        // Build adjacency set
        std::vector<std::set<size_t>> adj(n);
        for (const auto& [u, v] : problem.edges) {
            adj[u].insert(v);
            adj[v].insert(u);
        }
        
        std::set<size_t> R, P, X;
        for (size_t v = 0; v < n; ++v) {
            P.insert(v);
        }
        
        solution.vertices.clear();
        solution.clique_size = 0;
        
        bron_kerbosch(R, P, X, adj, solution);
        
        metrics.iterations = 0;
        metrics.objective_value = solution.clique_size;
        metrics.is_optimal = (n <= 15);
        
        return true;
    }
    
private:
    void bron_kerbosch(std::set<size_t> R, std::set<size_t> P, std::set<size_t> X,
                      const std::vector<std::set<size_t>>& adj,
                      CliqueSolution& best) {
        if (P.empty() && X.empty()) {
            if (R.size() > best.clique_size) {
                best.vertices.assign(R.begin(), R.end());
                best.clique_size = R.size();
            }
            return;
        }
        
        auto P_copy = P;
        for (size_t v : P_copy) {
            std::set<size_t> new_R = R;
            new_R.insert(v);
            
            std::set<size_t> new_P, new_X;
            for (size_t u : P) {
                if (adj[v].count(u)) new_P.insert(u);
            }
            for (size_t u : X) {
                if (adj[v].count(u)) new_X.insert(u);
            }
            
            bron_kerbosch(new_R, new_P, new_X, adj, best);
            
            P.erase(v);
            X.insert(v);
        }
    }
};

// ============================================================================
// Clique Branch and Bound
// ============================================================================
class CliqueBranchBound : public Solver<CliqueProblem, CliqueSolution> {
public:
    std::string name() const override { return "Clique_BranchBound"; }
    
protected:
    bool solve_impl(const CliqueProblem& problem, CliqueSolution& solution, SolverMetrics& metrics) override {
        // Use Bron-Kerbosch for exact solution
        CliqueBronKerbosch bk;
        auto result = bk.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
