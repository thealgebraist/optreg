#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <set>

namespace optsolve {

// ============================================================================
// Vertex Cover Heuristic 1: Greedy Edge-Based
// ============================================================================
class VertexCoverGreedy : public Solver<VertexCoverProblem, VertexCoverSolution> {
public:
    std::string name() const override { return "VertexCover_Greedy"; }
    
protected:
    bool solve_impl(const VertexCoverProblem& problem, VertexCoverSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_vertices;
        solution.in_cover.assign(n, false);
        solution.cover_size = 0;
        
        std::set<std::pair<size_t, size_t>> uncovered_edges;
        for (const auto& [u, v] : problem.edges) {
            uncovered_edges.emplace(std::min(u, v), std::max(u, v));
        }
        
        while (!uncovered_edges.empty()) {
            // Count degree for each vertex among uncovered edges
            std::vector<size_t> degree(n, 0);
            for (const auto& [u, v] : uncovered_edges) {
                degree[u]++;
                degree[v]++;
            }
            
            // Pick vertex with max degree
            size_t max_v = 0;
            for (size_t v = 0; v < n; ++v) {
                if (degree[v] > degree[max_v]) {
                    max_v = v;
                }
            }
            
            solution.in_cover[max_v] = true;
            solution.cover_size++;
            
            // Remove edges incident to max_v
            auto it = uncovered_edges.begin();
            while (it != uncovered_edges.end()) {
                if (it->first == max_v || it->second == max_v) {
                    it = uncovered_edges.erase(it);
                } else {
                    ++it;
                }
            }
        }
        
        metrics.iterations = solution.cover_size;
        metrics.objective_value = solution.cover_size;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Vertex Cover Heuristic 2: 2-Approximation
// ============================================================================
class VertexCover2Approx : public Solver<VertexCoverProblem, VertexCoverSolution> {
public:
    std::string name() const override { return "VertexCover_2Approx"; }
    
protected:
    bool solve_impl(const VertexCoverProblem& problem, VertexCoverSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_vertices;
        solution.in_cover.assign(n, false);
        solution.cover_size = 0;
        
        std::set<std::pair<size_t, size_t>> uncovered_edges;
        for (const auto& [u, v] : problem.edges) {
            uncovered_edges.emplace(std::min(u, v), std::max(u, v));
        }
        
        while (!uncovered_edges.empty()) {
            // Pick arbitrary edge
            auto edge = *uncovered_edges.begin();
            size_t u = edge.first;
            size_t v = edge.second;
            
            // Add both endpoints to cover
            solution.in_cover[u] = true;
            solution.in_cover[v] = true;
            solution.cover_size += 2;
            
            // Remove all edges incident to u or v
            auto it = uncovered_edges.begin();
            while (it != uncovered_edges.end()) {
                if (it->first == u || it->second == u || it->first == v || it->second == v) {
                    it = uncovered_edges.erase(it);
                } else {
                    ++it;
                }
            }
        }
        
        metrics.iterations = solution.cover_size / 2;
        metrics.objective_value = solution.cover_size;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Vertex Cover Branch and Bound
// ============================================================================
class VertexCoverBranchBound : public Solver<VertexCoverProblem, VertexCoverSolution> {
public:
    std::string name() const override { return "VertexCover_BranchBound"; }
    
protected:
    bool solve_impl(const VertexCoverProblem& problem, VertexCoverSolution& solution, SolverMetrics& metrics) override {
        // Use greedy for approximation
        VertexCoverGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
