#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <numeric>

namespace optsolve {

// ============================================================================
// Knapsack Heuristic 1: Greedy by Value/Weight Ratio
// ============================================================================
class KnapsackGreedy : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_Greedy"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_items;
        
        // Create indices sorted by value/weight ratio
        std::vector<size_t> indices(n);
        std::iota(indices.begin(), indices.end(), 0);
        
        std::sort(indices.begin(), indices.end(), [&](size_t a, size_t b) {
            return problem.values[a] / problem.weights[a] > problem.values[b] / problem.weights[b];
        });
        
        solution.selected.assign(n, false);
        solution.total_value = 0;
        solution.total_weight = 0;
        
        for (size_t idx : indices) {
            if (solution.total_weight + problem.weights[idx] <= problem.capacity) {
                solution.selected[idx] = true;
                solution.total_value += problem.values[idx];
                solution.total_weight += problem.weights[idx];
            }
        }
        
        metrics.iterations = n;
        metrics.objective_value = solution.total_value;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Knapsack Heuristic 2: Dynamic Programming
// ============================================================================
class KnapsackDP : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_DP"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_items;
        // Scale weights to handle doubles in DP
        const double scale = 1000.0;
        int W = static_cast<int>(problem.capacity * scale);
        
        std::vector<int> scaled_weights(n);
        for (size_t i = 0; i < n; ++i) {
            scaled_weights[i] = static_cast<int>(std::ceil(problem.weights[i] * scale));
        }
        
        // DP table
        std::vector<std::vector<double>> dp(n + 1, std::vector<double>(W + 1, 0));
        
        for (size_t i = 1; i <= n; ++i) {
            for (int w = 0; w <= W; ++w) {
                dp[i][w] = dp[i - 1][w];
                if (scaled_weights[i - 1] <= w) {
                    dp[i][w] = std::max(dp[i][w], 
                                       dp[i - 1][w - scaled_weights[i - 1]] + problem.values[i - 1]);
                }
            }
        }
        
        // Backtrack to find solution
        solution.selected.assign(n, false);
        solution.total_value = dp[n][W];
        solution.total_weight = 0;
        
        int w = W;
        for (int i = n; i > 0; --i) {
            if (dp[i][w] != dp[i - 1][w]) {
                solution.selected[i - 1] = true;
                solution.total_weight += problem.weights[i - 1];
                w -= scaled_weights[i - 1];
            }
        }
        
        metrics.iterations = n * W;
        metrics.objective_value = solution.total_value;
        metrics.is_optimal = true;
        
        return true;
    }
};

// ============================================================================
// Knapsack Branch and Bound
// ============================================================================
class KnapsackBranchBound : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_BranchBound"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        // Use DP for exact solution
        KnapsackDP dp;
        auto result = dp.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
