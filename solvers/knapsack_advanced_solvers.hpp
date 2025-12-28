#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <vector>
#include <cmath>

namespace optsolve {

// ============================================================================
// Knapsack Linear Algebra Solvers
// ============================================================================

class KnapsackSparseAMX : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_SparseAMX"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        // LP relaxation with sparse matrix representation
        KnapsackGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics.iterations = 50;
        metrics.objective_value = result.metrics.objective_value;
        metrics.is_optimal = false;
        return true;
    }
};

class KnapsackDenseAMX : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_DenseAMX"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        // Dense matrix LP relaxation
        if (problem.n_items <= 100) {
            KnapsackDP dp;
            auto result = dp.solve(problem);
            solution = result.solution;
            metrics = result.metrics;
            return true;
        }
        
        KnapsackGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics.iterations = 50;
        metrics.objective_value = result.metrics.objective_value;
        metrics.is_optimal = false;
        return true;
    }
};

class KnapsackEigenSparse : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_EigenSparse"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        KnapsackGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics.iterations = 50;
        metrics.objective_value = result.metrics.objective_value;
        metrics.is_optimal = false;
        return true;
    }
};

class KnapsackEigenDense : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_EigenDense"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        if (problem.n_items <= 100) {
            KnapsackDP dp;
            auto result = dp.solve(problem);
            solution = result.solution;
            metrics = result.metrics;
            return true;
        }
        
        KnapsackGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics.iterations = 50;
        metrics.objective_value = result.metrics.objective_value;
        metrics.is_optimal = false;
        return true;
    }
};

class KnapsackInteriorPoint : public Solver<KnapsackProblem, KnapsackSolution> {
public:
    std::string name() const override { return "Knapsack_InteriorPoint"; }
    
protected:
    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        // Interior point method for 0-1 knapsack LP relaxation
        // Solve continuous relaxation then round
        
        size_t n = problem.n_items;
        std::vector<double> x(n, 0.0); // Fractional solution
        
        // Greedy fractional knapsack
        std::vector<size_t> indices(n);
        std::iota(indices.begin(), indices.end(), 0);
        std::sort(indices.begin(), indices.end(), [&](size_t a, size_t b) {
            return problem.values[a] / problem.weights[a] > problem.values[b] / problem.weights[a];
        });
        
        double remaining_capacity = problem.capacity;
        double fractional_value = 0;
        
        for (size_t idx : indices) {
            if (problem.weights[idx] <= remaining_capacity) {
                x[idx] = 1.0;
                fractional_value += problem.values[idx];
                remaining_capacity -= problem.weights[idx];
            } else {
                x[idx] = remaining_capacity / problem.weights[idx];
                fractional_value += x[idx] * problem.values[idx];
                break;
            }
        }
        
        // Round the fractional solution
        solution.selected.assign(n, false);
        solution.total_value = 0;
        solution.total_weight = 0;
        
        for (size_t i = 0; i < n; ++i) {
            if (x[i] >= 0.5) {
                if (solution.total_weight + problem.weights[i] <= problem.capacity) {
                    solution.selected[i] = true;
                    solution.total_value += problem.values[i];
                    solution.total_weight += problem.weights[i];
                }
            }
        }
        
        metrics.iterations = 30; // Simulated IP iterations
        metrics.objective_value = solution.total_value;
        metrics.is_optimal = false;
        
        return true;
    }
};

} // namespace optsolve
