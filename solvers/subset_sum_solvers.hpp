#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <unordered_map>

namespace optsolve {

// ============================================================================
// Subset Sum Heuristic 1: Greedy
// ============================================================================
class SubsetSumGreedy : public Solver<SubsetSumProblem, SubsetSumSolution> {
public:
    std::string name() const override { return "SubsetSum_Greedy"; }
    
protected:
    bool solve_impl(const SubsetSumProblem& problem, SubsetSumSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.numbers.size();
        
        // Sort indices by value descending
        std::vector<size_t> indices(n);
        std::iota(indices.begin(), indices.end(), 0);
        std::sort(indices.begin(), indices.end(), [&](size_t a, size_t b) {
            return problem.numbers[a] > problem.numbers[b];
        });
        
        solution.selected.assign(n, false);
        solution.sum = 0;
        solution.exists = false;
        
        for (size_t idx : indices) {
            if (solution.sum + problem.numbers[idx] <= problem.target) {
                solution.selected[idx] = true;
                solution.sum += problem.numbers[idx];
                
                if (solution.sum == problem.target) {
                    solution.exists = true;
                    break;
                }
            }
        }
        
        metrics.iterations = n;
        metrics.objective_value = solution.exists ? 1 : 0;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Subset Sum Heuristic 2: Meet-in-the-Middle
// ============================================================================
class SubsetSumMeetMiddle : public Solver<SubsetSumProblem, SubsetSumSolution> {
public:
    std::string name() const override { return "SubsetSum_MeetMiddle"; }
    
protected:
    bool solve_impl(const SubsetSumProblem& problem, SubsetSumSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.numbers.size();
        
        if (n <= 20) {
            size_t mid = n / 2;
            
            // Generate all sums for left half
            std::unordered_map<int, size_t> left_sums;
            for (size_t mask = 0; mask < (1ULL << mid); ++mask) {
                int sum = 0;
                for (size_t i = 0; i < mid; ++i) {
                    if (mask & (1ULL << i)) {
                        sum += problem.numbers[i];
                    }
                }
                left_sums[sum] = mask;
            }
            
            // Try all sums for right half
            size_t right_size = n - mid;
            for (size_t mask = 0; mask < (1ULL << right_size); ++mask) {
                int sum = 0;
                for (size_t i = 0; i < right_size; ++i) {
                    if (mask & (1ULL << i)) {
                        sum += problem.numbers[mid + i];
                    }
                }
                
                int needed = problem.target - sum;
                if (left_sums.count(needed)) {
                    // Found solution
                    solution.selected.assign(n, false);
                    solution.sum = problem.target;
                    solution.exists = true;
                    
                    size_t left_mask = left_sums[needed];
                    for (size_t i = 0; i < mid; ++i) {
                        if (left_mask & (1ULL << i)) {
                            solution.selected[i] = true;
                        }
                    }
                    for (size_t i = 0; i < right_size; ++i) {
                        if (mask & (1ULL << i)) {
                            solution.selected[mid + i] = true;
                        }
                    }
                    
                    metrics.iterations = 0;
                    metrics.objective_value = 1;
                    metrics.is_optimal = true;
                    return true;
                }
            }
        }
        
        // Fall back to greedy if too large
        SubsetSumGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

// ============================================================================
// Subset Sum Branch and Bound
// ============================================================================
class SubsetSumBranchBound : public Solver<SubsetSumProblem, SubsetSumSolution> {
public:
    std::string name() const override { return "SubsetSum_BranchBound"; }
    
protected:
    bool solve_impl(const SubsetSumProblem& problem, SubsetSumSolution& solution, SolverMetrics& metrics) override {
        SubsetSumMeetMiddle mm;
        auto result = mm.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
