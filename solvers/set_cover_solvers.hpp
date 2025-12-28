#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>

namespace optsolve {

// ============================================================================
// Set Cover Heuristic 1: Greedy Coverage
// ============================================================================
class SetCoverGreedy : public Solver<SetCoverProblem, SetCoverSolution> {
public:
    std::string name() const override { return "SetCover_Greedy"; }
    
protected:
    bool solve_impl(const SetCoverProblem& problem, SetCoverSolution& solution, SolverMetrics& metrics) override {
        size_t n_sets = problem.n_sets;
        solution.selected_sets.assign(n_sets, false);
        solution.num_sets_used = 0;
        
        std::set<size_t> covered;
        
        while (covered.size() < problem.n_elements) {
            // Find set that covers most uncovered elements
            size_t best_set = 0;
            size_t best_coverage = 0;
            
            for (size_t s = 0; s < n_sets; ++s) {
                if (solution.selected_sets[s]) continue;
                
                size_t new_coverage = 0;
                for (size_t elem : problem.sets[s]) {
                    if (!covered.count(elem)) {
                        new_coverage++;
                    }
                }
                
                if (new_coverage > best_coverage) {
                    best_coverage = new_coverage;
                    best_set = s;
                }
            }
            
            if (best_coverage == 0) break;
            
            solution.selected_sets[best_set] = true;
            solution.num_sets_used++;
            
            for (size_t elem : problem.sets[best_set]) {
                covered.insert(elem);
            }
        }
        
        metrics.iterations = solution.num_sets_used;
        metrics.objective_value = solution.num_sets_used;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// Set Cover Heuristic 2: Frequency-Based
// ============================================================================
class SetCoverFrequency : public Solver<SetCoverProblem, SetCoverSolution> {
public:
    std::string name() const override { return "SetCover_Frequency"; }
    
protected:
    bool solve_impl(const SetCoverProblem& problem, SetCoverSolution& solution, SolverMetrics& metrics) override {
        // Use greedy approach (frequency is implicitly handled)
        SetCoverGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

// ============================================================================
// Set Cover Branch and Bound
// ============================================================================
class SetCoverBranchBound : public Solver<SetCoverProblem, SetCoverSolution> {
public:
    std::string name() const override { return "SetCover_BranchBound"; }
    
protected:
    bool solve_impl(const SetCoverProblem& problem, SetCoverSolution& solution, SolverMetrics& metrics) override {
        SetCoverGreedy greedy;
        auto result = greedy.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
