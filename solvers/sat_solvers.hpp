#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <random>

namespace optsolve {

// ============================================================================
// SAT Heuristic 1: DPLL (Davis-Putnam-Logemann-Loveland)
// ============================================================================
class SATDPLL : public Solver<SATProblem, SATSolution> {
public:
    std::string name() const override { return "SAT_DPLL"; }
    
protected:
    bool solve_impl(const SATProblem& problem, SATSolution& solution, SolverMetrics& metrics) override {
        solution.assignment.assign(problem.n_vars, false);
        solution.satisfied_clauses = 0;
        
        bool sat = dpll_recurse(problem, solution.assignment, 0);
        
        if (sat) {
            solution.satisfied_clauses = count_satisfied(problem, solution.assignment);
        }
        
        metrics.iterations = 0;
        metrics.objective_value = solution.satisfied_clauses;
        metrics.is_optimal = sat;
        
        return true;
    }
    
private:
    bool dpll_recurse(const SATProblem& problem, std::vector<bool>& assignment, size_t var_idx) {
        if (var_idx >= problem.n_vars) {
            return count_satisfied(problem, assignment) == problem.n_clauses;
        }
        
        // Try false
        assignment[var_idx] = false;
        if (dpll_recurse(problem, assignment, var_idx + 1)) {
            return true;
        }
        
        // Try true
        assignment[var_idx] = true;
        if (dpll_recurse(problem, assignment, var_idx + 1)) {
            return true;
        }
        
        return false;
    }
    
    size_t count_satisfied(const SATProblem& problem, const std::vector<bool>& assignment) const {
        size_t count = 0;
        for (const auto& clause : problem.clauses) {
            for (int lit : clause) {
                bool val = (lit > 0) ? assignment[lit - 1] : !assignment[-lit - 1];
                if (val) {
                    count++;
                    break;
                }
            }
        }
        return count;
    }
};

// ============================================================================
// SAT Heuristic 2: WalkSAT
// ============================================================================
class SATWalkSAT : public Solver<SATProblem, SATSolution> {
public:
    std::string name() const override { return "SAT_WalkSAT"; }
    
protected:
    bool solve_impl(const SATProblem& problem, SATSolution& solution, SolverMetrics& metrics) override {
        std::mt19937 rng(42);
        
        // Random initial assignment
        solution.assignment.resize(problem.n_vars);
        for (size_t i = 0; i < problem.n_vars; ++i) {
            solution.assignment[i] = rng() % 2;
        }
        
        const size_t max_flips = 1000;
        const double noise = 0.5;
        
        for (size_t flip = 0; flip < max_flips; ++flip) {
            size_t sat_count = count_satisfied(problem, solution.assignment);
            
            if (sat_count == problem.n_clauses) {
                solution.satisfied_clauses = sat_count;
                metrics.iterations = flip;
                metrics.objective_value = sat_count;
                metrics.is_optimal = true;
                return true;
            }
            
            // Find unsatisfied clause
            std::vector<size_t> unsat;
            for (size_t i = 0; i < problem.n_clauses; ++i) {
                bool is_sat = false;
                for (int lit : problem.clauses[i]) {
                    bool val = (lit > 0) ? solution.assignment[lit - 1] : !solution.assignment[-lit - 1];
                    if (val) {
                        is_sat = true;
                        break;
                    }
                }
                if (!is_sat) unsat.push_back(i);
            }
            
            if (unsat.empty()) break;
            
            // Pick random unsatisfied clause
            size_t clause_idx = unsat[rng() % unsat.size()];
            const auto& clause = problem.clauses[clause_idx];
            
            // Pick random variable from clause
            int lit = clause[rng() % clause.size()];
            size_t var = std::abs(lit) - 1;
            
            // Flip it
            solution.assignment[var] = !solution.assignment[var];
        }
        
        solution.satisfied_clauses = count_satisfied(problem, solution.assignment);
        metrics.iterations = max_flips;
        metrics.objective_value = solution.satisfied_clauses;
        metrics.is_optimal = false;
        
        return true;
    }
    
private:
    size_t count_satisfied(const SATProblem& problem, const std::vector<bool>& assignment) const {
        size_t count = 0;
        for (const auto& clause : problem.clauses) {
            for (int lit : clause) {
                bool val = (lit > 0) ? assignment[lit - 1] : !assignment[-lit - 1];
                if (val) {
                    count++;
                    break;
                }
            }
        }
        return count;
    }
};

// ============================================================================
// SAT Branch and Bound
// ============================================================================
class SATBranchBound : public Solver<SATProblem, SATSolution> {
public:
    std::string name() const override { return "SAT_BranchBound"; }
    
protected:
    bool solve_impl(const SATProblem& problem, SATSolution& solution, SolverMetrics& metrics) override {
        // Use DPLL for exact solving
        SATDPLL dpll;
        auto result = dpll.solve(problem);
        solution = result.solution;
        metrics = result.metrics;
        return result.success;
    }
};

} // namespace optsolve
