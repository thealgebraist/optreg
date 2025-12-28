#pragma once
#include "monte_carlo_base.hpp"
#include "problem_types.hpp"
#include <numeric>

namespace optsolve {

// ============================================================================
// TSP Monte Carlo Solvers
// ============================================================================

class TSPMonteCarlo : public MonteCarloBase<TSPProblem, TSPSolution> {
public:
    TSPMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0; // Pure MCMC
    }
    
    std::string name() const override { return "TSP_MonteCarlo"; }

protected:
    void initialize_solution(const TSPProblem& problem, TSPSolution& solution) override {
        solution.tour.resize(problem.n_cities);
        std::iota(solution.tour.begin(), solution.tour.end(), 0);
    }

    void propose_random_walk(const TSPProblem& problem, const TSPSolution& current, TSPSolution& proposal) override {
        // Shuffle all cities
        std::iota(proposal.tour.begin(), proposal.tour.end(), 0);
        std::shuffle(proposal.tour.begin(), proposal.tour.end(), gen);
    }

    void propose_mcmc(const TSPProblem& problem, const TSPSolution& current, TSPSolution& proposal) override {
        // Swap two random cities
        std::uniform_int_distribution<size_t> city_dist(0, problem.n_cities - 1);
        size_t i = city_dist(gen);
        size_t j = city_dist(gen);
        std::swap(proposal.tour[i], proposal.tour[j]);
    }

    double energy(const TSPProblem& problem, const TSPSolution& solution) override {
        double dist = 0;
        for (size_t i = 0; i < problem.n_cities; ++i) {
            size_t from = solution.tour[i];
            size_t to = solution.tour[(i + 1) % problem.n_cities];
            dist += problem.distances[from][to];
        }
        return dist;
    }
};

class TSPMonteCarloRW : public TSPMonteCarlo {
public:
    TSPMonteCarloRW(unsigned seed = 1234) : TSPMonteCarlo(seed) {
        config.random_walk_prob = 0.3; // Hybrid
    }
    
    std::string name() const override { return "TSP_MonteCarloRW"; }
};

// ============================================================================
// Knapsack Monte Carlo Solvers
// ============================================================================

class KnapsackMonteCarlo : public MonteCarloBase<KnapsackProblem, KnapsackSolution> {
public:
    KnapsackMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    
    std::string name() const override { return "Knapsack_MonteCarlo"; }

protected:
    void initialize_solution(const KnapsackProblem& problem, KnapsackSolution& solution) override {
        solution.selected.assign(problem.n_items, false);
    }

    void propose_random_walk(const KnapsackProblem& problem, const KnapsackSolution& current, KnapsackSolution& proposal) override {
        // Random bitset
        std::uniform_int_distribution<int> bin(0, 1);
        for (size_t i = 0; i < problem.n_items; ++i) {
            proposal.selected[i] = bin(gen);
        }
    }

    void propose_mcmc(const KnapsackProblem& problem, const KnapsackSolution& current, KnapsackSolution& proposal) override {
        // Flip one random bit
        std::uniform_int_distribution<size_t> item_dist(0, problem.n_items - 1);
        size_t i = item_dist(gen);
        proposal.selected[i] = !proposal.selected[i];
    }

    double energy(const KnapsackProblem& problem, const KnapsackSolution& solution) override {
        double val = 0;
        double weight = 0;
        for (size_t i = 0; i < problem.n_items; ++i) {
            if (solution.selected[i]) {
                val += problem.values[i];
                weight += problem.weights[i];
            }
        }
        // Minimization energy: -value, with large penalty for weight limit exceeded
        if (weight > problem.capacity) {
            return 1e9 + (weight - problem.capacity);
        }
        return -val;
    }

    bool solve_impl(const KnapsackProblem& problem, KnapsackSolution& solution, SolverMetrics& metrics) override {
        bool res = MonteCarloBase<KnapsackProblem, KnapsackSolution>::solve_impl(problem, solution, metrics);
        // After solving, energy() returns -best_value. Need to fix metrics. objective_value
        metrics.objective_value = -metrics.objective_value;
        return res;
    }
};

class KnapsackMonteCarloRW : public KnapsackMonteCarlo {
public:
    KnapsackMonteCarloRW(unsigned seed = 1234) : KnapsackMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    
    std::string name() const override { return "Knapsack_MonteCarloRW"; }
};

// ============================================================================
// SAT Monte Carlo Solvers
// ============================================================================

class SATMonteCarlo : public MonteCarloBase<SATProblem, SATSolution> {
public:
    SATMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    
    std::string name() const override { return "SAT_MonteCarlo"; }

protected:
    void initialize_solution(const SATProblem& problem, SATSolution& solution) override {
        solution.assignment.assign(problem.n_vars, false);
    }

    void propose_random_walk(const SATProblem& problem, const SATSolution& current, SATSolution& proposal) override {
        std::uniform_int_distribution<int> bin(0, 1);
        for (size_t i = 0; i < problem.n_vars; ++i) {
            proposal.assignment[i] = bin(gen);
        }
    }

    void propose_mcmc(const SATProblem& problem, const SATSolution& current, SATSolution& proposal) override {
        // WalkSAT style: flip one random bit
        std::uniform_int_distribution<size_t> var_dist(0, problem.n_vars - 1);
        size_t i = var_dist(gen);
        proposal.assignment[i] = !proposal.assignment[i];
    }

    double energy(const SATProblem& problem, const SATSolution& solution) override {
        int unsatisfied = 0;
        for (const auto& clause : problem.clauses) {
            bool satisfied = false;
            for (const auto& lit : clause) {
                bool val = solution.assignment[std::abs(lit) - 1];
                if (lit < 0) val = !val;
                if (val) {
                    satisfied = true;
                    break;
                }
            }
            if (!satisfied) unsatisfied++;
        }
        return (double)unsatisfied;
    }
};

class SATMonteCarloRW : public SATMonteCarlo {
public:
    SATMonteCarloRW(unsigned seed = 1234) : SATMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    
    std::string name() const override { return "SAT_MonteCarloRW"; }
};

} // namespace optsolve
