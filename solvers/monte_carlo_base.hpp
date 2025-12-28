#pragma once
#include "solver_base.hpp"
#include <random>
#include <cmath>
#include <vector>
#include <algorithm>

namespace optsolve {

// Configuration for Monte Carlo solvers
struct MonteCarloConfig {
    int max_iterations = 10000;
    double initial_temp = 1.0;
    double cooling_rate = 0.995;
    double random_walk_prob = 0.3; // Probability of random walk move
    int batch_size = 1; // Number of parallel chains (for future AMX/batching)
    bool auto_accept_rw = true; // Random walk moves are always accepted
};

// Base class for Monte Carlo solvers with common utilities
template<typename Problem, typename Solution>
class MonteCarloBase : public Solver<Problem, Solution> {
protected:
    std::mt19937 gen;
    MonteCarloConfig config;

    MonteCarloBase(unsigned seed = 1234) : gen(seed) {}

    // Random walk proposal (global jump)
    virtual void propose_random_walk(const Problem& problem, const Solution& current, Solution& proposal) = 0;

    // MCMC proposal (local move)
    virtual void propose_mcmc(const Problem& problem, const Solution& current, Solution& proposal) = 0;

    // Energy function (usually objective value or objective + penalty)
    virtual double energy(const Problem& problem, const Solution& solution) = 0;

    // Initialize solution structure (resize vectors, etc.)
    virtual void initialize_solution(const Problem& problem, Solution& solution) = 0;

    bool solve_impl(const Problem& problem, Solution& solution, SolverMetrics& metrics) override {
        initialize_solution(problem, solution);
        Solution current = solution; 
        if (current.is_valid(problem) == false) {
            propose_random_walk(problem, current, current);
        }

        Solution best = current;
        double current_energy = energy(problem, current);
        double best_energy = current_energy;
        double temp = config.initial_temp;

        std::uniform_real_distribution<double> dist(0.0, 1.0);
        
        metrics.iterations = 0;
        for (int i = 0; i < config.max_iterations; ++i) {
            metrics.iterations++;
            Solution proposal = current;
            bool is_rw = dist(gen) < config.random_walk_prob;

            if (is_rw) {
                propose_random_walk(problem, current, proposal);
            } else {
                propose_mcmc(problem, current, proposal);
            }

            double proposal_energy = energy(problem, proposal);
            double delta = proposal_energy - current_energy;

            // Metropolis acceptance criterion
            // Note: For minimization, delta < 0 is good. For maximization, delta > 0 is good.
            // Problem types should define if they are min or max.
            // Here we assume minimization (like TSP). For maximization (Knapsack), use -delta.
            bool accept = false;
            if (is_rw && config.auto_accept_rw) {
                accept = true;
            } else {
                if (delta < 0) {
                    accept = true;
                } else {
                    double p = std::exp(-delta / temp);
                    if (dist(gen) < p) {
                        accept = true;
                    }
                }
            }

            if (accept) {
                current = proposal;
                current_energy = proposal_energy;
                if (current_energy < best_energy) {
                    best = current;
                    best_energy = current_energy;
                }
            }

            temp *= config.cooling_rate;
        }

        solution = best;
        metrics.objective_value = best_energy;
        metrics.is_optimal = false;
        return true;
    }
};

} // namespace optsolve
