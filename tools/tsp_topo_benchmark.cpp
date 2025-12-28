#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <random>
#include <cmath>
#include <iomanip>
#include <chrono>
#include <map>

using namespace optsolve;

int main() {
    std::vector<std::shared_ptr<Solver<TSPProblem, TSPSolution>>> solvers = {
        std::make_shared<TSPNearestNeighbor>(),
        std::make_shared<TSP2Opt>(),
        std::make_shared<TSPGeometricHeuristic>(),
        std::make_shared<TSPBoltzmannHeuristic>(),
        std::make_shared<TSPTopologicalBoltzmann>()
    };

    TSPBranchBound exact_solver;
    
    std::mt19937 rng(999);
    std::uniform_int_distribution<size_t> n_dist(4, 19);

    std::cout << "Starting Massive Benchmark: 4096 instances ($n < 20$)\n";
    std::cout << "------------------------------------------------------\n";

    std::map<std::string, double> total_gap;
    std::map<std::string, long long> total_time;
    std::map<std::string, int> optimal_count;

    for (int i = 0; i < 4096; ++i) {
        size_t n = n_dist(rng);
        auto p = TSPProblem::random(n, i + 8000);

        auto opt_res = exact_solver.solve(p);
        double opt_dist = opt_res.solution.total_distance;

        for (auto& s : solvers) {
            auto start = std::chrono::high_resolution_clock::now();
            auto res = s->solve(p);
            auto end = std::chrono::high_resolution_clock::now();

            double gap = (res.solution.total_distance / opt_dist - 1.0) * 100.0;
            total_gap[s->name()] += gap;
            total_time[s->name()] += std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
            if (std::abs(res.solution.total_distance - opt_dist) < 1e-6) {
                optimal_count[s->name()]++;
            }
        }

        if ((i + 1) % 512 == 0) {
            std::cout << "Benchmarked " << (i + 1) << " instances...\n";
        }
    }

    std::cout << "\n=== Benchmark Results (N=4096, n < 20) ===\n";
    std::cout << std::left << std::setw(25) << "Solver" << " | " << std::setw(10) << "Avg Gap" << " | " << std::setw(10) << "Opt Count" << " | " << "Avg Time (us)\n";
    std::cout << std::string(65, '-') << "\n";

    for (auto& s : solvers) {
        std::string name = s->name();
        std::cout << std::left << std::setw(25) << name << " | " 
                  << std::setw(9) << std::fixed << std::setprecision(3) << total_gap[name] / 4096.0 << "% | "
                  << std::setw(10) << optimal_count[name] << " | "
                  << total_time[name] / 4096 << "\n";
    }

    return 0;
}
