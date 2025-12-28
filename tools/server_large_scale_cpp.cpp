#include "all_advanced_solvers.hpp"
#include <iostream>
#include <vector>
#include <chrono>
#include <iomanip>

using namespace optsolve;

int main() {
    // 10x the initial C++ benchmark (20/10 -> 200/100)
    size_t n_s = 200;
    size_t n_g = 100;
    auto problem = ServerProblem::random(n_s, n_g, 42);
    
    // Lower min-util for random gen robustness at scale
    problem.u_target = 0.3;

    std::cout << "=== Large-Scale Server Optimization (C++ 200s/100g) ===\n";
    std::cout << "Instance: " << n_s << " servers, " << n_g << " groups\n\n";

    ServerGreedy greedy;
    ServerSparseAMX amx;

    // 1. Greedy
    auto start_g = std::chrono::high_resolution_clock::now();
    auto res_g = greedy.solve(problem);
    auto end_g = std::chrono::high_resolution_clock::now();
    double time_g = std::chrono::duration<double, std::milli>(end_g - start_g).count();

    std::cout << "Greedy Heuristic:\n";
    if (res_g.success) {
        std::cout << "  Cost: " << std::fixed << std::setprecision(2) << res_g.solution.total_cost << "\n";
        std::cout << "  Time: " << time_g << " ms\n";
    } else {
        std::cout << "  FAILED to find solution\n";
    }

    // 2. Sparse AMX (Optimal B&B)
    std::cout << "\nStarting Sparse AMX Optimal (B&B)... [This might take a moment]\n";
    auto start_a = std::chrono::high_resolution_clock::now();
    auto res_a = amx.solve(problem);
    auto end_a = std::chrono::high_resolution_clock::now();
    double time_a = std::chrono::duration<double, std::milli>(end_a - start_a).count();

    if (res_a.success) {
        std::cout << "Optimal Results:\n";
        std::cout << "  Cost: " << std::fixed << std::setprecision(2) << res_a.solution.total_cost << "\n";
        std::cout << "  Time: " << time_a << " ms\n";
        std::cout << "  Nodes Visited: " << res_a.metrics.iterations << "\n";
        
        if (res_g.success) {
            double gap = (res_g.solution.total_cost - res_a.solution.total_cost) / res_a.solution.total_cost * 100;
            std::cout << "\nAccuracy Gap: " << gap << "%\n";
        }
    } else {
        std::cout << "Optimal solver FAILED to find solution or timed out.\n";
    }

    return 0;
}
