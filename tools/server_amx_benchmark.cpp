#include "all_advanced_solvers.hpp"
#include <iostream>
#include <vector>
#include <chrono>
#include <iomanip>

using namespace optsolve;

int main() {
    // We'll use a slightly smaller instance for B&B as recursive search can be slow
    size_t n_s = 20;
    size_t n_g = 10;
    auto problem = ServerProblem::random(n_s, n_g, 42);

    std::cout << "=== Server Optimization Benchmark (C++ Sparse AMX) ===\n";
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
    auto start_a = std::chrono::high_resolution_clock::now();
    auto res_a = amx.solve(problem);
    auto end_a = std::chrono::high_resolution_clock::now();
    double time_a = std::chrono::duration<double, std::milli>(end_a - start_a).count();

    std::cout << "\nSparse AMX Optimal (B&B):\n";
    if (res_a.success) {
        std::cout << "  Cost: " << std::fixed << std::setprecision(2) << res_a.solution.total_cost << "\n";
        std::cout << "  Time: " << time_a << " ms\n";
        std::cout << "  Nodes Visited: " << res_a.metrics.iterations << "\n";
        
        if (res_g.success) {
            double gap = (res_g.solution.total_cost - res_a.solution.total_cost) / res_a.solution.total_cost * 100;
            std::cout << "\nAccuracy Gap: " << gap << "%\n";
        }
    } else {
        std::cout << "  FAILED to find solution\n";
    }

    return 0;
}
