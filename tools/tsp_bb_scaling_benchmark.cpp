#include "tsp_advanced_solvers.hpp"
#include <iostream>
#include <vector>
#include <chrono>
#include <iomanip>
#include <numeric>

using namespace optsolve;

int main() {
    std::cout << "=== TSP B&B Scaling Benchmark (Reduction-based Dense AMX) ===\n";
    std::cout << std::left << std::setw(6) << "N" << " | " 
              << std::setw(12) << "Avg Time(ms)" << " | "
              << std::setw(12) << "Avg Nodes" << " | "
              << "Status\n";
    std::cout << std::string(50, '-') << "\n";

    TSPDenseAMX bb;
    
    for (int n = 4; n <= 24; ++n) {
        double total_time = 0;
        size_t total_nodes = 0;
        bool timed_out = false;

        for (int trial = 0; trial < 8; ++trial) {
            auto p = TSPProblem::random(n, trial + n * 100);
            
            auto start = std::chrono::high_resolution_clock::now();
            auto res = bb.solve(p);
            auto end = std::chrono::high_resolution_clock::now();
            
            if (!res.success) {
                timed_out = true;
                break;
            }

            total_time += std::chrono::duration<double, std::milli>(end - start).count();
            total_nodes += res.metrics.iterations;
            
            // Safety break if one instance takes too long (> 2s)
            if (std::chrono::duration<double>(end - start).count() > 2.0) {
                timed_out = true;
                // We'll still report what we have for this N, but skip further trials/N
            }
        }

        if (timed_out) {
            std::cout << std::left << std::setw(6) << n << " | " 
                      << std::setw(12) << "TIMEOUT" << " | "
                      << std::setw(12) << "-" << " | "
                      << "Skipped remaining\n";
            break;
        }

        std::cout << std::left << std::setw(6) << n << " | " 
                  << std::setw(12) << std::fixed << std::setprecision(2) << total_time / 8.0 << " | "
                  << std::setw(12) << total_nodes / 8 << " | "
                  << "OK\n";
    }

    return 0;
}
