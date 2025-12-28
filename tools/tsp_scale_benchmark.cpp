#include "tsp_solvers.hpp"
#include "all_mc_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <chrono>
#include <random>

using namespace optsolve;

int main() {
    std::ofstream out("optreg/build/tsp_scale_benchmark.csv");
    out << "instance,n,solver,obj,time_ms\n";

    std::vector<std::shared_ptr<Solver<TSPProblem, TSPSolution>>> solvers = {
        std::make_shared<TSPNearestNeighbor>(),
        std::make_shared<TSP2Opt>(),
        std::make_shared<TSPPatternHeuristic>(),
        std::make_shared<TSPGeometricHeuristic>(),
        std::make_shared<TSPMonteCarloRW>()
    };

    std::mt19937 rng(99);
    std::uniform_int_distribution<size_t> n_dist(10, 31);

    std::cout << "Starting Scale Benchmark (1024 instances, n < 32)...\n";

    for (int i = 0; i < 1024; ++i) {
        size_t n = n_dist(rng);
        TSPProblem p = TSPProblem::random(n, i + 10000);
        
        for (auto& solver : solvers) {
            auto start = std::chrono::high_resolution_clock::now();
            auto res = solver->solve(p);
            auto end = std::chrono::high_resolution_clock::now();
            
            double ms = std::chrono::duration<double, std::milli>(end - start).count();
            out << i << "," << n << "," << solver->name() << "," << res.solution.total_distance << "," << ms << "\n";
        }
        
        if ((i + 1) % 64 == 0) std::cout << "Progress: " << (i + 1) << "/1024 instances\n";
    }

    out.close();
    std::cout << "Scale benchmark complete. Results saved to optreg/build/tsp_scale_benchmark.csv\n";
    return 0;
}
