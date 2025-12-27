#include <iostream>
#include <vector>
#include <chrono>
#include <iomanip>
#include "graph_coloring.h"
#include "interior_point.h"
#include "metaheuristics.h"
#include "interference_graph.h"

using namespace optreg;

// Generate a clique graph of size N
InterferenceGraph generate_clique(uint32_t n) {
    InterferenceGraph graph;
    graph.num_variables = n;
    for (uint32_t i = 0; i < n; ++i) {
        for (uint32_t j = i + 1; j < n; ++j) {
            graph.edges[i].insert(j);
            graph.edges[j].insert(i);
        }
    }
    return graph;
}

struct BenchResult {
    std::string name;
    double time_ms;
    double objective;
    bool optimal;
};

void print_table(const std::vector<uint32_t>& sizes, const std::map<uint32_t, std::vector<BenchResult>>& all_results) {
    std::cout << "\n" << std::setw(10) << "Size" << " | " 
              << std::setw(20) << "Solver" << " | " 
              << std::setw(12) << "Time (ms)" << " | " 
              << std::setw(12) << "Objective" << "\n";
    std::cout << std::string(60, '-') << "\n";

    for (uint32_t n : sizes) {
        if (all_results.count(n)) {
            for (const auto& res : all_results.at(n)) {
                std::cout << std::setw(10) << n << " | " 
                          << std::setw(20) << res.name << " | " 
                          << std::setw(12) << std::fixed << std::setprecision(2) << res.time_ms << " | " 
                          << std::setw(12) << res.objective << "\n";
            }
            std::cout << std::string(60, '-') << "\n";
        }
    }
}

int main() {
    std::vector<uint32_t> sizes = {5, 10, 15, 20};
    std::map<uint32_t, std::vector<BenchResult>> all_results;

    for (uint32_t n : sizes) {
        std::cout << "Benchmarking Clique K_" << n << "...\n";
        auto graph = generate_clique(n);
        uint32_t num_regs = n; // Should be colorable with n colors without spills
        
        std::unordered_map<uint32_t, double> spill_costs;
        for (uint32_t i = 0; i < n; ++i) spill_costs[i] = 100.0; // High spill cost

        ControlFlowGraph cfg; // Dummy CFG

        // 1. AMX Dense (Interior Point)
        {
            GraphColoringAllocator allocator(num_regs);
            auto lp = allocator.formulate_ip(graph, spill_costs);
            InteriorPointSolver solver;
            solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::AMXDense);
            solver.set_verbose(false);
            
            auto start = std::chrono::high_resolution_clock::now();
            auto sol = solver.solve(lp);
            auto end = std::chrono::high_resolution_clock::now();
            
            all_results[n].push_back({"AMX Dense IP", 
                std::chrono::duration<double, std::milli>(end - start).count(),
                sol.optimal ? 0.0 : sol.objective, sol.optimal});
        }

        // 2. AMX Sparse (Interior Point)
        {
            GraphColoringAllocator allocator(num_regs);
            auto lp = allocator.formulate_ip(graph, spill_costs);
            InteriorPointSolver solver;
            solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::AMX); // AMXSparse
            solver.set_verbose(false);
            
            auto start = std::chrono::high_resolution_clock::now();
            auto sol = solver.solve(lp);
            auto end = std::chrono::high_resolution_clock::now();
            
            all_results[n].push_back({"AMX Sparse IP", 
                std::chrono::duration<double, std::milli>(end - start).count(),
                sol.optimal ? 0.0 : sol.objective, sol.optimal});
        }

        // 3. Eigen Sparse (Interior Point)
        {
            GraphColoringAllocator allocator(num_regs);
            auto lp = allocator.formulate_ip(graph, spill_costs);
            InteriorPointSolver solver;
            solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::EigenSparse);
            solver.set_verbose(false);
            
            auto start = std::chrono::high_resolution_clock::now();
            auto sol = solver.solve(lp);
            auto end = std::chrono::high_resolution_clock::now();
            
            all_results[n].push_back({"Eigen Sparse IP", 
                std::chrono::duration<double, std::milli>(end - start).count(),
                sol.optimal ? 0.0 : sol.objective, sol.optimal});
        }

        // 4. Tabu Search Bit
        {
            TabuSearchBitSolver solver;
            auto start = std::chrono::high_resolution_clock::now();
            auto sol = solver.solve(cfg, graph, num_regs, spill_costs);
            auto end = std::chrono::high_resolution_clock::now();
            
            all_results[n].push_back({"Tabu Search Bit", 
                std::chrono::duration<double, std::milli>(end - start).count(),
                sol.total_cost, true});
        }

        // 5. GLS Bit
        {
            GuidedLocalSearchBitSolver solver;
            auto start = std::chrono::high_resolution_clock::now();
            auto sol = solver.solve(cfg, graph, num_regs, spill_costs);
            auto end = std::chrono::high_resolution_clock::now();
            
            all_results[n].push_back({"GLS Bit", 
                std::chrono::duration<double, std::milli>(end - start).count(),
                sol.total_cost, true});
        }
    }

    print_table(sizes, all_results);

    return 0;
}
