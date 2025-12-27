#include <iostream>
#include <chrono>
#include <iomanip>
#include <thread>
#include <atomic>
#include "tsplib_parser.h"
#include "tsp_solver.h"
#include "branch_bound.h"
#include "interior_point.h"

using namespace optreg;

// Standard gr17 instance (17 nodes, lower triangular)
const char* gr17_data = 
"NAME: gr17\n"
"TYPE: TSP\n"
"DIMENSION: 17\n"
"EDGE_WEIGHT_TYPE: EXPLICIT\n"
"EDGE_WEIGHT_FORMAT: LOWER_DIAG_ROW\n"
"EDGE_WEIGHT_SECTION\n"
" 0\n"
" 633 0\n"
" 257 390 0\n"
" 91 661 228 0\n"
" 412 227 169 383 0\n"
" 150 488 112 120 267 0\n"
" 80 572 196 77 351 63 0\n"
" 122 530 154 105 309 34 29 0\n"
" 638 355 372 679 240 540 587 561 0\n"
" 716 470 450 757 355 618 665 639 91 0\n"
" 143 420 85 113 256 65 92 84 411 489 0\n"
" 314 314 127 301 190 191 227 210 330 408 110 0\n"
" 220 440 181 213 365 193 164 193 545 623 154 263 0\n"
" 121 503 162 128 349 84 76 104 522 600 95 242 128 0\n"
" 272 214 140 338 121 211 247 220 199 277 151 86 286 250 0\n"
" 496 232 252 522 132 351 387 360 155 212 284 218 369 311 113 0\n"
" 176 438 107 190 322 120 120 137 470 548 65 171 215 96 226 317 0\n";

// Helper to handle explicitly formatted LOWER_DIAG_ROW
TSPInstance parse_gr17() {
    TSPInstance instance;
    instance.name = "gr17";
    instance.dimension = 17;
    instance.edge_weight_type = "EXPLICIT";
    instance.adj.resize(17, std::vector<double>(17));
    
    std::stringstream ss(gr17_data);
    std::string line;
    while (std::getline(ss, line) && line.find("EDGE_WEIGHT_SECTION") == std::string::npos);
    
    for (int i = 0; i < 17; ++i) {
        for (int j = 0; j <= i; ++j) {
            double w;
            ss >> w;
            instance.adj[i][j] = instance.adj[j][i] = w;
        }
    }
    return instance;
}

struct BenchResult {
    std::string solver;
    double time_ms;
    double cost;
    bool optimal;
};

void run_instance(const TSPInstance& instance, const std::string& name) {
    std::cout << "\n=== Benchmarking TSP: " << name << " (N=" << instance.dimension << ") ===\n";
    
    TSPSolver tsp_solver;
    auto lp = tsp_solver.formulate_ip(instance);
    
    std::vector<BenchResult> results;
    
    auto solve_with = [&](const std::string& label, BranchAndBound::LinearBackend backend) {
        std::cout << "  Running " << label << "..." << std::flush;
        BranchAndBound solver;
        solver.set_linear_solver_backend(backend);
        solver.set_num_integer_vars(instance.dimension * instance.dimension);
        solver.set_max_nodes(2000); 
        solver.set_tolerance(1e-4);
        
        auto start = std::chrono::high_resolution_clock::now();
        auto sol = solver.solve(lp);
        auto end = std::chrono::high_resolution_clock::now();
        
        double time_ms = std::chrono::duration<double, std::milli>(end - start).count();
        results.push_back({label, time_ms, sol.objective, sol.optimal});
        std::cout << " Done. (" << time_ms << " ms)\n";
    };

    solve_with("AMX Sparse B&B", BranchAndBound::LinearBackend::AMX);
    solve_with("AMX Dense B&B", BranchAndBound::LinearBackend::AMXDense);
    solve_with("Eigen Sparse B&B", BranchAndBound::LinearBackend::EigenSparse);

    // Heuristic: Nearest Neighbor
    {
        auto start = std::chrono::high_resolution_clock::now();
        std::vector<int> tour;
        std::vector<bool> visited(instance.dimension, false);
        int curr = 0;
        tour.push_back(0);
        visited[0] = true;
        double cost = 0;
        for (int i = 1; i < instance.dimension; ++i) {
            int next = -1;
            double min_d = 1e18;
            for (int j = 0; j < instance.dimension; ++j) {
                if (!visited[j] && instance.adj[curr][j] < min_d) {
                    min_d = instance.adj[curr][j];
                    next = j;
                }
            }
            tour.push_back(next);
            visited[next] = true;
            cost += min_d;
            curr = next;
        }
        cost += instance.adj[curr][0];
        auto end = std::chrono::high_resolution_clock::now();
        results.push_back({"Nearest Neighbor", std::chrono::duration<double, std::milli>(end - start).count(), cost, false});
    }

    // Output Table
    std::cout << std::setw(20) << "Solver" << " | " << std::setw(12) << "Time (ms)" << " | " << std::setw(10) << "Cost" << " | " << "Optimal\n";
    std::cout << std::string(60, '-') << "\n";
    for (const auto& res : results) {
        std::cout << std::setw(20) << res.solver << " | " 
                  << std::setw(12) << std::fixed << std::setprecision(2) << res.time_ms << " | " 
                  << std::setw(10) << res.cost << " | " 
                  << (res.optimal ? "YES" : "NO") << "\n";
    }
}

int main() {
    auto gr17 = parse_gr17();
    run_instance(gr17, "gr17");

    // Synthetic 10-node instance
    TSPInstance k10;
    k10.dimension = 10;
    k10.adj.resize(10, std::vector<double>(10));
    for(int i=0; i<10; ++i) {
        for(int j=0; j<10; ++j) {
            k10.adj[i][j] = (i==j) ? 0 : (std::abs(i-j) * 10 + (i+j)%5);
        }
    }
    run_instance(k10, "Synthetic-K10");

    return 0;
}
