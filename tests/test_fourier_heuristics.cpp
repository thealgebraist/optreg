#include <iostream>
#include <vector>
#include <chrono>
#include <fstream>
#include <iomanip>

#include "problem_types.hpp"
#include "solver_base.hpp"
#include "tsp_solvers.hpp"
#include "coloring_solvers.hpp"
#include "fourier_solvers.hpp"

using namespace optsolve;

int main() {
    std::cout << "Starting Fourier DE Heuristics Benchmark...\n";
    std::ofstream csv("fourier_results.csv");
    csv << "problem,id,fourier_val,standard_val,gap_pct\n";
    
    // 1. TSP Benchmark
    std::cout << "--- TSP (Active Contour vs Physarum vs 2-Opt) ---\n";
    TSP2Opt tsp_std;
    FourierContourSolver tsp_four;
    PhysarumTSPSolver tsp_phy;
    
    for(int i=0; i<128; ++i) {
        TSPProblem p = TSPProblem::random(50, i);
        
        auto res_std = tsp_std.solve(p);
        auto res_four = tsp_four.solve(p);
        auto res_phy = tsp_phy.solve(p);
        
        double gap_four = (res_four.metrics.objective_value - res_std.metrics.objective_value) / res_std.metrics.objective_value * 100.0;
        double gap_phy = (res_phy.metrics.objective_value - res_std.metrics.objective_value) / res_std.metrics.objective_value * 100.0;
        
        csv << "TSP," << i << "," << res_four.metrics.objective_value << "," << res_std.metrics.objective_value << "," << gap_four << "\n";
        csv << "TSP_Physarum," << i << "," << res_phy.metrics.objective_value << "," << res_std.metrics.objective_value << "," << gap_phy << "\n";
    }
    
    // 2. Coloring Benchmark
    std::cout << "--- Coloring (Kuramoto vs Physarum vs DSatur) ---\n";
    ColoringDSATUR col_std;
    KuramotoPhaseSolver col_four;
    PhysarumColoringSolver col_phy;
    
    for(int i=0; i<128; ++i) {
        GraphColoringProblem p = GraphColoringProblem::random(50, 0.2, i+1000);
        
        auto res_std = col_std.solve(p);
        auto res_four = col_four.solve(p);
        auto res_phy = col_phy.solve(p);
        
        double gap_four = (double)(res_four.metrics.objective_value - res_std.metrics.objective_value);
        double gap_phy = (double)(res_phy.metrics.objective_value - res_std.metrics.objective_value);
        
        csv << "Coloring," << i << "," << res_four.metrics.objective_value << "," << res_std.metrics.objective_value << "," << gap_four << "\n";
        csv << "Coloring_Physarum," << i << "," << res_phy.metrics.objective_value << "," << res_std.metrics.objective_value << "," << gap_phy << "\n";
    }
    
    csv.close();
    std::cout << "Done.\n";
    return 0;
}
