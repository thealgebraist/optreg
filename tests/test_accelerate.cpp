#include <iostream>
#include <vector>
#include <chrono>
#include <fstream>
#include <iomanip>

#include "problem_types.hpp"
#include "solver_base.hpp"
#include "tsp_solvers.hpp"
#include "fourier_solvers.hpp"
#include "accelerate_solvers.hpp"

using namespace optsolve;

int main() {
    std::cout << "Starting Accelerate Spectral Heuristic Benchmark (N=100)...\n";
    std::ofstream csv("accelerate_results.csv");
    csv << "id,std_2opt,fourier_contour,accel_spectral,gap_accel\n";
    
    TSP2Opt tsp_std;
    FourierContourSolver tsp_four;
    AccelerateFourierTSPSolver tsp_accel;
    
    // Warmup vDSP
    {
        TSPProblem p = TSPProblem::random(16, 0);
        tsp_accel.solve(p);
    }
    
    double total_gap = 0;
    int n_instances = 50;
    
    for(int i=0; i<n_instances; ++i) {
        TSPProblem p = TSPProblem::random(128, i + 2000); // 128 is Power of 2
        
        auto t1 = std::chrono::high_resolution_clock::now();
        auto res_std = tsp_std.solve(p);
        auto t2 = std::chrono::high_resolution_clock::now();
        
        auto res_four = tsp_four.solve(p);
        
        auto t3 = std::chrono::high_resolution_clock::now();
        auto res_accel = tsp_accel.solve(p);
        auto t4 = std::chrono::high_resolution_clock::now();
        
        double gap = (res_accel.metrics.objective_value - res_std.metrics.objective_value) / res_std.metrics.objective_value * 100.0;
        total_gap += gap;
        
        std::cout << "Instance " << i << ": Std=" << res_std.metrics.objective_value 
                  << " Accel=" << res_accel.metrics.objective_value 
                  << " Gap=" << gap << "%\n";
                  
        csv << i << "," << res_std.metrics.objective_value << "," 
            << res_four.metrics.objective_value << "," 
            << res_accel.metrics.objective_value << "," << gap << "\n";
    }
    
    std::cout << "\nAverage Gap (Accelerate vs 2-Opt): " << (total_gap / n_instances) << "%\n";
    std::cout << "Done.\n";
    csv.close();
    return 0;
}
