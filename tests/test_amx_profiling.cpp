#include "server_solvers_amx.hpp"
#include <iostream>
#include <vector>
#include <random>
#include <iomanip>
#include <chrono>

using namespace optsolve;

// Helper to check alignment
void check_alignment(const char* name, void* ptr) {
    uintptr_t addr = (uintptr_t)ptr;
    std::cout << "  - " << std::setw(10) << name << ": " << ptr 
              << " (Aligned 64B? " << ((addr % 64 == 0) ? "YES" : "NO") 
              << ", 16B? " << ((addr % 16 == 0) ? "YES" : "NO") << ")\n";
}

int main() {
    int n_instances = 512;
    std::cout << "Profiling AMX Solver on " << n_instances << " instances...\n";

    // Setup random generator
    std::mt19937 rng(42);
    std::uniform_real_distribution<float> dist_pos(0.0f, 100.0f);
    std::uniform_real_distribution<float> dist_dem(1.0f, 10.0f);
    
    // Access static profiler
    using Profiler = AMX_IPM_Solver::AmxProfiler;
    Profiler::reset();
    
    // Create solver and inspect alignment
    AMX_IPM_Solver solver;
    
    // Warm-up / Cache Coherence Analysis
    std::cout << "\n[Memory Alignment Check (Cache Coherence)]\n";
    // Force a resize to allocate memory
    solver.ws.resize(100, 100); 
    check_alignment("Dense A", solver.ws.dense_A.data());
    check_alignment("Work Buf", solver.ws.buffer.data());
    check_alignment("Matrix M", solver.ws.M.data());
    check_alignment("Diag D", solver.ws.D.data());

    std::cout << "\n[Execution Phase]\n";
    auto t_start = std::chrono::high_resolution_clock::now();
    
    double t_first_10 = 0;
    double t_remaining = 0;

    for (int i = 0; i < n_instances; ++i) {
        // Generate small LP instance
        ServerProblem problem;
        problem.sla_limit = 50.0;
        problem.z_score = 1.0;
        
        int n_servers = 5; // Small dense
        int n_groups = 10;
        
        for(int s=0; s<n_servers; ++s) {
            problem.servers.push_back({
                (size_t)s, dist_pos(rng), dist_pos(rng), 
                100.0f, 10.0f // Cap, Cost
            });
        }
        for(int g=0; g<n_groups; ++g) {
             problem.groups.push_back({
                 (size_t)g, dist_pos(rng), dist_pos(rng),
                 dist_dem(rng)
             });
        }
        
        auto t_iter_start = std::chrono::high_resolution_clock::now();
        
        // Solve
        solver.solve(problem);
        
        auto t_iter_end = std::chrono::high_resolution_clock::now();
        double dt = std::chrono::duration<double>(t_iter_end - t_iter_start).count();
        
        if (i < 10) t_first_10 += dt;
        else t_remaining += dt;
        
        if ((i+1) % 100 == 0) std::cout << "Processed " << i+1 << "...\n";
    }
    
    auto t_end = std::chrono::high_resolution_clock::now();
    double t_total = std::chrono::duration<double>(t_end - t_start).count();

    Profiler::print();
    
    std::cout << "\n[Branch/Cache Warmup Analysis]\n";
    std::cout << "Avg Time (First 10 - Cold): " << (t_first_10 / 10.0) * 1000.0 << " ms\n";
    std::cout << "Avg Time (Rest - Warm):     " << (t_remaining / (n_instances - 10.0)) * 1000.0 << " ms\n";
    
    if ((t_first_10 / 10.0) > (t_remaining / (n_instances - 10.0)) * 1.2) {
        std::cout << "-> Detectable Cache Warmup Effect (Cold is >20% slower)\n";
    } else {
        std::cout << "-> Minimal Warmup Effect (Code fits in L1/L2?)\n";
    }

    std::cout << "\nAnalysis Complete.\n";
    
    return 0;
}
