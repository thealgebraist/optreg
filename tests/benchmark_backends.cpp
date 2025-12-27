#include <iostream>
#include <vector>
#include <chrono>
#include <future>
#include <thread>
#include "graph_coloring.h"
#include "interference_graph.h"
#include "global_allocator.h"
#include "branch_bound.h"
#include "metaheuristics.h"
#include <map>
#include <cstdlib>

using namespace optreg;

// Generate a complete graph (Clique) of size K
InterferenceGraph generate_clique(uint32_t k) {
    InterferenceGraph graph;
    graph.num_variables = k;
    for (uint32_t i = 0; i < k; ++i) {
        for (uint32_t j = i + 1; j < k; ++j) {
            graph.edges[i].insert(j);
            graph.edges[j].insert(i);
            graph.degree[i]++;
            graph.degree[j]++;
        }
    }
    return graph;
}

void run_local_test(const std::string& name, GraphColoringAllocator& allocator, 
              const ControlFlowGraph& cfg, const LivenessInfo& live, const InterferenceGraph& graph,
              GraphColoringAllocator::SolverType type) {
    
    auto task = [&]() {
        auto start = std::chrono::high_resolution_clock::now();
        auto result = allocator.allocate_optimal(cfg, live, graph, type);
        auto end = std::chrono::high_resolution_clock::now();
        double time_ms = std::chrono::duration<double, std::milli>(end - start).count();
        std::cout << name << ": Spills=" << result.num_spills << " Time=" << time_ms << "ms\n";
    };

    auto future = std::async(std::launch::async, task);
    if (future.wait_for(std::chrono::seconds(60)) == std::future_status::timeout) {
        std::cout << name << ": TIMEOUT (>60s)\n";
        // Cannot kill thread, but we proceed. Result is lost.
    } else {
        future.get();
    }
}

void run_global_test(const std::string& name, GlobalRegisterAllocator& allocator, 
                     const GlobalCFG& cfg, const GlobalInterferenceGraph& graph,
                     GraphColoringAllocator::SolverType type) {
    
    auto task = [&]() {
        auto start = std::chrono::high_resolution_clock::now();
        auto result = allocator.allocate_optimal_global(cfg, graph, type);
        auto end = std::chrono::high_resolution_clock::now();
        double time_ms = std::chrono::duration<double, std::milli>(end - start).count();
        std::cout << name << ": Spills=" << result.num_spills << " Time=" << time_ms << "ms\n";
    };

    auto future = std::async(std::launch::async, task);
    if (future.wait_for(std::chrono::seconds(60)) == std::future_status::timeout) {
        std::cout << name << ": TIMEOUT (>60s)\n";
    } else {
        future.get();
    }
}

int main() {
    // ---------------------------------------------------------
    // Metaheuristic Suite (256 Random Clique Problems)
    // ---------------------------------------------------------
    {
    std::cout << "\n[Metaheuristics] Running 256 Random Clique Problems (K=10..30)...\n";
    
    // Stats accumulators
    struct MethodStats {
        long long total_spills = 0;
        double total_time_ms = 0.0;
        int wins = 0; 
    };
    
    std::map<std::string, MethodStats> stats;
    std::vector<std::string> methods = {"Tabu", "SA", "GA", "PSO", "TabuBit", "GLS", "GLSBit", "SafetyNet", "Heuristic"};
    
    // Define num_regs local to this scope
    const uint32_t num_regs = 32;
    
    // Using simple random seed
    std::srand(12345);
    
    for (int i = 0; i < 256; ++i) {
        // Generate random K in [10, 30]
        int k = 10 + (std::rand() % 21);
        InterferenceGraph graph = generate_clique(k);
        LivenessInfo live; 
        ControlFlowGraph cfg_dummy; 
        
        // Dummy spill costs (all 1.0)
        std::unordered_map<uint32_t, double> spill_costs;
        for(int v=0; v<k; ++v) spill_costs[v] = 1.0;
        
        int best_spills_this_problem = 9999;
        std::map<std::string, int> current_spills;
        
        // Run each method
        for (const auto& method : methods) {
            auto start = std::chrono::high_resolution_clock::now();
            int spills = 0;
            
            if (method == "Tabu") {
                TabuSearchSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "SA") {
                SimulatedAnnealingSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "GA") {
                GeneticAlgorithmSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "PSO") {
                ParticleSwarmSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "TabuBit") {
                TabuSearchBitSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "GLS") {
                GuidedLocalSearchSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "GLSBit") {
                GuidedLocalSearchBitSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "SafetyNet") {
                SafetyNetWalkSolver solver;
                auto res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
                spills = res.num_spills;
            } else if (method == "Heuristic") {
                // Use inline greedy heuristic
                std::vector<int> color(k, -1);
                int spill_cnt = 0;
                for(int v=0; v<k; ++v) {
                    std::vector<bool> used(num_regs, false);
                    for(int n=0; n<v; ++n) if(graph.edges.at(v).count(n) && color[n]>=0) used[color[n]] = true;
                    int c = -1;
                    for(uint32_t r=0; r<num_regs; ++r) if(!used[r]) { c=r; break; }
                    color[v] = c;
                    if(c==-1) spill_cnt++;
                }
                spills = spill_cnt;
            }
            
            auto end = std::chrono::high_resolution_clock::now();
            double time = std::chrono::duration<double, std::milli>(end - start).count();
            
            stats[method].total_spills += spills;
            stats[method].total_time_ms += time;
            current_spills[method] = spills;
            
            if (spills < best_spills_this_problem) best_spills_this_problem = spills;
        }
        
        // Count wins
        for (const auto& method : methods) {
            if (current_spills[method] == best_spills_this_problem) {
                stats[method].wins++;
            }
        }
        
        if (i % 32 == 0) std::cout << "Done " << i << "/256\r" << std::flush;
    }
    
    std::cout << "\nResults (256 problems):\n";
    std::cout << "Method      | Total Spills | Total Time (ms) | Wins (Lowest Spills)\n";
    std::cout << "---------------------------------------------------------------\n";
    for (const auto& method : methods) {
        printf("%-11s | %-12lld | %-15.2f | %d\n", 
               method.c_str(), stats[method].total_spills, stats[method].total_time_ms, stats[method].wins);
    }
    } // End Metaheuristic scope

    std::cout << "\nBackend Comparison Benchmark (Max 60s per test)\n";
    std::cout << "=============================================\n";
    
    // ---------------------------------------------------------
    // Local Benchmark
    // ---------------------------------------------------------
    ControlFlowGraph cfg_dummy;
    LivenessInfo live_dummy;
    uint32_t num_regs = 8;
    GraphColoringAllocator allocator(num_regs);
    
    std::vector<uint32_t> sizes = {12, 16};
    
    for (uint32_t k : sizes) {
        std::cout << "\n[Local] Clique Size " << k << "\n";
        InterferenceGraph graph = generate_clique(k);
        live_dummy.ranges.clear();
        for(uint32_t i=0; i<k; ++i) live_dummy.ranges.push_back({0, 100, i});
        
        run_local_test("Newton (AMX Sp) ", allocator, cfg_dummy, live_dummy, graph, GraphColoringAllocator::SolverType::Newton_AMX);
        run_local_test("Newton (AMX De) ", allocator, cfg_dummy, live_dummy, graph, GraphColoringAllocator::SolverType::Newton_AMXDense);
        run_local_test("Newton (Sparse)", allocator, cfg_dummy, live_dummy, graph, GraphColoringAllocator::SolverType::Newton_Sparse);
        run_local_test("Newton (Dense) ", allocator, cfg_dummy, live_dummy, graph, GraphColoringAllocator::SolverType::Newton_Dense);
    }
    
    // ---------------------------------------------------------
    // Global Benchmark
    // ---------------------------------------------------------
    std::cout << "\n[Global] Multi-Function Clique\n";
    GlobalRegisterAllocator global_allocator(num_regs);
    GlobalCFG global_cfg;
    
    // Function 1: Clique 10 (spills 2)
    ControlFlowGraph func1;
    for(uint32_t i=0; i<10; ++i) func1.variables[i] = {};
    global_cfg.functions.push_back(func1);
    
    // Function 2: Clique 10 (spills 2)
    ControlFlowGraph func2;
    for(uint32_t i=0; i<10; ++i) func2.variables[i] = {};
    global_cfg.functions.push_back(func2);
    
    GlobalInterferenceGraph global_graph;
    global_graph.num_variables = 20;
    
    // Build Clique 1 (vars 0-9)
    for(uint32_t i=0; i<10; ++i) {
        global_graph.var_to_function[i] = 0;
        for(uint32_t j=i+1; j<10; ++j) {
            global_graph.edges[i].insert(j);
            global_graph.edges[j].insert(i);
        }
    }
    // Build Clique 2 (vars 10-19)
    for(uint32_t i=10; i<20; ++i) {
        global_graph.var_to_function[i] = 1;
        for(uint32_t j=i+1; j<20; ++j) {
            global_graph.edges[i].insert(j);
            global_graph.edges[j].insert(i);
        }
    }
    
    run_global_test("Global (AMX Sp) ", global_allocator, global_cfg, global_graph, GraphColoringAllocator::SolverType::Newton_AMX);
    run_global_test("Global (AMX De) ", global_allocator, global_cfg, global_graph, GraphColoringAllocator::SolverType::Newton_AMXDense);

    return 0;
}
