#include "global_allocator.h"
#include "graph_coloring.h"
#include "ir_parser.h"
#include <iostream>
#include <chrono>

using namespace optreg;

// Test global allocator on merge sort
int main() {
    std::cout << "Merge Sort Register Allocation Comparison\n";
    std::cout << "==========================================\n\n";
    
    // Simulate merge sort IR with 3 functions:
    // 1. compare(a, b)
    // 2. merge(arr, left, mid, right)
    // 3. mergeSort(arr, left, right)
    
    GlobalCFG cfg;
    cfg.function_names[0] = "compare";
    cfg.function_names[1] = "merge";
    cfg.function_names[2] = "mergeSort";
    
    // Function 0: compare (2 vars, simple)
    {
        ControlFlowGraph func;
        func.entry_block = 0;
        BasicBlock bb;
        bb.id = 0;
        
        for (uint32_t i = 0; i < 2; ++i) {
            Variable v;
            v.id = i;
            v.name = "v" + std::to_string(i);
            v.def_point = i;
            v.last_use = i + 1;
            func.variables[i] = v;
        }
        func.blocks.push_back(bb);
        cfg.functions.push_back(func);
    }
    
    // Function 1: merge (15 vars, complex with loops)
    {
        ControlFlowGraph func;
        func.entry_block = 0;
        BasicBlock bb;
        bb.id = 0;
        
        for (uint32_t i = 0; i < 15; ++i) {
            Variable v;
            v.id = i;
            v.name = "v" + std::to_string(i);
            v.def_point = i;
            v.last_use = i + 10;  // Long-lived
            func.variables[i] = v;
        }
        func.blocks.push_back(bb);
        cfg.functions.push_back(func);
    }
    
    // Function 2: mergeSort (8 vars, recursive calls)
    {
        ControlFlowGraph func;
        func.entry_block = 0;
        BasicBlock bb;
        bb.id = 0;
        
        for (uint32_t i = 0; i < 8; ++i) {
            Variable v;
            v.id = i;
            v.name = "v" + std::to_string(i);
            v.def_point = i;
            v.last_use = i + 5;
            func.variables[i] = v;
        }
        func.blocks.push_back(bb);
        cfg.functions.push_back(func);
    }
    
    // Add call sites
    // mergeSort calls merge (vars 0,1,2,3 live)
    CallSite call1;
    call1.caller_func = 2;
    call1.callee_func = 1;
    call1.live_at_call = {0, 1, 2, 3};
    cfg.call_sites.push_back(call1);
    
    // mergeSort calls itself recursively (vars 0,1, 2 live)
    CallSite call2;
    call2.caller_func = 2;
    call2.callee_func = 2;
    call2.live_at_call = {0, 1, 2};
    cfg.call_sites.push_back(call2);
    
    uint32_t num_registers = 8;
    
    // Build global interference graph
    GlobalRegisterAllocator global_alloc(num_registers);
    auto global_graph = global_alloc.build_global_graph(cfg);
    
    std::cout << "Global interference graph:\n";
    std::cout << "  Total variables: " << global_graph.num_variables << "\n";
    std::cout << "  Total edges: " << (global_graph.edges.size() / 2) << "\n\n";
    
    // Strategy 1: Local heuristic (per-function)
    std::cout << "Strategy 1: Local Heuristic\n";
    std::cout << "----------------------------\n";
    auto start1 = std::chrono::high_resolution_clock::now();
    
    uint32_t local_total_spills = 0;
    for (size_t i = 0; i < cfg.functions.size(); ++i) {
        auto liveness = compute_liveness(cfg.functions[i]);
        auto local_graph = build_interference_graph(liveness, cfg.functions[i]);
        
        GraphColoringAllocator local_alloc(num_registers);
        // Note: Would use heuristic here, using optimal for now
        auto result = local_alloc.allocate_optimal(cfg.functions[i], liveness, local_graph);
        local_total_spills += result.num_spills;
        
        std::cout << "  " << cfg.function_names[i] << ": " 
                  << result.num_spills << " spills\n";
    }
    
    auto end1 = std::chrono::high_resolution_clock::now();
    auto time1 = std::chrono::duration_cast<std::chrono::microseconds>(end1 - start1);
    
    std::cout << "Total spills: " << local_total_spills << "\n";
    std::cout << "Time: " << time1.count() << " μs\n\n";
    
    // Strategy 2: Global heuristic
    std::cout << "Strategy 2: Global Heuristic\n";
    std::cout << "----------------------------\n";
    auto start2 = std::chrono::high_resolution_clock::now();
    
    auto global_heur_result = global_alloc.allocate_heuristic_global(cfg, global_graph);
    
    auto end2 = std::chrono::high_resolution_clock::now();
    auto time2 = std::chrono::duration_cast<std::chrono::microseconds>(end2 - start2);
    
    std::cout << "Total spills: " << global_heur_result.num_spills << "\n";
    std::cout << "Time: " << time2.count() << " μs\n\n";
    
    // Strategy 3: Global optimal
    std::cout << "Strategy 3: Global Optimal (LP)\n";
    std::cout << "--------------------------------\n";
    auto start3 = std::chrono::high_resolution_clock::now();
    
    auto global_opt_result = global_alloc.allocate_optimal_global(cfg, global_graph);
    
    auto end3 = std::chrono::high_resolution_clock::now();
    auto time3 = std::chrono::duration_cast<std::chrono::microseconds>(end3 - start3);
    
    std::cout << "Total spills: " << global_opt_result.num_spills << "\n";
    std::cout << "Time: " << time3.count() << " μs\n\n";
    
    // Summary
    std::cout << "=== Comparison Summary ===\n";
    std::cout << "Local heuristic:  " << local_total_spills << " spills, " 
              << time1.count() << " μs\n";
    std::cout << "Global heuristic: " << global_heur_result.num_spills << " spills, "
              << time2.count() << " μs (speedup: " 
              << (double(time1.count()) / time2.count()) << "x)\n";
    std::cout << "Global optimal:   " << global_opt_result.num_spills << " spills, "
              << time3.count() << " μs\n\n";
    
    double improvement_global = 100.0 * (local_total_spills - global_heur_result.num_spills) 
                                / local_total_spills;
    double improvement_opt = 100.0 * (local_total_spills - global_opt_result.num_spills)
                             / local_total_spills;
    
    std::cout << "Global heuristic improvement: " << improvement_global << "%\n";
    std::cout << "Global optimal improvement:   " << improvement_opt << "%\n";
    
    return 0;
}
