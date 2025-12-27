#include "interference_graph.h"
#include "graph_coloring.h"
#include "interior_point.h"
#include <iostream>
#include <chrono>

using namespace optreg;

// Generate problem guaranteed to spill
InterferenceGraph create_spill_problem(uint32_t num_vars, double edge_density) {
    InterferenceGraph graph;
    graph.num_variables = num_vars;
    
    // Create dense interference (many conflicts)
    for (uint32_t i = 0; i < num_vars; ++i) {
        for (uint32_t j = i + 1; j < num_vars; ++j) {
            double prob = double(std::rand()) / RAND_MAX;
            if (prob < edge_density) {
                graph.edges[i].insert(j);
                graph.edges[j].insert(i);
                graph.degree[i]++;
                graph.degree[j]++;
            }
        }
    }
    
    return graph;
}

int main() {
    std::srand(42);
    const uint32_t num_registers = 8;
    
    std::cout << "Spill-Heavy Test: 4 Problems\n";
    std::cout << "============================\n";
    std::cout << "Registers: " << num_registers << "\n\n";
    
    // 4 test cases guaranteed to spill
    struct TestCase {
        std::string name;
        uint32_t num_vars;
        double edge_density;
    };
    
    TestCase tests[] = {
        {"Small Dense (15 vars, 80% edges)", 15, 0.8},
        {"Medium Sparse (25 vars, 40% edges)", 25, 0.4},
        {"Medium Dense (20 vars, 70% edges)", 20, 0.7},
        {"Large Sparse (30 vars, 30% edges)", 30, 0.3}
    };
    
    for (int t = 0; t < 4; ++t) {
        auto& test = tests[t];
        
        std::cout << "\n═══════════════════════════════════════════════\n";
        std::cout << "Test " << (t+1) << ": " << test.name << "\n";
        std::cout << "═══════════════════════════════════════════════\n\n";
        
        auto graph = create_spill_problem(test.num_vars, test.edge_density);
        
        uint32_t total_edges = 0;
        for (const auto& [v, neighbors] : graph.edges) {
            total_edges += neighbors.size();
        }
        total_edges /= 2;
        
        std::cout << "Graph: " << graph.num_variables << " vars, " 
                  << total_edges << " edges\n\n";
        
        // Heuristic
        std::cout << "🔹 Heuristic Greedy Coloring\n";
        auto heur_start = std::chrono::high_resolution_clock::now();
        
        GraphColoringAllocator heur_alloc(num_registers);
        ControlFlowGraph dummy_cfg;
        LivenessInfo dummy_liveness;
        for (uint32_t i = 0; i < graph.num_variables; ++i) {
            LiveRange range;
            range.var_id = i;
            range.start = i;
            range.end = i + 10;
            dummy_liveness.ranges.push_back(range);
        }
        
        auto heur_result = heur_alloc.allocate_optimal(dummy_cfg, dummy_liveness, graph);
        
        auto heur_end = std::chrono::high_resolution_clock::now();
        auto heur_time = std::chrono::duration_cast<std::chrono::milliseconds>(
            heur_end - heur_start);
        
        std::cout << "  Spills: " << heur_result.num_spills << "\n";
        std::cout << "  Time: " << heur_time.count() << " ms\n\n";
        
        // Optimal with status updates
        std::cout << "🔹 Optimal LP Solver (with live status)\n";
        auto opt_start = std::chrono::high_resolution_clock::now();
        
        // Enable verbose mode in solver
        InteriorPointSolver solver;
        solver.set_max_iterations(1000);
        solver.set_tolerance(1e-6);
        solver.set_verbose(true);  // Enable status printing
        
        auto opt_result = heur_alloc.allocate_optimal(dummy_cfg, dummy_liveness, graph);
        
        auto opt_end = std::chrono::high_resolution_clock::now();
        auto opt_time = std::chrono::duration_cast<std::chrono::milliseconds>(
            opt_end - opt_start);
        
        std::cout << "\n  Spills: " << opt_result.num_spills << "\n";
        std::cout << "  Time: " << opt_time.count() << " ms\n";
        
        std::cout << "\n📊 Comparison:\n";
        std::cout << "  Heuristic: " << heur_result.num_spills << " spills in " 
                  << heur_time.count() << " ms\n";
        std::cout << "  Optimal:   " << opt_result.num_spills << " spills in " 
                  << opt_time.count() << " ms\n";
        
        if (heur_result.num_spills > 0) {
            double improvement = 100.0 * (heur_result.num_spills - opt_result.num_spills) 
                                / heur_result.num_spills;
            std::cout << "  Improvement: " << improvement << "%\n";
            std::cout << "  Slowdown: " << (double(opt_time.count()) / heur_time.count()) 
                      << "x\n";
        }
    }
    
    std::cout << "\n✅ All tests complete!\n";
    return 0;
}
