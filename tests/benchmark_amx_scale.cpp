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
#include <iomanip>

using namespace optreg;

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

struct BenchResult {
    double time_ms;
    uint32_t spills;
};

BenchResult run_solver(GraphColoringAllocator& allocator, 
                     const ControlFlowGraph& cfg, const LivenessInfo& live, const InterferenceGraph& graph,
                     GraphColoringAllocator::SolverType type) {
    auto start = std::chrono::high_resolution_clock::now();
    auto result = allocator.allocate_optimal(cfg, live, graph, type);
    auto end = std::chrono::high_resolution_clock::now();
    double time_ms = std::chrono::duration<double, std::milli>(end - start).count();
    return {time_ms, result.num_spills};
}

BenchResult run_meta(const std::string& method, const InterferenceGraph& graph, uint32_t num_regs) {
    ControlFlowGraph cfg_dummy;
    std::unordered_map<uint32_t, double> spill_costs;
    for(uint32_t v=0; v<graph.num_variables; ++v) spill_costs[v] = 1.0;
    
    auto start = std::chrono::high_resolution_clock::now();
    RegisterAllocation res;
    if (method == "SafetyNet") {
        SafetyNetWalkSolver solver;
        res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
    } else if (method == "TabuBit") {
        TabuSearchBitSolver solver;
        res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
    } else if (method == "GLSBit") {
        GuidedLocalSearchBitSolver solver;
        res = solver.solve(cfg_dummy, graph, num_regs, spill_costs);
    } else {
        // Simple Greedy
        std::vector<int> color(graph.num_variables, -1);
        int spill_cnt = 0;
        for(uint32_t v=0; v<graph.num_variables; ++v) {
            std::vector<bool> used(num_regs, false);
            if (graph.edges.count(v)) {
                for(int n : graph.edges.at(v)) if(n < (int)v && color[n]>=0) used[color[n]] = true;
            }
            int c = -1;
            for(uint32_t r=0; r<num_regs; ++r) if(!used[r]) { c=r; break; }
            color[v] = c;
            if(c==-1) spill_cnt++;
        }
        res.num_spills = spill_cnt;
    }
    auto end = std::chrono::high_resolution_clock::now();
    double time_ms = std::chrono::duration<double, std::milli>(end - start).count();
    return {time_ms, res.num_spills};
}

int main() {
    uint32_t num_regs = 32;
    GraphColoringAllocator allocator(num_regs);
    ControlFlowGraph cfg_dummy;
    LivenessInfo live_dummy;
    
    std::cout << std::fixed << std::setprecision(2);
    std::cout << "--- Scaling Benchmark: Finding AMX 4s Threshold ---\n";
    
    auto find_limit = [&](GraphColoringAllocator::SolverType type, const std::string& label) {
        uint32_t k = 10;
        double last_time = 0;
        while (k < 1000) {
            InterferenceGraph graph = generate_clique(k);
            live_dummy.ranges.clear();
            for(uint32_t i=0; i<k; ++i) live_dummy.ranges.push_back({0, 100, i});
            
            auto res = run_solver(allocator, cfg_dummy, live_dummy, graph, type);
            std::cout << label << " K=" << k << " Time=" << res.time_ms << "ms\n";
            last_time = res.time_ms;
            if (res.time_ms > 4000.0) break;
            
            if (res.time_ms < 50) k += 5;
            else if (res.time_ms < 500) k += 10;
            else k += 20;
        }
        return k;
    };

    uint32_t k_sparse = find_limit(GraphColoringAllocator::SolverType::Newton_AMX, "AMX Sparse");
    uint32_t k_dense = find_limit(GraphColoringAllocator::SolverType::Newton_AMXDense, "AMX Dense ");

    std::cout << "\n--- Scaling Global Benchmark: Finding AMX 4s Threshold ---\n";
    auto find_limit_global = [&](GraphColoringAllocator::SolverType type, const std::string& label) {
        uint32_t num_funcs = 1;
        uint32_t k = 10; // Use K=10 for global scaling
        while (num_funcs < 200) {
            GlobalRegisterAllocator g_allocator(num_regs);
            GlobalCFG g_cfg;
            GlobalInterferenceGraph g_graph;
            g_graph.num_variables = num_funcs * k;
            
            for (uint32_t f = 0; f < num_funcs; ++f) {
                ControlFlowGraph func;
                for(uint32_t i=0; i<k; ++i) func.variables[f*k + i] = {};
                g_cfg.functions.push_back(func);
                for(uint32_t i=0; i<k; ++i) {
                    g_graph.var_to_function[f*k + i] = f;
                    for(uint32_t j=i+1; j<k; ++j) {
                        g_graph.edges[f*k + i].insert(f*k + j);
                        g_graph.edges[f*k + j].insert(f*k + i);
                    }
                }
            }
            
            auto start = std::chrono::high_resolution_clock::now();
            auto res = g_allocator.allocate_optimal_global(g_cfg, g_graph, type);
            auto end = std::chrono::high_resolution_clock::now();
            double time_ms = std::chrono::duration<double, std::milli>(end - start).count();
            
            std::cout << label << " Funcs=" << num_funcs << " (m=" << (num_funcs * (10 + 45*32)) << ") Time=" << time_ms << "ms\n";
            if (time_ms > 4000.0) break;
            
            if (time_ms < 100) num_funcs += 2;
            else if (time_ms < 1000) num_funcs += 5;
            else num_funcs += 10;
        }
        return num_funcs;
    };

    uint32_t g_funcs_sparse = find_limit_global(GraphColoringAllocator::SolverType::Newton_AMX, "Global AMX Sparse");
    uint32_t g_funcs_dense = find_limit_global(GraphColoringAllocator::SolverType::Newton_AMXDense, "Global AMX Dense ");

    std::cout << "\n--- Final Comparison at Scale ---\n";
    auto compare = [&](uint32_t k, const std::string& label) {
        std::cout << "\nTesting " << label << " at K=" << k << "\n";
        InterferenceGraph graph = generate_clique(k);
        live_dummy.ranges.clear();
        for(uint32_t i=0; i<k; ++i) live_dummy.ranges.push_back({0, 100, i});

        auto amx = run_solver(allocator, cfg_dummy, live_dummy, graph, 
                            label == "AMX Sparse" ? GraphColoringAllocator::SolverType::Newton_AMX : GraphColoringAllocator::SolverType::Newton_AMXDense);
        std::cout << label << ": Spills=" << amx.spills << " Time=" << amx.time_ms << "ms\n";

        std::vector<std::string> metas = {"SafetyNet", "TabuBit", "GLSBit", "Heuristic"};
        for(const auto& m : metas) {
            auto res = run_meta(m, graph, num_regs);
            std::cout << m << " : Spills=" << res.spills << " Time=" << res.time_ms << "ms ";
            if (amx.spills < res.spills) {
                std::cout << "(AMX wins by " << (res.spills - amx.spills) << " spills)";
            } else if (amx.spills > res.spills) {
                std::cout << "(Heuristic wins by " << (amx.spills - res.spills) << " spills)";
            } else {
                std::cout << "(Tie in spills)";
            }
            std::cout << "\n";
        }
    };

    compare(k_sparse, "AMX Sparse");
    compare(k_dense, "AMX Dense");

    auto compare_global = [&](uint32_t num_funcs, uint32_t k, const std::string& label) {
        std::cout << "\nTesting GLOBAL " << label << " with " << num_funcs << " functions (K=" << k << ")\n";
        
        GlobalRegisterAllocator g_allocator(num_regs);
        GlobalCFG g_cfg;
        GlobalInterferenceGraph g_graph;
        g_graph.num_variables = num_funcs * k;

        for (uint32_t f = 0; f < num_funcs; ++f) {
            ControlFlowGraph func;
            for(uint32_t i=0; i<k; ++i) func.variables[f*k + i] = {};
            g_cfg.functions.push_back(func);
            for(uint32_t i=0; i<k; ++i) {
                g_graph.var_to_function[f*k + i] = f;
                for(uint32_t j=i+1; j<k; ++j) {
                    g_graph.edges[f*k + i].insert(f*k + j);
                    g_graph.edges[f*k + j].insert(f*k + i);
                }
            }
        }

        auto start = std::chrono::high_resolution_clock::now();
        auto amx = g_allocator.allocate_optimal_global(g_cfg, g_graph, 
                            label.find("Sparse") != std::string::npos ? GraphColoringAllocator::SolverType::Newton_AMX : GraphColoringAllocator::SolverType::Newton_AMXDense);
        auto end = std::chrono::high_resolution_clock::now();
        double amx_time = std::chrono::duration<double, std::milli>(end - start).count();
        std::cout << label << ": Spills=" << amx.num_spills << " Time=" << amx_time << "ms\n";

        // Heuristics are usually local, so we run them per function for global comparison
        std::vector<std::string> metas = {"SafetyNet", "TabuBit", "GLSBit", "Heuristic"};
        for(const auto& m : metas) {
            uint32_t total_spills = 0;
            auto meta_start = std::chrono::high_resolution_clock::now();
            for (uint32_t f = 0; f < num_funcs; ++f) {
                InterferenceGraph f_graph;
                f_graph.num_variables = k;
                for(uint32_t i=0; i<k; ++i) {
                    for(uint32_t j=i+1; j<k; ++j) {
                        f_graph.edges[i].insert(j);
                        f_graph.edges[j].insert(i);
                    }
                }
                auto res = run_meta(m, f_graph, num_regs);
                total_spills += res.spills;
            }
            auto meta_end = std::chrono::high_resolution_clock::now();
            double meta_time = std::chrono::duration<double, std::milli>(meta_end - meta_start).count();
            std::cout << m << " : Spills=" << total_spills << " Time=" << meta_time << "ms ";
            if (amx.num_spills < total_spills) std::cout << "(AMX wins)";
            else if (amx.num_spills > total_spills) std::cout << "(Heuristic wins)";
            else std::cout << "(Tie)";
            std::cout << "\n";
        }
    };

    compare_global(g_funcs_sparse, 20, "Global AMX Sparse");
    compare_global(g_funcs_dense, 20, "Global AMX Dense");

    return 0;
}
