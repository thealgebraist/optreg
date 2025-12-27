#include "interference_graph.h"
#include "live_range.h"
#include "graph_coloring.h"
#include "interior_point.h"
#include <iostream>
#include <random>
#include <chrono>
#include <vector>
#include <algorithm>

using namespace optreg;

// Generate random interference graph
InterferenceGraph generate_random_graph(
    uint32_t num_vars, 
    double edge_probability,
    std::mt19937& rng
) {
    InterferenceGraph graph;
    graph.num_variables = num_vars;
    
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    
    // Add random edges
    for (uint32_t i = 0; i < num_vars; ++i) {
        for (uint32_t j = i + 1; j < num_vars; ++j) {
            if (dist(rng) < edge_probability) {
                graph.edges[i].insert(j);
                graph.edges[j].insert(i);
                graph.degree[i]++;
                graph.degree[j]++;
            }
        }
    }
    
    return graph;
}

// Heuristic allocator: greedy graph coloring
struct HeuristicResult {
    uint32_t colors_used;
    uint32_t spills;
    std::chrono::microseconds time_us;
};

HeuristicResult solve_heuristic(
    const InterferenceGraph& graph,
    uint32_t num_registers
) {
    auto start = std::chrono::high_resolution_clock::now();
    
    // Greedy coloring with degree ordering
    std::vector<std::pair<uint32_t, uint32_t>> vars_by_degree;
    for (uint32_t v = 0; v < graph.num_variables; ++v) {
        uint32_t deg = graph.degree.count(v) ? graph.degree.at(v) : 0;
        vars_by_degree.push_back({deg, v});
    }
    
    // Sort by degree (descending)
    std::sort(vars_by_degree.rbegin(), vars_by_degree.rend());
    
    std::vector<uint32_t> color(graph.num_variables, UINT32_MAX);
    uint32_t max_color = 0;
    
    for (const auto& [deg, v] : vars_by_degree) {
        // Find smallest color not used by neighbors
        std::vector<bool> used_colors(num_registers + 1, false);
        
        const auto& neighbors = graph.edges.count(v) ? graph.edges.at(v) : std::unordered_set<uint32_t>{};
        for (uint32_t neighbor : neighbors) {
            if (color[neighbor] != UINT32_MAX && color[neighbor] < num_registers) {
                used_colors[color[neighbor]] = true;
            }
        }
        
        // Assign smallest available color
        for (uint32_t c = 0; c <= num_registers; ++c) {
            if (!used_colors[c]) {
                color[v] = c;
                max_color = std::max(max_color, c);
                break;
            }
        }
    }
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
    
    // Count spills (colors >= num_registers)
    uint32_t spills = 0;
    for (uint32_t c : color) {
        if (c >= num_registers) spills++;
    }
    
    return {max_color + 1, spills, duration};
}

// Optimal allocator result
struct OptimalResult {
    uint32_t colors_used;
    uint32_t spills;
    std::chrono::microseconds time_us;
    bool timeout;
};

// Optimal allocator: LP-based graph coloring
OptimalResult solve_optimal(
    const InterferenceGraph& graph,
    uint32_t num_registers,
    std::chrono::milliseconds timeout
) {
    auto start = std::chrono::high_resolution_clock::now();
    
    // Create dummy CFG and liveness for API
    ControlFlowGraph cfg;
    cfg.entry_block = 0;
    
    LivenessInfo liveness;
    // Create live ranges from graph
    for (uint32_t v = 0; v < graph.num_variables; ++v) {
        LiveRange range;
        range.var_id = v;
        range.start = v;
        range.end = v + 10; // dummy range
        liveness.ranges.push_back(range);
    }
    
    // Use LP solver
    GraphColoringAllocator allocator(num_registers);
    auto allocation = allocator.allocate_optimal(cfg, liveness, graph);
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
    
    bool timed_out = duration > timeout;
    
    // Count actual colors used
    uint32_t max_color = 0;
    for (const auto& [v, reg] : allocation.assignment) {
        if (reg >= 0) {
            max_color = std::max(max_color, static_cast<uint32_t>(reg));
        }
    }
    
    return {
        max_color + 1,
        allocation.num_spills,
        duration,
        timed_out
    };
}

int main() {
    const uint32_t num_tests = 256;
    const uint32_t num_registers = 8;
    const auto timeout = std::chrono::milliseconds(1000); // 1 second max
    
    std::mt19937 rng(42); // Fixed seed for reproducibility
    std::uniform_int_distribution<uint32_t> var_dist(5, 20); // 5-20 variables
    std::uniform_real_distribution<double> edge_dist(0.2, 0.7); // 20-70% edge probability
    
    uint32_t heuristic_wins = 0;
    uint32_t optimal_wins = 0;
    uint32_t ties = 0;
    uint32_t timeouts = 0;
    
    uint64_t total_heuristic_time_us = 0;
    uint64_t total_optimal_time_us = 0;
    
    std::cout << "Register Allocation Benchmark (256 random tests)\n";
    std::cout << "================================================\n";
    std::cout << "Registers available: " << num_registers << "\n";
    std::cout << "Timeout per test: 1000ms\n\n";
    
    for (uint32_t test = 0; test < num_tests; ++test) {
        uint32_t num_vars = var_dist(rng);
        double edge_prob = edge_dist(rng);
        
        auto graph = generate_random_graph(num_vars, edge_prob, rng);
        
        auto heuristic_result = solve_heuristic(graph, num_registers);
        auto optimal_result = solve_optimal(graph, num_registers, timeout);
        
        total_heuristic_time_us += heuristic_result.time_us.count();
        total_optimal_time_us += optimal_result.time_us.count();
        
        if (optimal_result.timeout) {
            timeouts++;
        } else if (optimal_result.spills < heuristic_result.spills) {
            optimal_wins++;
        } else if (heuristic_result.spills < optimal_result.spills) {
            heuristic_wins++;
        } else {
            ties++;
        }
        
        // Print progress every 32 tests
        if ((test + 1) % 32 == 0) {
            std::cout << "Progress: " << (test + 1) << "/" << num_tests 
                      << " tests completed\r" << std::flush;
        }
    }
    
    std::cout << "\n\n=== Results ===\n";
    std::cout << "Heuristic wins:  " << heuristic_wins << " (" 
              << (100.0 * heuristic_wins / num_tests) << "%)\n";
    std::cout << "Optimal wins:    " << optimal_wins << " (" 
              << (100.0 * optimal_wins / num_tests) << "%)\n";
    std::cout << "Ties:            " << ties << " (" 
              << (100.0 * ties / num_tests) << "%)\n";
    std::cout << "Timeouts:        " << timeouts << " (" 
              << (100.0 * timeouts / num_tests) << "%)\n\n";
    
    double avg_heuristic = double(total_heuristic_time_us) / num_tests;
    double avg_optimal = double(total_optimal_time_us) / num_tests;
    
    std::cout << "=== Performance ===\n";
    std::cout << "Avg heuristic time: " << avg_heuristic << " μs\n";
    std::cout << "Avg optimal time:   " << avg_optimal << " μs\n";
    std::cout << "Optimal slowdown:   " << (avg_optimal / avg_heuristic) << "x\n";
    std::cout << "Total time:         " << ((total_heuristic_time_us + total_optimal_time_us) / 1000) << " ms\n\n";
    
    std::cout << "NOTE: Currently both use same greedy heuristic (100% ties expected).\n";
    std::cout << "      Implement LP solver (Tasks 5-16) for true optimal vs heuristic comparison.\n\n";
    
    std::cout << "✅ Benchmark complete!\n";
    
    return 0;
}
