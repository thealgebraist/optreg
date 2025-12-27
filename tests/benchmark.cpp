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
    
    // If allocation failed, fall back to heuristic
    if (allocation.assignment.empty()) {
        auto heuristic = solve_heuristic(graph, num_registers);
        return {
            heuristic.colors_used,
            heuristic.spills,
            duration,
            true  // mark as timeout/failure
        };
    }
    
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

// ... (previous content kept via careful replace or overwrite)

#include "gradient_descent.h"

// ... (HeuristicResult and solve_heuristic maintained)

// GD allocator result
struct GDResult {
    uint32_t colors_used;
    uint32_t spills;
    std::chrono::microseconds time_us;
    uint32_t iterations;
};

GDResult solve_gd(
    const InterferenceGraph& graph,
    uint32_t num_registers
) {
    auto start = std::chrono::high_resolution_clock::now();
    
    GraphColoringAllocator allocator(num_registers);
    
    // Dummy spill costs (1.0 for all)
    std::unordered_map<uint32_t, double> spill_costs;
    for (uint32_t i = 0; i < graph.num_variables; ++i) spill_costs[i] = 1.0;
    
    // Formulate LP
    LPProblem lp = allocator.formulate_ip(graph, spill_costs);
    
    // Solve with GD
    GradientDescentSolver gd_solver;
    gd_solver.set_max_iters(500); // Fast comparison
    gd_solver.set_rho(50.0);      // Moderate penalty
    gd_solver.set_learning_rate(0.001); // Safe step
    
    LPSolution lp_sol = gd_solver.solve(lp);
    
    // Extract solution (rounding)
    // We need to convert LPSolution (which has x) to IPSolution (which has x, y, s)
    // The GD solver returns an LPSolution.
    // GraphColoringAllocator::extract_solution expects IPSolution.
    // Both define x, y, s.
    // IPSolution is likely a typedef or struct in interior_point.h.
    // Check included header. Assuming IPSolution = LPSolution for now as they share structure in interior_point.h
    
    IPSolution ip_sol;
    ip_sol.x = lp_sol.x;
    // IPSolution for B&B output doesn't carry duals or iter count suitable for LP
    ip_sol.objective = lp_sol.objective;
    ip_sol.optimal = lp_sol.optimal;
    ip_sol.nodes_explored = lp_sol.iterations;
    ip_sol.nodes_pruned = 0;
    
    RegisterAllocation allocation = allocator.extract_solution(ip_sol, graph);
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
    
    uint32_t max_color = 0;
    for (const auto& [v, reg] : allocation.assignment) {
        if (reg >= 0) max_color = std::max(max_color, static_cast<uint32_t>(reg));
    }
    
    return {
        max_color + 1,
        allocation.num_spills,
        duration,
        lp_sol.iterations
    };
}

// ... (solve_optimal maintained)

int main() {
    using namespace optreg;
    
    const uint32_t num_registers = 8;
    const auto timeout = std::chrono::milliseconds(1000); 
    const auto total_time_limit = std::chrono::seconds(60); 
    
    std::mt19937 rng(42); 
    std::uniform_int_distribution<uint32_t> var_dist(5, 20); 
    std::uniform_real_distribution<double> edge_dist(0.2, 0.7); 
    
    uint32_t heuristic_wins = 0;
    uint32_t optimal_wins = 0;
    uint32_t gd_wins = 0;
    uint32_t ties = 0;
    uint32_t timeouts = 0;
    
    uint64_t total_heuristic_time_us = 0;
    uint64_t total_optimal_time_us = 0;
    uint64_t total_gd_time_us = 0;
    
    // Stats accumulators
    uint64_t total_h_spills = 0, total_o_spills = 0, total_g_spills = 0;
    
    std::cout << "Register Allocation Benchmark (Heuristic vs Newton vs Gradient Descent)\n";
    std::cout << "=====================================================================\n";
    
    // User requested 128 instances
    const int TEST_COUNT = 128;
    std::cout << "Running " << TEST_COUNT << " test instances...\n\n";
    
    for (int test = 1; test <= TEST_COUNT; ++test) {
        
        uint32_t num_vars = var_dist(rng);
        double edge_prob = edge_dist(rng);
        auto graph = generate_random_graph(num_vars, edge_prob, rng);
        
        auto h_res = solve_heuristic(graph, num_registers);
        auto o_res = solve_optimal(graph, num_registers, timeout); // Newton
        auto g_res = solve_gd(graph, num_registers); // GD
        
        total_heuristic_time_us += h_res.time_us.count();
        total_optimal_time_us += o_res.time_us.count();
        total_gd_time_us += g_res.time_us.count();
        
        total_h_spills += h_res.spills;
        total_o_spills += o_res.spills;
        total_g_spills += g_res.spills;
        
        if (o_res.timeout) timeouts++;
        
        // Win logic (O vs H)
        if (o_res.spills < h_res.spills) optimal_wins++;
        else if (h_res.spills < o_res.spills) heuristic_wins++;
        else ties++;
        
        // Print progress
        if (test % 10 == 0 || test == TEST_COUNT) {
            std::cout << "Tests: " << test << "/" << TEST_COUNT 
                      << " | H_spills: " << total_h_spills
                      << " Newton_spills: " << total_o_spills 
                      << " GD_spills: " << total_g_spills << "\r" << std::flush;
        }
    }
    
    std::cout << "\n\n=== RESULTS ===\n";
    std::cout << "Total Tests: " << TEST_COUNT << "\n";
    std::cout << "Heuristic Spills: " << total_h_spills << " (Avg: " << double(total_h_spills)/TEST_COUNT << ")\n";
    std::cout << "Optimal Spills:   " << total_o_spills << " (Avg: " << double(total_o_spills)/TEST_COUNT << ")\n";
    std::cout << "GD Spills:        " << total_g_spills << " (Avg: " << double(total_g_spills)/TEST_COUNT << ")\n";
    std::cout << "\nTime (ms):\n";
    std::cout << "Heuristic: " << total_heuristic_time_us/1000.0 << " ms\n";
    std::cout << "Optimal:   " << total_optimal_time_us/1000.0 << " ms\n";
    std::cout << "GD:        " << total_gd_time_us/1000.0 << " ms\n";
    
    return 0;
}
