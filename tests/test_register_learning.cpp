#include <iostream>
#include <vector>
#include <string>
#include <chrono>
#include <random>
#include <fstream>
#include <numeric>
#include <algorithm>
#include <map>
#include <iomanip>
#include <queue>
#include <set>
#include <cmath>

#include "problem_types.hpp"
#include "solver_base.hpp"
#include <Accelerate/Accelerate.h> // For AMX Simulation

using namespace optsolve;

// ============================================================================
// Utilities
// ============================================================================

// Mock AMX Relaxation
void simulate_amx_relaxation(size_t m, size_t n, bool aligned) {
    if (m == 0 || n == 0) return;
    // Simulate low-level matrix ops cost
    // 1000 ops ~ 1 microsecond?
    // Just a tiny busy loop or volatile write to prevent optimization
    volatile int x = 0;
    for(int i=0; i<10; ++i) x++;
}

// Compute Node Clustering Coefficient
double get_clustering_coeff(size_t v, const std::vector<std::vector<bool>>& adj, size_t n) {
    std::vector<size_t> neighbors;
    for(size_t i=0; i<n; ++i) {
        if (i!=v && adj[v][i]) neighbors.push_back(i);
    }
    size_t k = neighbors.size();
    if (k < 2) return 0.0;
    
    size_t edges = 0;
    for(size_t i=0; i<k; ++i) {
        for(size_t j=i+1; j<k; ++j) {
            if (adj[neighbors[i]][neighbors[j]]) edges++;
        }
    }
    return (2.0 * edges) / (double)(k * (k-1));
}

// ============================================================================
// Correct BnB Solver with Timeout
// ============================================================================

class GraphColoringBnB_WithTimeout : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Coloring_BnB_Timeout"; }
    
    // Config
    double timeout_seconds = 1.0;
    bool timed_out = false;
    
protected:
    struct Node {
        std::vector<size_t> colors; // colors[i] or 0 if unassigned
        int level;
        size_t max_color_used;
        double lb;
        bool operator>(const Node& o) const { return lb > o.lb; }
    };
    
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        auto start_time = std::chrono::steady_clock::now();
        timed_out = false;
        
        std::vector<std::vector<bool>> adj(p.n_vertices, std::vector<bool>(p.n_vertices, false));
        for(auto& e : p.edges) { adj[e.first][e.second] = adj[e.second][e.first] = true; }
        
        // Initial Solution (Greedy/DSatur) to set UB
        // Simple Greedy
        std::vector<size_t> greedy_colors(p.n_vertices, 0);
        size_t greedy_max = 0;
        for(size_t i=0; i<p.n_vertices; ++i) {
            std::vector<bool> used(p.n_vertices + 1, false);
            for(size_t j=0; j<i; ++j) {
                if(adj[i][j]) used[greedy_colors[j]] = true;
            }
            size_t c = 1;
            while(used[c]) c++;
            greedy_colors[i] = c;
            if(c > greedy_max) greedy_max = c;
        }
        
        size_t best_colors_count = greedy_max;
        std::vector<size_t> best_sol = greedy_colors;
        
        std::priority_queue<Node, std::vector<Node>, std::greater<Node>> pq;
        Node root;
        root.colors.assign(p.n_vertices, 0);
        root.level = 0;
        root.max_color_used = 0;
        root.lb = 1;
        pq.push(root);
        
        m.iterations = 0;
        
        while(!pq.empty()) {
            // Check Timeout
            if (m.iterations % 100 == 0) {
                auto now = std::chrono::steady_clock::now();
                if (std::chrono::duration<double>(now - start_time).count() > timeout_seconds) {
                    timed_out = true;
                    break;
                }
            }
            
            Node curr = pq.top(); pq.pop();
            m.iterations++;
            
            if (curr.lb >= best_colors_count) continue;
            
            if (curr.level == p.n_vertices) {
                if (curr.max_color_used < best_colors_count) {
                    best_colors_count = curr.max_color_used;
                    best_sol = curr.colors;
                }
                continue;
            }
            
            // Branch: Assign color to vertex 'level'
            size_t v = curr.level;
            
            // Simple logic: Try colors 1..max_used+1
            // Optimization: AMX Sim
            simulate_amx_relaxation(10, 10, false);
            
            for(size_t c=1; c <= curr.max_color_used + 1; ++c) {
                if (c >= best_colors_count) break;
                
                // Check conflict
                bool conflict = false;
                for(size_t u=0; u<v; ++u) {
                    if (adj[v][u] && curr.colors[u] == c) {
                        conflict = true;
                        break;
                    }
                }
                if (conflict) continue;
                
                Node child = curr;
                child.colors[v] = c;
                child.level++;
                child.max_color_used = std::max(child.max_color_used, c);
                child.lb = child.max_color_used; // Simple LB. 
                // Better LB: max clique in remaining graph? Too slow.
                // Or DSatur of remaining?
                
                pq.push(child);
            }
        }
        
        val.colors = best_sol;
        val.num_colors = best_colors_count;
        m.objective_value = best_colors_count;
        return true; // Return valid (possibly suboptimal if timed out)
    }
};

// ============================================================================
// Main
// ============================================================================

int main() {
    std::cout << "Starting Register Allocation Learning Generation...\n";
    std::ofstream csv("register_data.csv");
    csv << "inst_id,node_id,degree,clustering,neighbor_deg_avg,solution_color,is_optimal,time_ms\n";
    
    std::mt19937 rng(12345);
    GraphColoringBnB_WithTimeout solver;
    solver.timeout_seconds = 1.0;
    
    int optimal_count = 0;
    int timeout_count = 0;
    
    for(int i=0; i<1024; ++i) {
        // N=50 is roughly register count for heavy kernels (vector regs etc)
        // Density 0.2
        int n = 50; 
        // Generate with specific seed for reproducibility
        GraphColoringProblem p = GraphColoringProblem::random(n, 0.2, i);
        
        // Solve
        auto t1 = std::chrono::high_resolution_clock::now();
        
        auto res = solver.solve(p);
        GraphColoringSolution sol = res.solution;
        SolverMetrics m = res.metrics;
        
        auto t2 = std::chrono::high_resolution_clock::now();
        double ms = std::chrono::duration<double>(t2 - t1).count() * 1000.0;
        
        bool is_optimal = !solver.timed_out;
        if (solver.timed_out) timeout_count++;
        else optimal_count++;
        
        // Log Features
        // 1. Build Adjacency
        std::vector<std::vector<bool>> adj(n, std::vector<bool>(n, false));
        std::vector<int> degrees(n, 0);
        for(auto& e : p.edges) {
            adj[e.first][e.second] = adj[e.second][e.first] = true;
            degrees[e.first]++;
            degrees[e.second]++;
        }
        
        for(size_t u=0; u<n; ++u) {
            double clust = get_clustering_coeff(u, adj, n);
            double neigh_deg_sum = 0;
            for(size_t v=0; v<n; ++v) {
                if (adj[u][v]) neigh_deg_sum += degrees[v];
            }
            double neigh_deg_avg = degrees[u] > 0 ? neigh_deg_sum / degrees[u] : 0;
            
            // Log
            csv << i << "," 
                << u << "," 
                << degrees[u] << "," 
                << clust << "," 
                << neigh_deg_avg << "," 
                << sol.colors[u] << "," 
                << (is_optimal ? 1 : 0) << ","
                << ms << "\n";
        }
        
        if (i % 50 == 0) {
            std::cout << "Processed " << i << " instances. Optimal: " << optimal_count << ", Timeout: " << timeout_count << "\n";
        }
    }
    
    csv.close();
    std::cout << "Done. Data saved to register_data.csv\n";
    std::cout << "Total Optimal Solutions in <1s: " << optimal_count << "/" << 1024 << "\n";
    
    return 0;
}
