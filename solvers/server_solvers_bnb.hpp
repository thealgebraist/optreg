#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <queue>
#include <vector>
#include <limits>
#include <memory>
#include <cmath>
#include <iostream>

namespace optsolve {

// Interface for LP Relaxation Solvers
// These solvers take a partial assignment and return a Lower Bound (LB) 
// and a proposed fractional solution for the remaining variables.
struct RelaxationResult {
    double lower_bound;
    std::vector<double> fractional_solution; // Size: n_servers * n_groups (vars for decision)
    bool feasible;
};

// Abstract Base Class for Relaxation Engines (Adapters)
class RelaxationEngine {
public:
    virtual ~RelaxationEngine() = default;
    virtual RelaxationResult solve_relaxation(const ServerProblem& problem, 
                                              const std::vector<int>& partial_assignment) = 0;
};

// Generic Branch and Bound Solver
// Template param is the Relaxation Engine (e.g. DenseAMX, SparseAcc)
template<typename RelaxerType>
class ServerBnB : public Solver<ServerProblem, ServerSolution> {
public:
    std::string _name;
    ServerBnB(std::string name_suffix) : _name("ServerBnB_" + name_suffix) {}
    
    std::string name() const override { return _name; }

    // Exposed for profiling
    size_t nodes_visited = 0;
    size_t prunings = 0;

protected:
    struct Node {
        std::vector<int> assignment; // -1 = unassigned, 0..S-1 = server
        int level; // Index of group being decided
        double lower_bound;

        // Priority Queue: Best LB first (Best-First Search) or DFS?
        // User asked for "branch and bound", typically DFS is better for memory, 
        // Best-First for minimizing node count. Let's use simple DFS (stack) or Best-First.
        // Let's use Best-First to find good solutions fast if heuristics guide it.
        bool operator>(const Node& other) const {
            return lower_bound > other.lower_bound;
        }
    };

    bool solve_impl(const ServerProblem& problem, ServerSolution& solution, SolverMetrics& metrics) override {
        nodes_visited = 0;
        prunings = 0;
        RelaxerType relaxer;
        
        size_t n_g = problem.groups.size();
        size_t n_s = problem.servers.size();
        
        // Root Node
        Node root;
        root.assignment.assign(n_g, -1);
        root.level = 0;
        
        // Initial Relaxation
        RelaxationResult root_res = relaxer.solve_relaxation(problem, root.assignment);
        if (!root_res.feasible) return false;
        root.lower_bound = root_res.lower_bound;
        
        // Priority Queue (Min-Heap on LB)
        std::priority_queue<Node, std::vector<Node>, std::greater<Node>> pq;
        pq.push(root);
        
        double best_known_cost = std::numeric_limits<double>::infinity();
        std::vector<int> best_assignment;
        
        // Heuristic Initial Solution (Greedy)
        // ... (Optional, can rely on relaxed finding integer solutions)
        
        auto start_time = std::chrono::high_resolution_clock::now();
        
        while (!pq.empty()) {
            // Check time limit? User said "2s to solve", benchmark runs for 10m.
            // We should just run to completion or reasonable cutoff.
            
            Node current = pq.top();
            pq.pop();
            
            if (current.lower_bound >= best_known_cost) {
                prunings++;
                continue; // Prune
            }
            
            nodes_visited++;
            
            // Check if leaf
            if (current.level == n_g) {
                // Complete valid assignment
                // Determine cost (exact)
                // Relaxation LB should match cost here if exact, but let's recompute to be safe
                double cost = 0;
                std::vector<bool> active(n_s, false);
                for(int s : current.assignment) active[s] = true;
                for(size_t s=0; s<n_s; ++s) if(active[s]) cost += problem.servers[s].cost;
                
                if (cost < best_known_cost) {
                    best_known_cost = cost;
                    best_assignment = current.assignment;
                }
                continue;
            }
            
            // Branch: Assign group 'current.level' to a compatible server
            // Strategy: Use Fractional Solution from Relaxer to guide branching order?
            // For now, simple iteration.
            
            // Optimization: Only branch on compatible servers
            // And maybe sort by cost?
            
            int g_idx = current.level;
            
            for (size_t s = 0; s < n_s; ++s) {
                // Compatibility Check
                // (Using logic from ServerProblem / existing solvers)
                // Note: We need access to compatibility logic.
                /* 
                 double dx = problem.groups[g_idx].x - problem.servers[s].x;
                 ...
                 if (!compatible) continue;
                 */
                // For speed, let's assume we copy compatibility logic or pre-compute it.
                // Let's implement inline compat check for now.
                double dx = problem.groups[g_idx].x - problem.servers[s].x;
                double dy = problem.groups[g_idx].y - problem.servers[s].y;
                double dist = std::sqrt(dx*dx + dy*dy);
                if (dist * 0.1 > problem.sla_limit) continue;
                
                // Also Capacity check?
                // Relaxation usually handles aggregated capacity, but strict check here helps.
                // But we don't track usage in Node struct to save memory. 
                // We rely on Relaxer to detect infeasibility down the line.
                
                Node child = current;
                child.assignment[g_idx] = s;
                child.level++;
                
                // Run Relaxation on Child
                RelaxationResult res = relaxer.solve_relaxation(problem, child.assignment);
                if (res.feasible && res.lower_bound < best_known_cost) {
                    child.lower_bound = res.lower_bound;
                    pq.push(child);
                } else {
                    // Pruned by bound or infeasibility
                }
            }
        }
        
        if (best_known_cost == std::numeric_limits<double>::infinity()) {
            return false;
        }
        
        // Reconstruct Solution
        solution.server_assignment.assign(n_g, 0);
        for(size_t i=0; i<n_g; ++i) solution.server_assignment[i] = best_assignment[i];
        
        solution.active_servers.assign(n_s, false);
        for(size_t s : best_assignment) solution.active_servers[s] = true;
        
        solution.total_cost = best_known_cost;
        metrics.objective_value = best_known_cost;
        metrics.iterations = nodes_visited;
        metrics.is_optimal = true;
        
        return true;
    }
};

} // namespace optsolve
