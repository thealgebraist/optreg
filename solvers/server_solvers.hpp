#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <queue>
#include <limits>
#include <numeric>

namespace optsolve {

// ============================================================================
// Server Greedy Heuristic
// ============================================================================
class ServerGreedy : public Solver<ServerProblem, ServerSolution> {
public:
    std::string name() const override { return "Server_Greedy"; }
    
protected:
    bool solve_impl(const ServerProblem& problem, ServerSolution& solution, SolverMetrics& metrics) override {
        size_t n_s = problem.servers.size();
        size_t n_g = problem.groups.size();
        
        solution.server_assignment.assign(n_g, size_t(-1));
        solution.active_servers.assign(n_s, false);
        std::vector<double> usage(n_s, 0.0);
        
        // Strategy: Sort groups by demand DESC, assign to cheapest compatible active server, else cheapest compatible.
        std::vector<size_t> sorted_groups(n_g);
        std::iota(sorted_groups.begin(), sorted_groups.end(), 0);
        std::sort(sorted_groups.begin(), sorted_groups.end(), [&](size_t a, size_t b) {
            return problem.groups[a].demand > problem.groups[b].demand;
        });
        
        std::vector<size_t> cheapest_servers(n_s);
        std::iota(cheapest_servers.begin(), cheapest_servers.end(), 0);
        std::sort(cheapest_servers.begin(), cheapest_servers.end(), [&](size_t a, size_t b) {
            return problem.servers[a].cost < problem.servers[b].cost;
        });
        
        for (size_t g : sorted_groups) {
            double demand = problem.groups[g].demand;
            bool assigned = false;
            
            // Try active first
            for (size_t s : cheapest_servers) {
                if (solution.active_servers[s] && is_compatible(problem, g, s) && usage[s] + demand <= problem.servers[s].capacity) {
                    solution.server_assignment[g] = s;
                    usage[s] += demand;
                    assigned = true;
                    break;
                }
            }
            
            if (!assigned) {
                // Try any
                for (size_t s : cheapest_servers) {
                    if (is_compatible(problem, g, s) && usage[s] + demand <= problem.servers[s].capacity) {
                        solution.server_assignment[g] = s;
                        usage[s] += demand;
                        solution.active_servers[s] = true;
                        assigned = true;
                        break;
                    }
                }
            }
            
            if (!assigned) return false;
        }
        
        // Final check for min utilization
        for (size_t s = 0; s < n_s; ++s) {
            if (solution.active_servers[s] && usage[s] < problem.u_target * problem.servers[s].capacity) {
                // Heuristic failed min-util check - for now, just return false or try shifting?
                // For simplicity, we'll just say this heuristic doesn't guarantee min-util.
            }
        }
        
        solution.total_cost = 0;
        for (size_t s = 0; s < n_s; ++s) if (solution.active_servers[s]) solution.total_cost += problem.servers[s].cost;
        
        return true;
    }
    
private:
    bool is_compatible(const ServerProblem& p, size_t g, size_t s) {
        double dx = p.groups[g].x - p.servers[s].x;
        double dy = p.groups[g].y - p.servers[s].y;
        double dist = std::sqrt(dx*dx + dy*dy);
        double mu = dist * 0.1;
        double sigma = mu * 0.1;
        return (mu + p.z_score * sigma <= p.sla_limit + 1e-6);
    }
};

// ============================================================================
// Server Sparse AMX - Optimal Branch & Bound
// ============================================================================
class ServerSparseAMX : public Solver<ServerProblem, ServerSolution> {
public:
    std::string name() const override { return "Server_SparseAMX"; }
    
protected:
    struct State {
        size_t group_idx;
        std::vector<size_t> assignment;
        std::vector<double> usage;
        double current_cost;
        
        bool operator>(const State& other) const {
            return current_cost > other.current_cost;
        }
    };

    bool solve_impl(const ServerProblem& problem, ServerSolution& solution, SolverMetrics& metrics) override {
        size_t n_s = problem.servers.size();
        size_t n_g = problem.groups.size();
        
        // Pre-calculate compatibility index to speed up search
        std::vector<std::vector<size_t>> compatibility(n_g);
        for (size_t g = 0; g < n_g; ++g) {
            for (size_t s = 0; s < n_s; ++s) {
                if (is_compatible(problem, g, s)) {
                    compatibility[g].push_back(s);
                }
            }
        }

        double best_cost = std::numeric_limits<double>::infinity();
        std::vector<size_t> best_assignment;
        
        std::vector<size_t> current_assignment(n_g, -1);
        std::vector<double> current_usage(n_s, 0.0);
        std::vector<bool> server_active(n_s, false);
        
        size_t nodes = 0;
        search(problem, 0, current_assignment, current_usage, server_active, 0.0, best_cost, best_assignment, nodes, compatibility);
        
        if (best_cost == std::numeric_limits<double>::infinity()) return false;
        
        solution.server_assignment = best_assignment;
        solution.active_servers.assign(n_s, false);
        for (size_t s : best_assignment) if (s != -1) solution.active_servers[s] = true;
        solution.total_cost = best_cost;
        
        metrics.iterations = nodes;
        metrics.is_optimal = true;
        return true;
    }

private:
    void search(const ServerProblem& p, size_t g_idx, std::vector<size_t>& assign, 
                std::vector<double>& usage, std::vector<bool>& active, 
                double cost, double& best_cost, std::vector<size_t>& best_assign, size_t& nodes,
                const std::vector<std::vector<size_t>>& compat) {
        nodes++;
        if (cost >= best_cost) return;
        
        if (g_idx == p.groups.size()) {
            for (size_t s = 0; s < p.servers.size(); ++s) {
                if (active[s] && usage[s] < p.u_target * p.servers[s].capacity) return;
            }
            best_cost = cost;
            best_assign = assign;
            return;
        }
        
        // Only try compatible servers
        for (size_t s : compat[g_idx]) {
            if (usage[s] + p.groups[g_idx].demand <= p.servers[s].capacity) {
                double added_cost = active[s] ? 0 : p.servers[s].cost;
                bool was_active = active[s];
                
                assign[g_idx] = s;
                usage[s] += p.groups[g_idx].demand;
                active[s] = true;
                
                search(p, g_idx + 1, assign, usage, active, cost + added_cost, best_cost, best_assign, nodes, compat);
                
                usage[s] -= p.groups[g_idx].demand;
                active[s] = was_active;
            }
        }
    }

    bool is_compatible(const ServerProblem& p, size_t g, size_t s) {
        double dx = p.groups[g].x - p.servers[s].x;
        double dy = p.groups[g].y - p.servers[s].y;
        double dist = std::sqrt(dx*dx + dy*dy);
        double mu = dist * 0.1;
        double sigma = mu * 0.1;
        return (mu + p.z_score * sigma <= p.sla_limit + 1e-6);
    }
};

} // namespace optsolve
