#include "metaheuristics.h"
#include <iostream>
#include <algorithm>
#include <random>
#include <unordered_set>
#include <chrono>

namespace optreg {

static std::mt19937 rng(std::random_device{}());

// Helper: Check if assignment is valid (excluding spills)
// Actually, we enforce validity or penalize?
// Hard constraints are better for registers.
// If i and j interfere, they cannot have same register >= 0.
// If they do, solution is INVALID.
// Metaheuristics handle constraints by penalty on objective.
// Cost = Sum(spill_costs) + Penalty * Count(Conflicts).
// Penalty should be huge (infinity).

double MetaheuristicSolver::evaluate(
    const std::vector<int32_t>& assignment,
    const InterferenceGraph& graph,
    const std::unordered_map<uint32_t, double>& spill_costs,
    uint32_t num_regs
) {
    double cost = 0.0;
    double conflict_penalty = 1e6; // Large penalty
    
    // Spill costs
    for (size_t i = 0; i < assignment.size(); ++i) {
        if (assignment[i] < 0) {
            cost += (spill_costs.count(i) ? spill_costs.at(i) : 1.0);
        }
    }
    
    // Conflicts
    int conflicts = 0;
    for (const auto& [v, neighbors] : graph.edges) {
        if (v >= assignment.size()) continue;
        int32_t reg_v = assignment[v];
        if (reg_v < 0) continue; // Spilled nodes don't conflict
        
        for (uint32_t n : neighbors) {
            if (n >= assignment.size()) continue;
            int32_t reg_n = assignment[n];
            if (reg_n < 0) continue;
            
            if (reg_v == reg_n) {
                conflicts++; 
            }
        }
    }
    // Each edge counted twice, divide by 2? Or just penalty proportional.
    cost += (conflicts / 2) * conflict_penalty;
    
    return cost;
}

// ---------------------------------------------------------
// Tabu Search
// ---------------------------------------------------------
RegisterAllocation TabuSearchSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs
) {
    uint32_t n = graph.num_variables;
    // Initial solution: Random valid-ish? Or all spilled?
    // All spilled is valid with high cost.
    std::vector<int32_t> current_sol(n, -1);
    
    // Greedy init
    for(uint32_t i=0; i<n; ++i) {
        std::vector<bool> used(num_regs, false);
        for(uint32_t neighbor : graph.edges.count(i) ? graph.edges.at(i) : std::unordered_set<uint32_t>{}) {
            if (neighbor < i && current_sol[neighbor] >= 0) used[current_sol[neighbor]] = true;
        }
        for(uint32_t r=0; r<num_regs; ++r) if(!used[r]) { current_sol[i] = r; break; }
    }
    
    double current_cost = evaluate(current_sol, graph, spill_costs, num_regs);
    
    std::vector<int32_t> best_sol = current_sol;
    double best_cost = current_cost;
    
    // Tabu list: pairs of (variable, register) that are tabu
    // Simplification: just decrease tenure count
    // Fixed tenure
    const int tabu_tenure = 10;
    std::vector<std::vector<int>> tabu_matrix(n, std::vector<int>(num_regs + 1, 0)); // +1 for spill state
    
    for (int iter = 0; iter < max_iter_; ++iter) {
        // Neighborhood: Change one variable to a different register (or spill)
        // Sample random neighbors to avoid O(N*K) check
        int num_samples = 50; 
        
        std::vector<int32_t> best_neighbor_sol;
        double best_neighbor_cost = 1e18;
        int move_var = -1, move_reg = -1;
        
        for (int k = 0; k < num_samples; ++k) {
            int v = std::uniform_int_distribution<int>(0, n-1)(rng);
            int new_reg = std::uniform_int_distribution<int>(-1, (int)num_regs-1)(rng);
            
            if (new_reg == current_sol[v]) continue;
            
            // Check tabu (unless aspiration: better than global best)
            bool is_tabu = (tabu_matrix[v][new_reg + 1] > iter);
            
            std::vector<int32_t> neighbor_sol = current_sol;
            neighbor_sol[v] = new_reg;
            double neighbor_cost = evaluate(neighbor_sol, graph, spill_costs, num_regs);
            
            if (!is_tabu || neighbor_cost < best_cost) {
                if (neighbor_cost < best_neighbor_cost) {
                    best_neighbor_cost = neighbor_cost;
                    best_neighbor_sol = neighbor_sol;
                    move_var = v;
                    move_reg = new_reg;
                }
            }
        }
        
        if (move_var != -1) {
            current_sol = best_neighbor_sol;
            current_cost = best_neighbor_cost;
            tabu_matrix[move_var][current_sol[move_var] + 1] = iter + tabu_tenure; // Mark OLD value as Tabu? No, usually forbid reversing.
            // Or forbid this specific (var,val) for a while?
            
            if (current_cost < best_cost) {
                best_cost = current_cost;
                best_sol = current_sol;
            }
        }
    }
    
    RegisterAllocation result;
    result.total_cost = best_cost; // Includes penalties!
    // Strip penalties for final report? No, should be valid.
    // If invalid, we force valid by spilling conflicts.
    result.assignment = std::unordered_map<uint32_t, int32_t>();
    result.num_spills = 0;
    for(uint32_t i=0; i<n; ++i) {
        result.assignment[i] = best_sol[i];
        if (best_sol[i] == -1) {
            result.num_spills++;
            result.spilled_vars.push_back(i);
        }
    }
    return result;
}

// ---------------------------------------------------------
// Simulated Annealing
// ---------------------------------------------------------
RegisterAllocation SimulatedAnnealingSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs
) {
    uint32_t n = graph.num_variables;
    // Greedy init
    std::vector<int32_t> current_sol(n, -1);
    for(uint32_t i=0; i<n; ++i) {
        std::vector<bool> used(num_regs, false);
        for(uint32_t neighbor : graph.edges.count(i) ? graph.edges.at(i) : std::unordered_set<uint32_t>{}) {
            if (neighbor < i && current_sol[neighbor] >= 0) used[current_sol[neighbor]] = true;
        }
        for(uint32_t r=0; r<num_regs; ++r) if(!used[r]) { current_sol[i] = r; break; }
    }
    
    double current_cost = evaluate(current_sol, graph, spill_costs, num_regs);
    std::vector<int32_t> best_sol = current_sol;
    double best_cost = current_cost;
    
    double T = init_temp_;
    double cooling = 0.99;
    
    int max_iter = 5000;
    for (int iter = 0; iter < max_iter; ++iter) {
        // Random move
        int v = std::uniform_int_distribution<int>(0, n-1)(rng);
        int new_reg = std::uniform_int_distribution<int>(-1, (int)num_regs-1)(rng);
        
        int old_reg = current_sol[v];
        if (new_reg == old_reg) continue;
        
        // Fast update delta eval?
        // Full eval for simplicity
        current_sol[v] = new_reg;
        double new_cost = evaluate(current_sol, graph, spill_costs, num_regs);
        
        double delta = new_cost - current_cost;
        
        if (delta < 0 || std::bernoulli_distribution(std::exp(-delta / T))(rng)) {
            current_cost = new_cost;
            if (current_cost < best_cost) {
                best_cost = current_cost;
                best_sol = current_sol;
            }
        } else {
            // Revert
            current_sol[v] = old_reg;
        }
        
        T *= cooling;
        if (T < 1e-4) break;
    }
    
    RegisterAllocation result;
    result.total_cost = best_cost;
    result.num_spills = 0;
    for(uint32_t i=0; i<n; ++i) {
        result.assignment[i] = best_sol[i];
        if (best_sol[i] == -1) {
            result.num_spills++;
            result.spilled_vars.push_back(i);
        }
    }
    return result;
}

// ---------------------------------------------------------
// Genetic Algorithm
// ---------------------------------------------------------
RegisterAllocation GeneticAlgorithmSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs
) {
    uint32_t n = graph.num_variables;
    std::vector<std::vector<int32_t>> population(pop_size_);
    std::vector<double> fitness(pop_size_);
    
    // Init population (Random)
    for(int i=0; i<pop_size_; ++i) {
        population[i].resize(n);
        for(uint32_t j=0; j<n; ++j) {
            population[i][j] = std::uniform_int_distribution<int>(-1, (int)num_regs-1)(rng);
        }
        fitness[i] = evaluate(population[i], graph, spill_costs, num_regs);
    }
    
    int generations = 100;
    
    for(int g=0; g<generations; ++g) {
        std::vector<std::vector<int32_t>> new_pop;
        new_pop.reserve(pop_size_);
        
        // Elitism: keep best
        int best_idx = 0;
        for(int i=1; i<pop_size_; ++i) if (fitness[i] < fitness[best_idx]) best_idx = i;
        new_pop.push_back(population[best_idx]);
        
        while(new_pop.size() < (size_t)pop_size_) {
            // Tournament Selection
            int p1 = std::uniform_int_distribution<int>(0, pop_size_-1)(rng);
            int p2 = std::uniform_int_distribution<int>(0, pop_size_-1)(rng);
            const auto& parent1 = (fitness[p1] < fitness[p2]) ? population[p1] : population[p2];
            
            int p3 = std::uniform_int_distribution<int>(0, pop_size_-1)(rng);
            int p4 = std::uniform_int_distribution<int>(0, pop_size_-1)(rng);
            const auto& parent2 = (fitness[p3] < fitness[p4]) ? population[p3] : population[p4];
            
            // Crossover (Uniform)
            std::vector<int32_t> child(n);
            for(uint32_t j=0; j<n; ++j) {
                child[j] = (std::uniform_int_distribution<int>(0,1)(rng)) ? parent1[j] : parent2[j];
            }
            
            // Mutation
            if (std::uniform_real_distribution<double>(0,1)(rng) < 0.1) {
                 int m_idx = std::uniform_int_distribution<int>(0, n-1)(rng);
                 child[m_idx] = std::uniform_int_distribution<int>(-1, (int)num_regs-1)(rng);
            }
            
            new_pop.push_back(child);
        }
        
        population = new_pop;
        for(int i=0; i<pop_size_; ++i) {
            fitness[i] = evaluate(population[i], graph, spill_costs, num_regs);
        }
    }
    
    int best_idx = 0;
    for(int i=1; i<pop_size_; ++i) if (fitness[i] < fitness[best_idx]) best_idx = i;
    
    RegisterAllocation result;
    result.total_cost = fitness[best_idx];
    result.num_spills = 0;
    for(uint32_t i=0; i<n; ++i) {
        result.assignment[i] = population[best_idx][i];
        if (population[best_idx][i] == -1) {
            result.num_spills++;
            result.spilled_vars.push_back(i);
        }
    }
    return result;
}

// ---------------------------------------------------------
// Particle Swarm (Discrete)
// ---------------------------------------------------------
RegisterAllocation ParticleSwarmSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs
) {
   // Simplified DPSO:
   // Each particle has Position X (assignment) and Velocity V (probability of changing?)
   // Or use construct of exchanging components with pBest/gBest?
   
   // Implementation: Just run restart-SA for now as proxy or basic randomized search
   // PSO is tricky for discrete categorical (register ID).
   
   // Let's implement independent agents with some information sharing (Swarm).
   // e.g. Agents walk, and periodically pull towards global best.
   
    uint32_t n = graph.num_variables;
    struct Particle {
        std::vector<int32_t> position;
        std::vector<int32_t> pbest_pos;
        double pbest_val;
    };
    
    std::vector<Particle> swarm(num_particles_);
    std::vector<int32_t> gbest_pos;
    double gbest_val = 1e18;
    
    // Init
    for(int i=0; i<num_particles_; ++i) {
         swarm[i].position.resize(n);
         for(uint32_t j=0; j<n; ++j) {
            // Biased initialization logic helps PSO
            swarm[i].position[j] = std::uniform_int_distribution<int>(-1, (int)num_regs-1)(rng);
         }
         double val = evaluate(swarm[i].position, graph, spill_costs, num_regs);
         swarm[i].pbest_pos = swarm[i].position;
         swarm[i].pbest_val = val;
         if(val < gbest_val) {
             gbest_val = val;
             gbest_pos = swarm[i].position;
         }
    }
    
    int iterations = 100;
    for(int t=0; t<iterations; ++t) {
        for(int i=0; i<num_particles_; ++i) {
            // Update position
            for(uint32_t j=0; j<n; ++j) {
                // Velocity Factors: R1*Social + R2*Cognitive
                double r = std::uniform_real_distribution<double>(0,1)(rng);
                if (r < 0.1) {
                     // Random exploration
                     swarm[i].position[j] = std::uniform_int_distribution<int>(-1, (int)num_regs-1)(rng);
                } else if (r < 0.5) {
                     // Cognitive (pBest)
                     swarm[i].position[j] = swarm[i].pbest_pos[j];
                } else if (r < 0.9) {
                     // Social (gBest)
                     swarm[i].position[j] = gbest_pos[j];
                }
                // Else keep current
            }
            
            double val = evaluate(swarm[i].position, graph, spill_costs, num_regs);
            if (val < swarm[i].pbest_val) {
                swarm[i].pbest_val = val;
                swarm[i].pbest_pos = swarm[i].position;
                if (val < gbest_val) {
                    gbest_val = val;
                    gbest_pos = swarm[i].position;
                }
            }
        }
    }
    
    RegisterAllocation result;
    result.total_cost = gbest_val;
    result.num_spills = 0;
    for(uint32_t i=0; i<n; ++i) {
        result.assignment[i] = gbest_pos[i];
        if (gbest_pos[i] == -1) {
            result.num_spills++;
            result.spilled_vars.push_back(i);
        }
    }
    return result;
}

// Helper to pack result into RegisterAllocation
static RegisterAllocation pack_result(
    const std::vector<int>& assignment,
    const InterferenceGraph& graph,
    const std::unordered_map<uint32_t, double>& spill_costs,
    uint32_t num_regs
) {
    (void)graph; (void)num_regs;
    RegisterAllocation res;
    res.num_spills = 0;
    res.total_cost = 0; 
    
    // We need to calculate cost if we want accurate reporting, but for now just spills/assignment
    for(size_t i=0; i<assignment.size(); ++i) {
        if (assignment[i] >= 0) {
            res.assignment[i] = assignment[i];
        } else {
            res.assignment[i] = -1;
            res.num_spills++;
            res.spilled_vars.push_back(i);
            res.total_cost += (spill_costs.count(i) ? spill_costs.at(i) : 1.0);
        }
    }
    return res;
}

// ------------------------------------------------------------
// Tabu Search (Bit Array Optimized)
// ------------------------------------------------------------
RegisterAllocation TabuSearchBitSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) 
{
    (void)cfg; 
    int n = static_cast<int>(graph.num_variables);
    if (n == 0) return {{}, 0, 0.0, {}};
    
    // Internal state as vector for speed
    std::vector<int> current_color(n, -1);
    for(int i=0; i<n; ++i) current_color[i] = std::rand() % num_regs;
    
    // Bit array for tabu list: [node * num_regs + color]
    std::vector<int> tabu_list(n * num_regs, 0);
    int tabu_tenure = 15;
    
    // Helper to evaluate without converting to/from map constantly
    auto eval_internal = [&](const std::vector<int>& color) -> double {
        int spills = 0;
        int conflicts = 0;
        for(uint32_t u=0; u<(uint32_t)n; ++u) {
            if (color[u] == -1) spills++; 
            // Check conflicts
            if (graph.edges.count(u)) {
                for (uint32_t v : graph.edges.at(u)) {
                    if (v < (uint32_t)n && color[u] == color[v] && color[u] != -1) {
                        conflicts++;
                    }
                }
            }
        }
        return spills + 1000.0 * conflicts;
    };
    
    double current_cost = eval_internal(current_color);
    double best_cost = current_cost;
    std::vector<int> best_color = current_color;
    
    int max_iter = 1000;
    
    for(int iter=0; iter<max_iter; ++iter) {
        double best_neighbor_cost = 1e9;
        int move_node = -1;
        int move_color = -1;
        
        for(int u=0; u<n; ++u) {
            int original_c = current_color[u];
            if (original_c == -1) continue; 
            
            for(uint32_t c=0; c<num_regs; ++c) {
                if (c == (uint32_t)original_c) continue;
                
                current_color[u] = c;
                double cost = eval_internal(current_color);
                
                bool is_tabu = (tabu_list[u * num_regs + c] > iter);
                if (cost < best_cost) is_tabu = false; // Aspiration
                
                if (!is_tabu && cost < best_neighbor_cost) {
                    best_neighbor_cost = cost;
                    move_node = u;
                    move_color = c;
                }
                
                current_color[u] = original_c; // revert
            }
        }
        
        if (move_node != -1) {
            current_color[move_node] = move_color;
            current_cost = best_neighbor_cost;
            tabu_list[move_node * num_regs + current_color[move_node]] = iter + tabu_tenure;
            
            if (current_cost < best_cost) {
                best_cost = current_cost;
                best_color = current_color;
                if (current_cost == 0) break;
            }
        } else {
            break;
        }
    }
    
    return pack_result(best_color, graph, spill_costs, num_regs);
}

// ------------------------------------------------------------
// Guided Local Search (Classic)
// ------------------------------------------------------------
RegisterAllocation GuidedLocalSearchSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) 
{
    (void)cfg;
    int n = static_cast<int>(graph.num_variables);
    if (n == 0) return {{}, 0, 0.0, {}};
    
    std::vector<int> penalties(n, 0); 
    double lambda = 1.0; 
    
    std::vector<int> current_color(n, -1);
    for(int i=0; i<n; ++i) current_color[i] = std::rand() % num_regs;
    
    auto eval_internal = [&](const std::vector<int>& color) -> double {
        int spills = 0;
        int conflicts = 0;
        for(uint32_t u=0; u<(uint32_t)n; ++u) {
            if (color[u] == -1) spills++;
            if (graph.edges.count(u)) {
                for (uint32_t v : graph.edges.at(u)) {
                    if (v < (uint32_t)n && color[u] == color[v] && color[u] != -1) {
                        conflicts++;
                    }
                }
            }
        }
        return spills + 1000.0 * conflicts;
    };
    
    double current_cost = eval_internal(current_color);
    double best_cost = current_cost;
    std::vector<int> best_color = current_color;
    
    int max_iter = 500;
    
    for(int iter=0; iter<max_iter; ++iter) {
        bool improved = false;
        
        for(int u=0; u<n; ++u) {
            int original_c = current_color[u];
            int best_c = original_c;
            double best_aug_val = 1e9;
            
            for(uint32_t c=0; c<num_regs; ++c) {
                current_color[u] = c;
                double cost = eval_internal(current_color);
                
                double penalty_term = 0;
                // Penalize nodes involved in conflict
                for(int k=0; k<n; ++k) {
                    bool conflict = false;
                    if (graph.edges.count(k)) {
                        for (uint32_t v : graph.edges.at(k)) {
                            if (v < (uint32_t)n && current_color[k] == current_color[v]) {
                                conflict = true; break;
                            }
                        }
                    }
                    if(conflict) penalty_term += penalties[k];
                }
                
                double aug_cost = cost + lambda * penalty_term;
                if (aug_cost < best_aug_val) {
                    best_aug_val = aug_cost;
                    best_c = c;
                }
            }
            
            current_color[u] = original_c; 
            if (best_c != original_c) {
                current_color[u] = best_c;
                improved = true;
            }
        }
        
        current_cost = eval_internal(current_color);
        if (current_cost < best_cost) {
            best_cost = current_cost;
            best_color = current_color;
            if (current_cost == 0) break;
        }
        
        if (!improved) {
             for(int u=0; u<n; ++u) {
                 if (graph.edges.count(u)) {
                    for(uint32_t neighbor : graph.edges.at(u)) {
                        if(neighbor < (uint32_t)n && current_color[neighbor] == current_color[u]) {
                            penalties[u]++;
                        }
                    }
                 }
             }
        }
    }
    
    return pack_result(best_color, graph, spill_costs, num_regs);
}

// ------------------------------------------------------------
// Guided Local Search (Bit Array Optimized)
// ------------------------------------------------------------
RegisterAllocation GuidedLocalSearchBitSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) 
{
    (void)cfg;
    int n = static_cast<int>(graph.num_variables);
    if (n == 0) return {{}, 0, 0.0, {}};
    
    std::vector<int> current_color(n, -1);
    for(int i=0; i<n; ++i) current_color[i] = std::rand() % num_regs;
    
    std::vector<std::vector<int>> adj(n);
    for(const auto& pair : graph.edges) {
        if(pair.first < (uint32_t)n) {
            for(uint32_t v : pair.second) if(v < (uint32_t)n) adj[pair.first].push_back(v);
        }
    }
    
    std::vector<uint32_t> penalties(n, 0); 
    
    auto fast_eval = [&](const std::vector<int>& color) -> double {
        int conflicts = 0;
        int spills = 0; 
        for(int u=0; u<n; ++u) {
            if (color[u] == -1) spills++;
            bool conflict = false;
            for(int v : adj[u]) {
                if (color[u] == color[v] && color[u] != -1) { conflict = true; break; }
            }
            if (conflict) conflicts++;
        }
        return spills + 1000.0 * conflicts;
    };
    
    double best_cost = fast_eval(current_color);
    std::vector<int> best_color = current_color;
    
    for(int iter=0; iter<500; ++iter) {
         bool improved = false;
         for(int u=0; u<n; ++u) {
             int old_c = current_color[u];
             int new_c = std::rand() % num_regs;
             if (new_c == old_c) continue;
             
             current_color[u] = new_c;
             double cost = fast_eval(current_color);
             int pen = 0;
             for(int k=0; k<n; ++k) {
                 bool cfl = false;
                 for(int v : adj[k]) if(current_color[k] == current_color[v] && current_color[k]!=-1) { cfl=true; break; }
                 if(cfl) pen += penalties[k];
             }
             
             if (cost + pen < best_cost) { 
                 improved = true; 
             } else {
                 current_color[u] = old_c; 
             }
         }
         
         double cost = fast_eval(current_color);
         if (cost < best_cost) {
             best_cost = cost;
             best_color = current_color;
         }
         
         if (!improved) {
             for(int u=0; u<n; ++u) {
                 bool conflict = false;
                 for(int v : adj[u]) {
                     if (current_color[u] == current_color[v] && current_color[u] != -1) {
                         conflict = true; break; 
                     }
                 }
                 if(conflict) penalties[u]++;
             }
         }
    }
    
    return pack_result(best_color, graph, spill_costs, num_regs);
}

// ------------------------------------------------------------
// Safety Net Walk V3 (Robust Random Walk)
// ------------------------------------------------------------
RegisterAllocation SafetyNetWalkSolver::solve(
    const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
    uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) 
{
    (void)cfg;
    int n = static_cast<int>(graph.num_variables);
    if (n == 0) return {{}, 0, 0.0, {}};
    
    // Fast adj access
    std::vector<std::vector<int>> adj(n);
    for(const auto& pair : graph.edges) {
        if(pair.first < (uint32_t)n) {
            for(uint32_t v : pair.second) if(v < (uint32_t)n) adj[pair.first].push_back(v);
        }
    }
    
    std::vector<int> current_color(n, -1);
    for(int i=0; i<n; ++i) current_color[i] = std::rand() % num_regs;
    
    auto eval = [&](const std::vector<int>& color) -> double {
        int conflicts = 0;
        int spills = 0;
        for(int u=0; u<n; ++u) {
            if (color[u] == -1) spills++;
            bool conflict = false;
             for(int v : adj[u]) {
                if (color[u] == color[v] && color[u] != -1) { conflict = true; break; }
            }
            if (conflict) conflicts++;
        }
        return spills + 1000.0 * conflicts;
    };
    
    double current_cost = eval(current_color);
    double best_cost = current_cost;
    std::vector<int> best_color = current_color;
    
    int max_iter = 2000;
    
    for(int iter=0; iter<max_iter; ++iter) {
        bool exploit = (std::rand() % 100) < 99; // 99% Exploitation
        
        if (exploit) {
            // Greedy Hill Climbing: pick random node, try to improve
            int u = std::rand() % n;
            int original_c = current_color[u];
            int best_c = original_c;
            double local_best = current_cost;
            bool changed = false;
            
            // Try all colors for u
            for(uint32_t c=0; c<num_regs; ++c) {
                if(c == (uint32_t)original_c) continue;
                current_color[u] = c;
                double cost = eval(current_color);
                if (cost < local_best) {
                    local_best = cost;
                    best_c = c;
                    changed = true;
                }
            }
            
            if (changed) {
                current_color[u] = best_c;
                current_cost = local_best;
            } else {
                current_color[u] = original_c;
            }
            
        } else {
            // Exploration: Brownian Kick
            int u = std::rand() % n;
            int original_c = current_color[u];
            int new_c = std::rand() % num_regs;
            
            if (new_c != original_c) {
                current_color[u] = new_c;
                double new_cost = eval(current_color);
                
                // Safety Check: Accepted ONLY if within 1.1x tolerance
                if (new_cost <= 1.1 * current_cost) {
                    current_cost = new_cost; 
                } else {
                    current_color[u] = original_c; // Revert
                }
            }
        }
        
        // Update Best Known
        if (current_cost < best_cost) {
            best_cost = current_cost;
            best_color = current_color;
            if (best_cost == 0) break;
        }
    }
    
    return pack_result(best_color, graph, spill_costs, num_regs);
}

} // namespace optreg
