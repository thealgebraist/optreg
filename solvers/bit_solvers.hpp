#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <vector>
#include <bitset>
#include <random>
#include <map>

namespace optsolve {

// Limit N=64 for pure u64 bitsets, or generic?
// For the prompt "1024 small instances", N<=64 is reasonable for optimal testing.
// I will implement a fixed N=64 optimized solver. If N > 64, it degrades or asserts.

typedef uint64_t BitMask;

struct BitGraph {
    size_t n;
    std::vector<BitMask> adj; // adj[i] = bitmask of neighbors of i
    
    void init(const GraphColoringProblem& p) {
        n = p.n_vertices;
        adj.assign(n, 0);
        for(auto& e : p.edges) {
            adj[e.first] |= (1ULL << e.second);
            adj[e.second] |= (1ULL << e.first);
        }
    }
    
    // Check conflicts for user u with color c (where color_sets[c] is mask of nodes with color c)
    int count_conflicts(size_t u, BitMask color_mask) const {
        BitMask conflicts = adj[u] & color_mask;
        // Count set bits
        return std::popcount(conflicts);
    }
};

// ============================================================================
// 1. Bitset Greedy
// ============================================================================
class BitsetGreedy : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Bitset_Greedy"; }
protected:
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        if (p.n_vertices > 64) {
            // Fallback
             val.num_colors = 9999; return false; 
        }
        
        BitGraph g; g.init(p);
        std::vector<size_t> colors(p.n_vertices);
        std::vector<BitMask> color_sets(p.n_vertices, 0); // Up to N colors
        
        for(size_t u=0; u<p.n_vertices; ++u) {
            size_t c = 0;
            while(true) {
                // Check if color c is used by any neighbor
                if ((g.adj[u] & color_sets[c]) == 0) {
                    colors[u] = c;
                    color_sets[c] |= (1ULL << u);
                    break;
                }
                c++;
            }
        }
        
        size_t max_c = 0;
        for(size_t c : colors) max_c = std::max(max_c, c);
        
        val.colors = colors;
        val.num_colors = max_c + 1;
        m.objective_value = val.num_colors;
        m.iterations = p.n_vertices;
        return true;
    }
};

// ============================================================================
// Base Bitset Local Search
// ============================================================================
struct BitSearchState {
    BitGraph g;
    size_t k;
    std::vector<size_t> node_color;
    std::vector<BitMask> color_mask; // color_mask[c] = nodes with color c
    size_t total_conflicts;
    
    void init(const GraphColoringProblem& p, size_t target_k) {
        g.init(p);
        k = target_k;
        node_color.assign(p.n_vertices, 0);
        color_mask.assign(target_k, 0);
        
        std::mt19937 rng(111);
        for(size_t i=0; i<p.n_vertices; ++i) {
            size_t c = rng() % k;
            move(i, c); // Setup
        }
        recalc_conflicts();
    }
    
    void move(size_t u, size_t new_c) {
        size_t old_c = node_color[u];
        color_mask[old_c] &= ~(1ULL << u);
        color_mask[new_c] |= (1ULL << u);
        node_color[u] = new_c;
    }
    
    int delta_conflicts(size_t u, size_t new_c) {
        // Remove u from old color => reduces conflicts by (adj[u] & color_mask[old_c]) (excluding u itself if it was set)
        // Add u to new color => increases by (adj[u] & color_mask[new_c])
        size_t old_c = node_color[u];
        if (old_c == new_c) return 0;
        
        int old_conf = std::popcount(g.adj[u] & color_mask[old_c]);
        int new_conf = std::popcount(g.adj[u] & color_mask[new_c]);
        return new_conf - old_conf;
    }
    
    void recalc_conflicts() {
        total_conflicts = 0;
        for(size_t u=0; u<g.n; ++u) {
            // Count neighbors with same color
            total_conflicts += std::popcount(g.adj[u] & color_mask[node_color[u]]);
        }
        total_conflicts /= 2; // Each edge counted twice
    }
};

// ============================================================================
// 2. Bitset Tabu
// ============================================================================
class BitsetTabu : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Bitset_Tabu"; }
protected:
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        if (p.n_vertices > 64) return false;
        
        // Initial UB
        BitsetGreedy bs;
        auto res = bs.solve(p);
        size_t k = res.solution.num_colors;
        val = res.solution;
        m.objective_value = k;
        
        while(k > 1) {
            BitSearchState s;
            s.init(p, k-1);
            
            bool solved = false;
            std::vector<std::vector<int>> tabu(p.n_vertices, std::vector<int>(k-1, 0));
            
            for(size_t iter=0; iter<1000*p.n_vertices; ++iter) {
                m.iterations++;
                if (s.total_conflicts == 0) { solved=true; break; }
                
                // Find best move
                // Iterate all u, all c? Or just conflicting u?
                // Bitset optimization: we can quickly identify conflicting nodes
                // Mask of all conflicting nodes?
                // Iterating all u is fast enough for N=64 (64*K ops)
                
                int best_delta = 999999;
                size_t best_u = 0;
                size_t best_c = 0;
                
                for(size_t u=0; u<p.n_vertices; ++u) {
                    if ((s.g.adj[u] & s.color_mask[s.node_color[u]]) == 0) continue; // Not conflicting
                    
                    for(size_t c=0; c<k-1; ++c) {
                        if (c == s.node_color[u]) continue;
                        int d = s.delta_conflicts(u, c);
                        
                        if (iter < tabu[u][c]) {
                            if (s.total_conflicts + d > 0) continue; // Aspiration
                        }
                        
                        if (d < best_delta) {
                            best_delta = d;
                            best_u = u;
                            best_c = c;
                        }
                    }
                }
                
                if (best_delta < 999999) {
                    s.move(best_u, best_c);
                    s.total_conflicts += best_delta; // Update running sum
                    tabu[best_u][s.node_color[best_u]] = iter + 5;
                } else break; 
            }
            
            if (solved) {
                k--;
                val.num_colors = k;
                m.objective_value = k;
            } else break;
        }
        return true;
    }
};

// ============================================================================
// 3. Bitset Random Walk
// ============================================================================
class BitsetRandomWalk : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Bitset_RandomWalk"; }
protected:
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        if (p.n_vertices > 64) return false;
        BitsetGreedy bs;
        auto res = bs.solve(p);
        size_t k = res.solution.num_colors;
        val = res.solution;
        m.objective_value = k;
        
        while(k > 1) {
            BitSearchState s;
            s.init(p, k-1);
            bool solved = false;
            std::mt19937 rng(999);
            
            for(size_t iter=0; iter<1000*p.n_vertices; ++iter) {
                m.iterations++;
                if (s.total_conflicts == 0) { solved=true; break; }
                
                // Pick random conflicting node
                std::vector<size_t> confs;
                for(size_t u=0; u<p.n_vertices; ++u) {
                    if ((s.g.adj[u] & s.color_mask[s.node_color[u]]) != 0) confs.push_back(u);
                }
                
                if(confs.empty()) { s.recalc_conflicts(); if(s.total_conflicts==0){solved=true; break;} }
                
                size_t u = confs[rng() % confs.size()];
                size_t c = rng() % (k-1);
                
                int d = s.delta_conflicts(u, c);
                s.move(u, c);
                s.total_conflicts += d;
            }
            if (solved) { k--; val.num_colors=k; m.objective_value=k; } else break;
        }
        return true;
    }
};

// ============================================================================
// 4. Bitset GLS
// ============================================================================
class BitsetGLS : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Bitset_GLS"; }
protected:
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        if (p.n_vertices > 64) return false;
        
        BitsetGreedy bs;
        auto res = bs.solve(p);
        size_t k = res.solution.num_colors;
        val = res.solution;
        m.objective_value = k;

        // Penalties matrix (flat or map?) N is small.
        // N=64 -> 64*64 = 4096 ints. Flat array OK.
        std::vector<int> penalties(p.n_vertices * p.n_vertices, 0);
        auto get_p = [&](size_t u, size_t v) { return penalties[u*p.n_vertices + v]; };
        auto inc_p = [&](size_t u, size_t v) { penalties[u*p.n_vertices + v]++; penalties[v*p.n_vertices + u]++; };
        
        while(k > 1) {
            BitSearchState s;
            s.init(p, k-1);
            std::fill(penalties.begin(), penalties.end(), 0);
            
            bool solved = false;
            
            for(size_t iter=0; iter<500*p.n_vertices; ++iter) {
                m.iterations++;
                if (s.total_conflicts == 0) { solved=true; break; }
                
                int best_aug = 999999;
                size_t best_u = 0;
                size_t best_c = 0;
                
                for(size_t u=0; u<p.n_vertices; ++u) {
                    if ((s.g.adj[u] & s.color_mask[s.node_color[u]]) == 0) continue;
                    
                    for(size_t c=0; c<k-1; ++c) {
                        if (c == s.node_color[u]) continue;
                        
                        int d_conf = s.delta_conflicts(u, c);
                        
                        // d_pen?
                        // Old conflicts removed: neighbors v with old color
                         int pen_removed = 0;
                         size_t old_c = s.node_color[u];
                         BitMask old_conf_mask = s.g.adj[u] & s.color_mask[old_c];
                         // Iterate set bits
                         for(size_t v=0; v<p.n_vertices; ++v) if ((old_conf_mask >> v) & 1) pen_removed += get_p(u, v);
                         
                         int pen_added = 0;
                         BitMask new_conf_mask = s.g.adj[u] & s.color_mask[c];
                         for(size_t v=0; v<p.n_vertices; ++v) if ((new_conf_mask >> v) & 1) pen_added += get_p(u, v);
                         
                         int d_pen = pen_added - pen_removed;
                         
                         if (d_conf + d_pen < best_aug) {
                             best_aug = d_conf + d_pen;
                             best_u = u;
                             best_c = c;
                         }
                    }
                }
                
                s.move(best_u, best_c); // Always apply best aug move? Or hill climb? 
                // GLS usually moves to local min of aug cost.
                // If local min, penalties increase.
                // Simplified: apply best move, if stuck (no improvement in conflicts) then penalize.
                s.recalc_conflicts();
                
                // Penalize features present in current state
                 for(size_t u=0; u<p.n_vertices; ++u) {
                     BitMask confs = s.g.adj[u] & s.color_mask[s.node_color[u]];
                     if (confs) {
                         for(size_t v=u+1; v<p.n_vertices; ++v) if((confs >> v) & 1) inc_p(u, v);
                     }
                 }
            }
            if (solved) { k--; val.num_colors=k; m.objective_value=k; } else break;
        }
        return true;
    }
};

}
