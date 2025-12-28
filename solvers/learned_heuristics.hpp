#pragma once
#include "problem_types.hpp"
#include "solver_base.hpp"
#include <vector>
#include <queue>
#include <algorithm>
#include <map>

namespace optsolve {

// ============================================================================
// Learned Heuristic for Graph Coloring (Register Allocation)
// ============================================================================
// Score(v) = w1*Deg + w2*Clust + w3*NeighAvg
// Prority: Higher absolute score (depending on sign) -> Color First.
// Usually higher degree -> color first (DSatur).

class LearnedColoringSolver : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Learned_Coloring_Heuristic"; }
    
    // Default weights (updated after analysis on 150 instances)
    // Correlations: Degree +0.33 (High Deg -> Late Color), Neigh -0.03 (High Neigh -> Early Color)
    // Strategy: Pick Early (High Priority) if correlated with Low Color.
    // w_degree = -0.3290 (Pick Low Degree First)
    // w_clustering = -0.0297 (Pick Low Clustering First)
    // w_neighbor_avg = +0.0283 (Pick High Neighbor Degree First)
    
    double w_degree = -0.3290;
    double w_clustering = -0.0297;
    double w_neighbor_avg = 0.0283;
    
    // Compute Clustering (Duplicate from test file, generic util needed)
    double get_clustering(size_t v, const std::vector<std::vector<bool>>& adj, size_t n) {
        std::vector<size_t> neighbors;
        for(size_t i=0; i<n; ++i) if (adj[v][i]) neighbors.push_back(i);
        size_t k = neighbors.size();
        if (k < 2) return 0.0;
        size_t edges = 0;
        for(size_t i=0; i<k; ++i) for(size_t j=i+1; j<k; ++j) if (adj[neighbors[i]][neighbors[j]]) edges++;
        return (2.0 * edges) / (double)(k * (k-1));
    }

protected:
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        size_t n = p.n_vertices;
        std::vector<std::vector<bool>> adj(n, std::vector<bool>(n, false));
        std::vector<int> degrees(n, 0);
        for(auto& e : p.edges) {
            adj[e.first][e.second] = adj[e.second][e.first] = true;
            degrees[e.first]++;
            degrees[e.second]++;
        }
        
        // 1. Calculate Priorities
        struct NodePriority {
            size_t id;
            double score;
            bool operator<(const NodePriority& o) const { return score < o.score; }
        };
        
        std::priority_queue<NodePriority> pq;
        
        for(size_t i=0; i<n; ++i) {
            double clust = get_clustering(i, adj, n);
            double neigh_sum = 0;
            for(size_t j=0; j<n; ++j) if(adj[i][j]) neigh_sum += degrees[j];
            double neigh_avg = degrees[i]>0 ? neigh_sum/degrees[i] : 0;
            
            double score = w_degree * degrees[i] + 
                           w_clustering * clust + 
                           w_neighbor_avg * neigh_avg;
            pq.push({i, score});
        }
        
        // 2. Greedy Coloring based on Priority
        std::vector<size_t> colors(n, 0); // 0 = uncolored (Wait, valid colors > 0?)
        // Let's use 0-indexed colors internally
        std::vector<int> assigned_color(n, -1);
        size_t max_c = 0;
        
        m.iterations = 0;
        
        while(!pq.empty()) {
            NodePriority curr = pq.top(); pq.pop();
            size_t u = curr.id;
            
            // Pick smallest available color
            std::vector<bool> used(n, false);
            for(size_t v=0; v<n; ++v) {
                if (adj[u][v] && assigned_color[v] != -1) {
                    used[assigned_color[v]] = true;
                }
            }
            
            int c = 0;
            while(c < n && used[c]) c++;
            assigned_color[u] = c;
            m.iterations++;
            if ((size_t)(c+1) > max_c) max_c = c+1;
        }
        
        // Convert to output format
        val.colors.resize(n);
        for(size_t i=0; i<n; ++i) val.colors[i] = (size_t)(assigned_color[i] + 1); // 1-based output? 
        // Problem def used 1-based in random gen? No, problem types usually don't care, but output usually 1-indexed for some verifiers.
        // Let's check: GraphColoringSolution uses size_t.
        // I will use 1-based to be safe or strictly distinct.
        val.num_colors = max_c;
        m.objective_value = (double)max_c;
        return true;
    }
};

}
