#include "tsp_advanced.h"
#include <algorithm>
#include <numeric>
#include <queue>
#include <cmath>
#include <map>

namespace tsp_advanced {

// ==========================================
// Union-Find Implementation
// ==========================================

UnionFind::UnionFind(int n) : parent_(n), rank_(n, 0) {
    std::iota(parent_.begin(), parent_.end(), 0);
}

int UnionFind::find(int x) {
    if (parent_[x] != x) {
        parent_[x] = find(parent_[x]);  // Path compression
    }
    return parent_[x];
}

void UnionFind::unite(int x, int y) {
    int px = find(x), py = find(y);
    if (px == py) return;
    
    // Union by rank
    if (rank_[px] < rank_[py]) {
        parent_[px] = py;
    } else if (rank_[px] > rank_[py]) {
        parent_[py] = px;
    } else {
        parent_[py] = px;
        rank_[px]++;
    }
}

bool UnionFind::connected(int x, int y) {
    return find(x) == find(y);
}

int UnionFind::count_components() {
    std::set<int> roots;
    for (size_t i = 0; i < parent_.size(); ++i) {
        roots.insert(find(i));
    }
    return roots.size();
}

std::vector<std::set<int>> UnionFind::get_components() {
    std::map<int, std::set<int>> comp_map;
    for (size_t i = 0; i < parent_.size(); ++i) {
        comp_map[find(i)].insert(i);
    }
    
    std::vector<std::set<int>> components;
    for (const auto& [root, nodes] : comp_map) {
        components.push_back(nodes);
    }
    return components;
}

// ==========================================
// 1-Tree Lower Bound (Held-Karp)
// ==========================================

OneTreeBound::OneTreeBound(const std::vector<std::vector<double>>& dist)
    : dist_(dist), n_(dist.size()), penalties_(n_, 0.0) {}

double OneTreeBound::mst_cost(const std::vector<int>& nodes) {
    if (nodes.size() <= 1) return 0;
    
    // Kruskal's algorithm
    std::vector<Edge> edges;
    for (size_t i = 0; i < nodes.size(); ++i) {
        for (size_t j = i + 1; j < nodes.size(); ++j) {
            edges.push_back({nodes[i], nodes[j], dist_[nodes[i]][nodes[j]]});
        }
    }
    std::sort(edges.begin(), edges.end());
    
    UnionFind uf(n_);
    double cost = 0;
    for (const auto& e : edges) {
        if (!uf.connected(e.u, e.v)) {
            uf.unite(e.u, e.v);
            cost += e.weight;
        }
    }
    return cost;
}

double OneTreeBound::compute(const std::vector<int>& excluded_node) {
    // 1-tree = MST on nodes {1..n-1} + 2 cheapest edges from node 0
    std::vector<int> mst_nodes;
    for (int i = 1; i < n_; ++i) {
        if (std::find(excluded_node.begin(), excluded_node.end(), i) == excluded_node.end()) {
            mst_nodes.push_back(i);
        }
    }
    
    double bound = mst_cost(mst_nodes);
    
    // Add 2 cheapest edges from node 0
    std::vector<double> edges_from_0;
    for (int i = 1; i < n_; ++i) {
        if (std::find(excluded_node.begin(), excluded_node.end(), i) == excluded_node.end()) {
            edges_from_0.push_back(dist_[0][i] + penalties_[0] + penalties_[i]);
        }
    }
    std::sort(edges_from_0.begin(), edges_from_0.end());
    
    if (edges_from_0.size() >= 2) {
        bound += edges_from_0[0] + edges_from_0[1];
    }
    
    return bound;
}

double OneTreeBound::held_karp_bound(int iterations) {
    double best_bound = compute();
    double step_size = 1.0;
    
    for (int iter = 0; iter < iterations; ++iter) {
        // Compute 1-tree and degrees
        std::vector<int> degrees(n_, 0);
        
        // MST contributes to degrees
        std::vector<int> mst_nodes;
        for (int i = 1; i < n_; ++i) mst_nodes.push_back(i);
        
        // Simplified: assume each node has degree ~2 in MST
        for (int node : mst_nodes) degrees[node] = 2;
        degrees[0] = 2;  // From the 2 edges added
        
        // Update penalties (subgradient method)
        bool converged = true;
        for (int i = 0; i < n_; ++i) {
            double delta = step_size * (2 - degrees[i]);  // Target degree = 2
            if (std::abs(delta) > 0.01) converged = false;
            penalties_[i] += delta;
        }
        
        double new_bound = compute();
        best_bound = std::max(best_bound, new_bound);
        
        if (converged) break;
        step_size *= 0.95;  // Decay
    }
    
    return best_bound;
}

// ==========================================
// Subtour Elimination
// ==========================================

SubtourElimination::SubtourElimination(int n) : n_(n), uf_(n) {}

std::vector<std::set<int>> SubtourElimination::detect_subtours(
    const std::vector<std::pair<int,int>>& edges) {
    
    UnionFind uf(n_);
    for (const auto& [u, v] : edges) {
        uf.unite(u, v);
    }
    return uf.get_components();
}

bool SubtourElimination::is_connected(const std::vector<std::pair<int,int>>& edges) {
    UnionFind uf(n_);
    for (const auto& [u, v] : edges) {
        uf.unite(u, v);
    }
    return uf.count_components() == 1;
}

// ==========================================
// Cutting Planes
// ==========================================

CuttingPlanes::CuttingPlanes(int n) : n_(n) {}

std::vector<Cut> CuttingPlanes::generate_sec_cuts(
    const std::vector<std::pair<int,int>>& edges) {
    
    SubtourElimination se(n_);
    auto components = se.detect_subtours(edges);
    
    std::vector<Cut> cuts;
    
    // For each component that's not the whole graph, generate a cut
    for (const auto& comp : components) {
        if (comp.size() > 1 && comp.size() < (size_t)n_) {
            Cut cut;
            cut.nodes_in_set = std::vector<int>(comp.begin(), comp.end());
            
            // Count edges crossing the cut
            int crossing = 0;
            for (const auto& [u, v] : edges) {
                bool u_in = comp.count(u) > 0;
                bool v_in = comp.count(v) > 0;
                if (u_in != v_in) crossing++;
            }
            
            // Violation: should have >= 2 edges crossing, we have 'crossing'
            cut.violation = std::max(0.0, 2.0 - crossing);
            
            if (cut.violation > 0.01) {
                cuts.push_back(cut);
            }
        }
    }
    
    return cuts;
}

Cut CuttingPlanes::separate(const std::vector<std::pair<int,int>>& edges) {
    auto cuts = generate_sec_cuts(edges);
    
    if (cuts.empty()) {
        return {{}, 0.0};
    }
    
    // Return most violated
    return *std::max_element(cuts.begin(), cuts.end(),
        [](const Cut& a, const Cut& b) { return a.violation < b.violation; });
}

} // namespace tsp_advanced
