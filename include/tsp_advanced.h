#pragma once
#include <vector>
#include <set>

namespace tsp_advanced {

// Union-Find for subtour detection
class UnionFind {
public:
    explicit UnionFind(int n);
    int find(int x);
    void unite(int x, int y);
    bool connected(int x, int y);
    int count_components();
    std::vector<std::set<int>> get_components();
    
private:
    std::vector<int> parent_;
    std::vector<int> rank_;
};

// Minimum Spanning Tree for 1-tree bound
struct Edge {
    int u, v;
    double weight;
    bool operator<(const Edge& other) const { return weight < other.weight; }
};

class OneTreeBound {
public:
    explicit OneTreeBound(const std::vector<std::vector<double>>& dist);
    
    // Compute 1-tree lower bound
    double compute(const std::vector<int>& excluded_node = {});
    
    // Held-Karp bound with Lagrangian relaxation
    double held_karp_bound(int iterations = 30);
    
private:
    const std::vector<std::vector<double>>& dist_;
    int n_;
    std::vector<double> penalties_;  // Lagrangian multipliers
    
    double mst_cost(const std::vector<int>& nodes);
    void update_penalties(const std::vector<int>& degrees);
};

// Subtour elimination
class SubtourElimination {
public:
    explicit SubtourElimination(int n);
    
    // Detect subtours in current solution
    std::vector<std::set<int>> detect_subtours(const std::vector<std::pair<int,int>>& edges);
    
    // Check if solution is connected
    bool is_connected(const std::vector<std::pair<int,int>>& edges);
    
private:
    int n_;
    UnionFind uf_;
};

// Cutting plane generation
struct Cut {
    std::vector<int> nodes_in_set;  // S for subtour elimination: sum_{i in S, j not in S} x_ij >= 2
    double violation;  // How much the cut is violated
};

class CuttingPlanes {
public:
    explicit CuttingPlanes(int n);
    
    // Generate subtour elimination cuts
    std::vector<Cut> generate_sec_cuts(const std::vector<std::pair<int,int>>& edges);
    
    // Separate violated cuts (find most violated)
    Cut separate(const std::vector<std::pair<int,int>>& edges);
    
private:
    int n_;
};

} // namespace tsp_advanced
