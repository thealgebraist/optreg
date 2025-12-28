#pragma once
#include <vector>
#include <string>

namespace tsp_heuristics {

struct Tour {
    std::vector<int> cities;
    int cost;
    std::string method;
};

class TSPHeuristics {
public:
    // Constructor with distance matrix
    explicit TSPHeuristics(const std::vector<std::vector<double>>& dist);
    
    // 8 Different heuristics
    Tour nearest_neighbor(int start = 0);
    Tour greedy_insertion();
    Tour farthest_insertion();
    Tour cheapest_insertion();
    Tour random_insertion(int seed = 42);
    Tour savings_algorithm();
    Tour two_opt(const Tour& initial);
    Tour three_opt(const Tour& initial);
    
    // Get best of all heuristics
    Tour best_heuristic();
    
private:
    const std::vector<std::vector<double>>& dist_;
    int n_;
    
    int compute_cost(const std::vector<int>& tour) const;
    void improve_with_2opt(std::vector<int>& tour, int& cost);
    void improve_with_3opt(std::vector<int>& tour, int& cost);
};

} // namespace tsp_heuristics
