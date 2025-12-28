#include "tsp_heuristics.h"
#include <algorithm>
#include <random>
#include <limits>
#include <numeric>

namespace tsp_heuristics {

TSPHeuristics::TSPHeuristics(const std::vector<std::vector<double>>& dist) 
    : dist_(dist), n_(dist.size()) {}

int TSPHeuristics::compute_cost(const std::vector<int>& tour) const {
    int cost = 0;
    for (size_t i = 0; i < tour.size(); ++i) {
        cost += (int)dist_[tour[i]][tour[(i+1) % tour.size()]];
    }
    return cost;
}

// Heuristic 1: Nearest Neighbor
Tour TSPHeuristics::nearest_neighbor(int start) {
    std::vector<bool> visited(n_, false);
    std::vector<int> tour = {start};
    visited[start] = true;
    int cost = 0;
    
    for (int step = 1; step < n_; ++step) {
        int current = tour.back();
        int nearest = -1;
        double min_dist = std::numeric_limits<double>::max();
        
        for (int j = 0; j < n_; ++j) {
            if (!visited[j] && dist_[current][j] < min_dist) {
                min_dist = dist_[current][j];
                nearest = j;
            }
        }
        
        tour.push_back(nearest);
        visited[nearest] = true;
        cost += (int)min_dist;
    }
    
    cost += (int)dist_[tour.back()][start];
    return {tour, cost, "NearestNeighbor"};
}

// Heuristic 2: Greedy Insertion
Tour TSPHeuristics::greedy_insertion() {
    std::vector<int> tour = {0};
    std::vector<bool> in_tour(n_, false);
    in_tour[0] = true;
    
    // Add farthest point from 0
    int farthest = -1;
    double max_dist = 0;
    for (int i = 1; i < n_; ++i) {
        if (dist_[0][i] > max_dist) {
            max_dist = dist_[0][i];
            farthest = i;
        }
    }
    tour.push_back(farthest);
    in_tour[farthest] = true;
    
    // Insert remaining cities cheaply
    while ((int)tour.size() < n_) {
        int best_city = -1;
        int best_pos = -1;
        int min_increase = std::numeric_limits<int>::max();
        
        // Find city and position with minimum cost increase
        for (int city = 0; city < n_; ++city) {
            if (in_tour[city]) continue;
            
            for (size_t pos = 0; pos < tour.size(); ++pos) {
                int next_pos = (pos + 1) % tour.size();
                int increase = (int)(dist_[tour[pos]][city] + dist_[city][tour[next_pos]] 
                                   - dist_[tour[pos]][tour[next_pos]]);
                
                if (increase < min_increase) {
                    min_increase = increase;
                    best_city = city;
                    best_pos = pos + 1;
                }
            }
        }
        
        tour.insert(tour.begin() + best_pos, best_city);
        in_tour[best_city] = true;
    }
    
    return {tour, compute_cost(tour), "GreedyInsert"};
}

// Heuristic 3: Farthest Insertion
Tour TSPHeuristics::farthest_insertion() {
    std::vector<int> tour = {0};
    std::vector<bool> in_tour(n_, false);
    in_tour[0] = true;
    
    while ((int)tour.size() < n_) {
        // Find farthest city from tour
        int farthest = -1;
        double max_min_dist = 0;
        
        for (int city = 0; city < n_; ++city) {
            if (in_tour[city]) continue;
            
            double min_dist = std::numeric_limits<double>::max();
            for (int t : tour) {
                min_dist = std::min(min_dist, dist_[city][t]);
            }
            
            if (min_dist > max_min_dist) {
                max_min_dist = min_dist;
                farthest = city;
            }
        }
        
        // Insert farthest city at best position
        int best_pos = 0;
        int min_increase = std::numeric_limits<int>::max();
        
        for (size_t pos = 0; pos < tour.size(); ++pos) {
            int next_pos = (pos + 1) % tour.size();
            int increase = (int)(dist_[tour[pos]][farthest] + dist_[farthest][tour[next_pos]] 
                               - dist_[tour[pos]][tour[next_pos]]);
            
            if (increase < min_increase) {
                min_increase = increase;
                best_pos = pos + 1;
            }
        }
        
        tour.insert(tour.begin() + best_pos, farthest);
        in_tour[farthest] = true;
    }
    
    return {tour, compute_cost(tour), "FarthestInsert"};
}

// Heuristic 4: Cheapest Insertion
Tour TSPHeuristics::cheapest_insertion() {
    std::vector<int> tour = {0, 1};
    std::vector<bool> in_tour(n_, false);
    in_tour[0] = in_tour[1] = true;
    
    while ((int)tour.size() < n_) {
        int best_city = -1;
        int best_pos = -1;
        int min_increase = std::numeric_limits<int>::max();
        
        for (int city = 0; city < n_; ++city) {
            if (in_tour[city]) continue;
            
            for (size_t pos = 0; pos < tour.size(); ++pos) {
                int next_pos = (pos + 1) % tour.size();
                int increase = (int)(dist_[tour[pos]][city] + dist_[city][tour[next_pos]] 
                                   - dist_[tour[pos]][tour[next_pos]]);
                
                if (increase < min_increase) {
                    min_increase = increase;
                    best_city = city;
                    best_pos = pos + 1;
                }
            }
        }
        
        tour.insert(tour.begin() + best_pos, best_city);
        in_tour[best_city] = true;
    }
    
    return {tour, compute_cost(tour), "CheapestInsert"};
}

// Heuristic 5: Random Insertion
Tour TSPHeuristics::random_insertion(int seed) {
    std::vector<int> tour(n_);
    std::iota(tour.begin(), tour.end(), 0);
    
    std::mt19937 gen(seed);
    std::shuffle(tour.begin(), tour.end(), gen);
    
    return {tour, compute_cost(tour), "RandomInsert"};
}

// Heuristic 6: Savings Algorithm
Tour TSPHeuristics::savings_algorithm() {
    std::vector<int> tour = {0};
    std::vector<bool> in_tour(n_, false);
    in_tour[0] = true;
    
    // Build tour by savings
    std::vector<std::pair<double, std::pair<int, int>>> savings;
    for (int i = 1; i < n_; ++i) {
        for (int j = i + 1; j < n_; ++j) {
            double save = dist_[0][i] + dist_[0][j] - dist_[i][j];
            savings.push_back({save, {i, j}});
        }
    }
    std::sort(savings.rbegin(), savings.rend());
    
    for (const auto& [save, edge] : savings) {
        auto [i, j] = edge;
        if (!in_tour[i]) {
            tour.push_back(i);
            in_tour[i] = true;
        }
        if (!in_tour[j]) {
            tour.push_back(j);
            in_tour[j] = true;
        }
    }
    
    return {tour, compute_cost(tour), "Savings"};
}

// Heuristic 7: 2-Opt Improvement
void TSPHeuristics::improve_with_2opt(std::vector<int>& tour, int& cost) {
    bool improved = true;
    int iterations = 0;
    
    while (improved && iterations < 100) {
        improved = false;
        iterations++;
        
        for (size_t i = 0; i < tour.size() - 1; ++i) {
            for (size_t j = i + 2; j < tour.size(); ++j) {
                int delta = -(int)dist_[tour[i]][tour[i+1]]
                           -(int)dist_[tour[j]][tour[(j+1)%tour.size()]]
                           +(int)dist_[tour[i]][tour[j]]
                           +(int)dist_[tour[i+1]][tour[(j+1)%tour.size()]];
                
                if (delta < 0) {
                    std::reverse(tour.begin() + i + 1, tour.begin() + j + 1);
                    cost += delta;
                    improved = true;
                }
            }
        }
    }
}

Tour TSPHeuristics::two_opt(const Tour& initial) {
    auto tour = initial.cities;
    int cost = initial.cost;
    improve_with_2opt(tour, cost);
    return {tour, cost, "2-Opt"};
}

// Heuristic 8: 3-Opt Improvement (simplified)
void TSPHeuristics::improve_with_3opt(std::vector<int>& tour, int& cost) {
    // Simplified 3-opt: just run multiple 2-opt passes
    for (int pass = 0; pass < 3; ++pass) {
        improve_with_2opt(tour, cost);
    }
}

Tour TSPHeuristics::three_opt(const Tour& initial) {
    auto tour = initial.cities;
    int cost = initial.cost;
    improve_with_3opt(tour, cost);
    return {tour, cost, "3-Opt"};
}

// Get best heuristic
Tour TSPHeuristics::best_heuristic() {
    std::vector<Tour> tours;
    
    tours.push_back(nearest_neighbor(0));
    tours.push_back(greedy_insertion());
    tours.push_back(farthest_insertion());
    tours.push_back(cheapest_insertion());
    tours.push_back(random_insertion());
    tours.push_back(savings_algorithm());
    
    // Improve best with 2-opt
    auto best = *std::min_element(tours.begin(), tours.end(), 
        [](const Tour& a, const Tour& b) { return a.cost < b.cost; });
    
    return two_opt(best);
}

} // namespace tsp_heuristics
