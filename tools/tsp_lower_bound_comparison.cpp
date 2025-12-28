#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <chrono>
#include <iomanip>
#include <numeric>
#include <queue>

using namespace optsolve;

// Simple Prim's Algorithm for MST
double calculate_mst(const TSPProblem& p) {
    size_t n = p.n_cities;
    if (n == 0) return 0;
    std::vector<double> min_edge(n, std::numeric_limits<double>::infinity());
    std::vector<bool> in_mst(n, false);
    min_edge[0] = 0;
    double mst_weight = 0;

    for (size_t i = 0; i < n; ++i) {
        int u = -1;
        for (size_t v = 0; v < n; ++v) {
            if (!in_mst[v] && (u == -1 || min_edge[v] < min_edge[u])) {
                u = v;
            }
        }

        if (min_edge[u] == std::numeric_limits<double>::infinity()) break;

        in_mst[u] = true;
        mst_weight += min_edge[u];

        for (size_t v = 0; v < n; ++v) {
            if (!in_mst[v] && p.distances[u][v] < min_edge[v]) {
                min_edge[v] = p.distances[u][v];
            }
        }
    }
    return mst_weight;
}

// Degree-2 Lower Bound: 0.5 * sum(shortest_edge_1 + shortest_edge_2 for each node)
double calculate_degree2_lb(const TSPProblem& p) {
    size_t n = p.n_cities;
    double total_lb = 0;
    for (size_t i = 0; i < n; ++i) {
        double d1 = std::numeric_limits<double>::infinity();
        double d2 = std::numeric_limits<double>::infinity();
        for (size_t j = 0; j < n; ++j) {
            if (i == j) continue;
            double d = p.distances[i][j];
            if (d < d1) {
                d2 = d1;
                d1 = d;
            } else if (d < d2) {
                d2 = d;
            }
        }
        total_lb += (d1 + d2);
    }
    return total_lb * 0.5;
}

int main() {
    size_t n = 1024;
    std::cout << "=== TSP Lower Bound Analysis (N=" << n << ") ===\n\n";

    // Standardize instance generation (512x512 grid)
    TSPProblem p;
    p.n_cities = n;
    p.coords.resize(n);
    p.distances.resize(n, std::vector<double>(n, 0.0));
    std::mt19937 rng(1337);
    std::uniform_real_distribution<double> dist_gen(0.0, 512.0);
    for (size_t i = 0; i < n; ++i) p.coords[i] = {dist_gen(rng), dist_gen(rng)};
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = i + 1; j < n; ++j) {
            double d = std::sqrt(std::pow(p.coords[i].x - p.coords[j].x, 2) + std::pow(p.coords[i].y - p.coords[j].y, 2));
            p.distances[i][j] = p.distances[j][i] = d;
        }
    }

    // 1. Calculate Lower Bounds
    std::cout << "Calculating Lower Bounds..." << std::endl;
    auto mst_lb = calculate_mst(p);
    auto deg2_lb = calculate_degree2_lb(p);
    double global_lb = std::max(mst_lb, deg2_lb);

    // 2. Run Heuristics
    std::vector<std::shared_ptr<Solver<TSPProblem, TSPSolution>>> solvers = {
        std::make_shared<TSPNearestNeighbor>(),
        std::make_shared<TSP2Opt>(),
        std::make_shared<TSPGeometricHeuristic>(),
        std::make_shared<TSPBoltzmannHeuristic>(),
        std::make_shared<TSPTopologicalBoltzmann>()
    };

    std::cout << "\n=== Results vs Lower Bound (" << global_lb << ") ===\n";
    std::cout << std::left << std::setw(25) << "Solver" << " | " << std::setw(12) << "Distance" << " | " << "Gap to LB %\n";
    std::cout << std::string(60, '-') << "\n";

    for (auto& s : solvers) {
        auto start = std::chrono::high_resolution_clock::now();
        auto res = s->solve(p);
        auto end = std::chrono::high_resolution_clock::now();
        double d = res.solution.total_distance;
        double gap = (d / global_lb - 1.0) * 100.0;
        
        std::cout << std::left << std::setw(25) << s->name() << " | " 
                  << std::setw(12) << std::fixed << std::setprecision(2) << d << " | "
                  << std::setprecision(3) << gap << "%\n";
    }

    std::cout << "\nLower Bound Types:\n";
    std::cout << "  MST Weight:      " << mst_lb << "\n";
    std::cout << "  Degree-2 Sum:    " << deg2_lb << "\n";
    std::cout << "  Combined Max LB: " << global_lb << "\n";

    return 0;
}
