#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <chrono>
#include <iomanip>
#include <numeric>
#include <algorithm>
#include <set>

using namespace optsolve;

// Monotone Chain algorithm for Convex Hull
std::vector<size_t> get_convex_hull_indices(const std::vector<TSPProblem::Point>& points) {
    size_t n = points.size();
    if (n <= 2) {
        std::vector<size_t> h;
        for (size_t i = 0; i < n; ++i) h.push_back(i);
        return h;
    }

    struct IndexedPoint {
        TSPProblem::Point p;
        size_t id;
    };
    std::vector<IndexedPoint> ip(n);
    for (size_t i = 0; i < n; ++i) ip[i] = {points[i], i};

    std::sort(ip.begin(), ip.end(), [](const IndexedPoint& a, const IndexedPoint& b) {
        return a.p.x < b.p.x || (a.p.x == b.p.x && a.p.y < b.p.y);
    });

    auto cross_product = [](const TSPProblem::Point& a, const TSPProblem::Point& b, const TSPProblem::Point& c) {
        return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
    };

    std::vector<IndexedPoint> hull;
    // Lower hull
    for (const auto& p : ip) {
        while (hull.size() >= 2 && cross_product(hull[hull.size()-2].p, hull.back().p, p.p) <= 0) {
            hull.pop_back();
        }
        hull.push_back(p);
    }

    // Upper hull
    size_t lower_hull_size = hull.size();
    for (int i = n - 2; i >= 0; --i) {
        while (hull.size() > lower_hull_size && cross_product(hull[hull.size()-2].p, hull.back().p, ip[i].p) <= 0) {
            hull.pop_back();
        }
        hull.push_back(ip[i]);
    }
    hull.pop_back(); // Last point is same as first

    std::vector<size_t> result;
    for (const auto& p : hull) result.push_back(p.id);
    return result;
}

// Simple Prim's for MST
double calculate_mst(const TSPProblem& p) {
    size_t n = p.n_cities;
    std::vector<double> min_edge(n, std::numeric_limits<double>::infinity());
    std::vector<bool> in_mst(n, false);
    min_edge[0] = 0;
    double mst_weight = 0;
    for (size_t i = 0; i < n; ++i) {
        int u = -1;
        for (size_t v = 0; v < n; ++v) {
            if (!in_mst[v] && (u == -1 || min_edge[v] < min_edge[u])) u = v;
        }
        if (u == -1 || min_edge[u] == std::numeric_limits<double>::infinity()) break;
        in_mst[u] = true;
        mst_weight += min_edge[u];
        for (size_t v = 0; v < n; ++v) {
            if (!in_mst[v] && p.distances[u][v] < min_edge[v]) min_edge[v] = p.distances[u][v];
        }
    }
    return mst_weight;
}

int main() {
    size_t n = 1024;
    size_t num_instances = 512;
    std::cout << "=== Massive TSP Analysis: LB & CH Correlation (N=" << n << ", Instances=" << num_instances << ") ===\n";

    TSPTopologicalBoltzmann solver;
    double total_gap_to_mst = 0;
    double total_ch_loyalty = 0;

    for (size_t inst = 0; inst < num_instances; ++inst) {
        TSPProblem p;
        p.n_cities = n;
        p.coords.resize(n);
        p.distances.resize(n, std::vector<double>(n, 0.0));
        std::mt19937 rng(inst + 5000);
        std::uniform_real_distribution<double> dist_gen(0.0, 512.0);
        for (size_t i = 0; i < n; ++i) p.coords[i] = {dist_gen(rng), dist_gen(rng)};
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                double d = std::sqrt(std::pow(p.coords[i].x - p.coords[j].x, 2) + std::pow(p.coords[i].y - p.coords[j].y, 2));
                p.distances[i][j] = p.distances[j][i] = d;
            }
        }

        // 1. Lower Bound
        double mst = calculate_mst(p);

        // 2. Convex Hull
        auto ch_indices = get_convex_hull_indices(p.coords);
        std::set<std::pair<size_t, size_t>> ch_edges;
        for (size_t i = 0; i < ch_indices.size(); ++i) {
            size_t u = ch_indices[i];
            size_t v = ch_indices[(i + 1) % ch_indices.size()];
            ch_edges.insert({std::min(u, v), std::max(u, v)});
        }

        // 3. Solve with Heuristic
        auto res = solver.solve(p);
        double dist = res.solution.total_distance;
        total_gap_to_mst += (dist / mst - 1.0) * 100.0;

        // 4. CH Loyalty
        size_t matched_ch_edges = 0;
        for (size_t i = 0; i < res.solution.tour.size(); ++i) {
            size_t u = res.solution.tour[i];
            size_t v = res.solution.tour[(i + 1) % res.solution.tour.size()];
            if (ch_edges.count({std::min(u, v), std::max(u, v)})) {
                matched_ch_edges++;
            }
        }
        total_ch_loyalty += (double)matched_ch_edges / ch_edges.size();

        if ((inst + 1) % 64 == 0) {
            std::cout << "Processed " << (inst + 1) << " instances...\n";
        }
    }

    std::cout << "\n=== Summary Statistics (N=512) ===\n";
    std::cout << std::fixed << std::setprecision(4);
    std::cout << "Avg Gap to MST:      " << total_gap_to_mst / num_instances << "%\n";
    std::cout << "Avg Convex Hull Loyalty: " << (total_ch_loyalty / num_instances) * 100.0 << "%\n";
    std::cout << "-----------------------------------\n";

    return 0;
}
