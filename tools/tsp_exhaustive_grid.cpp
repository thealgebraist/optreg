#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <fstream>
#include <iomanip>
#include <numeric>

struct Point {
    double x, y;
};

struct Edge {
    size_t u, v;
    bool operator<(const Edge& other) const {
        if (u != other.u) return u < other.u;
        return v < other.v;
    }
};

int main() {
    std::vector<Point> grid;
    for (int y = 0; y < 4; ++y) {
        for (int x = 0; x < 4; ++x) {
            grid.push_back({(double)x, (double)y});
        }
    }

    std::string filename = "optreg/build/exhaustive_tsp_4x4.csv";
    std::ofstream out(filename);
    
    // Header
    out << "instance_id,n1,n2,n3,n4,opt_dist,opt_edges\n";

    size_t instance_id = 0;
    std::vector<int> mask(16, 0);
    std::fill(mask.end() - 4, mask.end(), 1);

    do {
        std::vector<size_t> subset;
        for (size_t i = 0; i < 16; ++i) {
            if (mask[i]) subset.push_back(i);
        }

        size_t n1 = subset[0], n2 = subset[1], n3 = subset[2], n4 = subset[3];
        
        auto dist = [&](size_t i, size_t j) {
            return std::sqrt(std::pow(grid[i].x - grid[j].x, 2) + std::pow(grid[i].y - grid[j].y, 2));
        };

        // There are 3 possible tours for 4 nodes
        double d1 = dist(n1, n2) + dist(n2, n3) + dist(n3, n4) + dist(n4, n1);
        double d2 = dist(n1, n2) + dist(n2, n4) + dist(n4, n3) + dist(n3, n1);
        double d3 = dist(n1, n3) + dist(n3, n2) + dist(n2, n4) + dist(n4, n1);

        double opt_dist = std::min({d1, d2, d3});
        
        std::vector<Edge> opt_edges;
        auto add_unique_edge = [&](size_t a, size_t b) {
            size_t u = std::min(a, b);
            size_t v = std::max(a, b);
            opt_edges.push_back({u, v});
        };

        auto add_tour_edges = [&](size_t a, size_t b, size_t c, size_t d) {
            add_unique_edge(a, b);
            add_unique_edge(b, c);
            add_unique_edge(c, d);
            add_unique_edge(d, a);
        };

        if (std::abs(d1 - opt_dist) < 1e-9) add_tour_edges(n1, n2, n3, n4);
        if (std::abs(d2 - opt_dist) < 1e-9) add_tour_edges(n1, n2, n4, n3);
        if (std::abs(d3 - opt_dist) < 1e-9) add_tour_edges(n1, n3, n2, n4);

        // Deduplicate edges
        std::sort(opt_edges.begin(), opt_edges.end());
        opt_edges.erase(std::unique(opt_edges.begin(), opt_edges.end(), [](const Edge& a, const Edge& b){
            return a.u == b.u && a.v == b.v;
        }), opt_edges.end());

        out << instance_id << "," << n1 << "," << n2 << "," << n3 << "," << n4 << "," << opt_dist << ",";
        for (size_t i = 0; i < opt_edges.size(); ++i) {
            out << opt_edges[i].u << "-" << opt_edges[i].v << (i == opt_edges.size() - 1 ? "" : ";");
        }
        out << "\n";

        instance_id++;
    } while (std::next_permutation(mask.begin(), mask.end()));

    std::cout << "Generated " << instance_id << " instances." << std::endl;
    return 0;
}
