#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <random>
#include <cmath>
#include <algorithm>

using namespace optsolve;

int main() {
    size_t n = 1024;
    std::mt19937 rng(42);
    // Explicitly generate 1024 nodes in [0, 512]
    TSPProblem p;
    p.n_cities = n;
    p.coords.resize(n);
    p.distances.resize(n, std::vector<double>(n, 0.0));
    
    std::uniform_real_distribution<double> dist_gen(0.0, 512.0);
    for (size_t i = 0; i < n; ++i) {
        p.coords[i] = {dist_gen(rng), dist_gen(rng)};
    }
    
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = i + 1; j < n; ++j) {
            double d = std::sqrt(std::pow(p.coords[i].x - p.coords[j].x, 2) + std::pow(p.coords[i].y - p.coords[j].y, 2));
            p.distances[i][j] = p.distances[j][i] = d;
        }
    }
    
    TSPTopologicalBoltzmann solver;
    
    std::cout << "Starting TSP Animation Simulation (N=1024, Steps=256, Scale=512x512)...\n";
    
    for (int step = 0; step < 256; ++step) {
        auto res = solver.solve(p);
        
        std::string filename = "optreg/build/frame_" + std::to_string(step) + ".txt";
        std::ofstream out(filename);
        for (const auto& c : p.coords) {
            out << c.x << " " << c.y << "\n";
        }
        out << "TOUR\n";
        for (size_t idx : res.solution.tour) {
            out << idx << " ";
        }
        out << "\n";
        out.close();
        
        // Perturb nodes: Gaussian walk sigma=1.0 (larger since scaled up)
        std::normal_distribution<double> g_dist(0.0, 1.0);
        for (size_t i = 0; i < n; ++i) {
            p.coords[i].x += g_dist(rng);
            p.coords[i].y += g_dist(rng);
            p.coords[i].x = std::clamp(p.coords[i].x, 0.0, 512.0);
            p.coords[i].y = std::clamp(p.coords[i].y, 0.0, 512.0);
        }
        
        // Recompute distance matrix
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = 0; j < n; ++j) {
                if (i == j) p.distances[i][j] = 0;
                else p.distances[i][j] = std::sqrt(std::pow(p.coords[i].x - p.coords[j].x, 2) + std::pow(p.coords[i].y - p.coords[j].y, 2));
            }
        }
        
        if ((step + 1) % 32 == 0) {
            std::cout << "Step " << (step + 1) << " complete.\n";
        }
    }
    
    std::cout << "Simulation data generated.\n";
    return 0;
}
