#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <random>
#include <cmath>
#include <algorithm>

using namespace optsolve;

// Helper to calculate angle between three points (a, b, c) at point b
double calculate_angle(const TSPProblem::Point& a, const TSPProblem::Point& b, const TSPProblem::Point& c) {
    double ux = a.x - b.x;
    double uy = a.y - b.y;
    double vx = c.x - b.x;
    double vy = c.y - b.y;
    
    double dot = ux * vx + uy * vy;
    double mag_u = std::sqrt(ux * ux + uy * uy);
    double mag_v = std::sqrt(vx * vx + vy * vy);
    
    if (mag_u < 1e-9 || mag_v < 1e-9) return 0.0;
    
    double cos_theta = dot / (mag_u * mag_v);
    // Clamp for safety
    cos_theta = std::max(-1.0, std::min(1.0, cos_theta));
    return std::acos(cos_theta) * 180.0 / M_PI;
}

struct NodeGeometricFeatures {
    int instance_id;
    int node_id;
    double angle;
    double dist_prev;
    double dist_next;
};

void save_geometric_features(std::ofstream& out, int inst_id, const TSPProblem& p, const std::vector<size_t>& tour) {
    size_t n = tour.size();
    for (size_t i = 0; i < n; ++i) {
        size_t prev = tour[(i + n - 1) % n];
        size_t curr = tour[i];
        size_t next = tour[(i + 1) % n];
        
        double angle = calculate_angle(p.coords[prev], p.coords[curr], p.coords[next]);
        double d_prev = p.distances[prev][curr];
        double d_next = p.distances[curr][next];
        
        out << inst_id << "," << curr << "," << angle << "," << d_prev << "," << d_next << "\n";
    }
}

int main() {
    std::mt19937 rng(1337);
    std::uniform_int_distribution<size_t> n_dist(10, 19);
    TSPBranchBound solver;

    std::ofstream base_features("optreg/build/tsp_base_geometric.csv");
    std::ofstream removal_sols("optreg/build/tsp_removal_results.csv");
    
    base_features << "instance_id,node_id,angle,dist_prev,dist_next\n";
    removal_sols << "instance_id,removed_node_id,edge_iou,n_remaining\n";

    std::cout << "Starting Node Removal Study (512 instances, n < 20)...\n";

    for (int i = 0; i < 512; ++i) {
        size_t n = n_dist(rng);
        TSPProblem base_p = TSPProblem::random(n, i + 5000);
        
        auto base_res = solver.solve(base_p);
        if (!base_res.success) continue;
        
        save_geometric_features(base_features, i, base_p, base_res.solution.tour);
        
        std::vector<std::pair<size_t, size_t>> base_edges;
        for (size_t k = 0; k < n; ++k) {
            size_t u = base_res.solution.tour[k];
            size_t v = base_res.solution.tour[(k + 1) % n];
            base_edges.push_back({std::min(u, v), std::max(u, v)});
        }

        // Try removing 10 random nodes (one at a time)
        std::vector<int> nodes_to_remove(n);
        std::iota(nodes_to_remove.begin(), nodes_to_remove.end(), 0);
        std::shuffle(nodes_to_remove.begin(), nodes_to_remove.end(), rng);
        
        int removals = std::min((int)n - 3, 10);
        for (int r = 0; r < removals; ++r) {
            int target = nodes_to_remove[r];
            
            // Create sub-problem
            TSPProblem sub_p;
            sub_p.n_cities = n - 1;
            sub_p.coords.reserve(n - 1);
            std::vector<size_t> mapping;
            for (size_t j = 0; j < n; ++j) {
                if ((int)j == target) continue;
                sub_p.coords.push_back(base_p.coords[j]);
                mapping.push_back(j);
            }
            
            sub_p.distances.assign(sub_p.n_cities, std::vector<double>(sub_p.n_cities, 0.0));
            for (size_t u = 0; u < sub_p.n_cities; ++u) {
                for (size_t v = 0; v < sub_p.n_cities; ++v) {
                    sub_p.distances[u][v] = base_p.distances[mapping[u]][mapping[v]];
                }
            }
            
            auto sub_res = solver.solve(sub_p);
            if (!sub_res.success) continue;
            
            // Compare edges
            std::vector<std::pair<size_t, size_t>> sub_edges;
            for (size_t k = 0; k < sub_p.n_cities; ++k) {
                size_t u = mapping[sub_res.solution.tour[k]];
                size_t v = mapping[sub_res.solution.tour[(k + 1) % sub_p.n_cities]];
                sub_edges.push_back({std::min(u, v), std::max(u, v)});
            }
            
            // Calculate IoU of edges (ignoring edges connected to target)
            int intersection = 0;
            int union_size = 0;
            
            auto base_edges_filtered = base_edges;
            base_edges_filtered.erase(
                std::remove_if(base_edges_filtered.begin(), base_edges_filtered.end(), 
                    [target](const auto& pair) { return (int)pair.first == target || (int)pair.second == target; }), 
                base_edges_filtered.end()
            );
            
            for (const auto& e1 : base_edges_filtered) {
                bool found = false;
                for (const auto& e2 : sub_edges) {
                    if (e1 == e2) { found = true; break; }
                }
                if (found) intersection++;
            }
            
            // IoU of remaining edges
            double iou = (double)intersection / (double)(base_edges_filtered.size() + sub_edges.size() - intersection);
            removal_sols << i << "," << target << "," << iou << "," << (n - 1) << "\n";
        }
        
        if ((i + 1) % 50 == 0) std::cout << "Done " << (i + 1) << " instances...\n";
    }
    
    base_features.close();
    removal_sols.close();
    std::cout << "Node removal study complete.\n";
    return 0;
}
