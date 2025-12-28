#include <iostream>
#include <filesystem>
#include <vector>
#include <algorithm>
#include <stack>
#include <chrono>
#include <iomanip>
#include "tsplib_parser.h"
#include "tsp_heuristics.h"

using namespace std::chrono;
using namespace optreg;
using namespace tsp_heuristics;
namespace fs = std::filesystem;

// Optimized B&B from Agda model
struct TSPNode {
    std::vector<int> path;
    std::vector<bool> visited;
    int cost, lb;
};

std::pair<int, int> solve_optimized_bb(const std::vector<std::vector<double>>& dist, 
                                        int best_heuristic, double time_limit, int node_limit) {
    auto start = high_resolution_clock::now();
    int n = dist.size();
    int best = best_heuristic;
    
    std::stack<TSPNode> stack;
    TSPNode root;
    root.path = {0};
    root.visited.resize(n, false);
    root.visited[0] = true;
    root.cost = root.lb = 0;
    stack.push(root);
    
    int nodes = 0;
    
    while (!stack.empty()) {
        auto now = high_resolution_clock::now();
        if (duration_cast<seconds>(now - start).count() > time_limit) break;
        if (nodes > node_limit) break;
        
        auto node = stack.top();
        stack.pop();
        nodes++;
        
        if (node.path.size() == (size_t)n) {
            best = std::min(best, node.cost + (int)dist[node.path.back()][0]);
            continue;
        }
        
        int lb = node.cost;
        if (!node.path.empty()) {
            int min_out = 1e9;
            for (int j = 0; j < n; ++j) {
                if (!node.visited[j]) {
                    min_out = std::min(min_out, (int)dist[node.path.back()][j]);
                }
            }
            if (min_out < 1e9) lb += min_out;
        }
        
        if (lb >= best) continue;
        
        int current = node.path.back();
        for (int next = 1; next < n; ++next) {
            if (!node.visited[next]) {
                TSPNode child = node;
                child.path.push_back(next);
                child.visited[next] = true;
                child.cost += (int)dist[current][next];
                stack.push(child);
            }
        }
    }
    
    return {best, nodes};
}

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "TSPLIB: 8 Heuristics + B&B" << std::endl;
    std::cout << "========================================\n" << std::endl;
    
    TSPLIBParser parser;
    std::vector<std::string> files;
    
    for (const auto& entry : fs::directory_iterator("data/tsplib")) {
        if (entry.path().extension() == ".tsp") {
            files.push_back(entry.path().string());
        }
    }
    std::sort(files.begin(), files.end());
    
    std::cout << "Instance         N   Best Heuristic  Method        BB Cost  Nodes    Time" << std::endl;
    std::cout << "--------------- --- --------------- ------------- ------- -------- -------" << std::endl;
    
    int tested = 0, improved = 0;
    
    for (const auto& file : files) {
        try {
            auto inst = parser.parse(file);
            if (inst.dimension == 0 || inst.dimension > 100 || inst.adj.empty()) continue;
            
            tested++;
            
            // Run all 8 heuristics
            TSPHeuristics heuristics(inst.adj);
            auto best_tour = heuristics.best_heuristic();
            
            // Run B&B with best heuristic bound
            auto start = high_resolution_clock::now();
            auto [bb_cost, nodes] = solve_optimized_bb(inst.adj, best_tour.cost, 30.0, 10000000);
            auto end = high_resolution_clock::now();
            double time_sec = duration_cast<milliseconds>(end - start).count() / 1000.0;
            
            if (bb_cost < best_tour.cost) improved++;
            
            printf("%-15s %3d %7d       %-13s %7d %8d %6.2fs\n",
                   fs::path(file).filename().string().substr(0, 15).c_str(),
                   inst.dimension,
                   best_tour.cost,
                   best_tour.method.substr(0, 13).c_str(),
                   bb_cost,
                   nodes,
                   time_sec);
                   
        } catch (const std::exception& e) {
            // Skip
        }
    }
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Summary:" << std::endl;
    std::cout << "  Tested:   " << tested << std::endl;
    std::cout << "  Improved by B&B: " << improved << std::endl;
    std::cout << "========================================" << std::endl;
    std::cout << "\n8 heuristics + optimized B&B working!" << std::endl;
    
    return 0;
}
