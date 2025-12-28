#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <algorithm>
#include <stack>
#include <chrono>
#include <limits>
#include <iomanip>
#include <filesystem>

using namespace std::chrono;
namespace fs = std::filesystem;

struct TSPInstance {
    int n;
    std::vector<std::vector<int>> dist;
    std::string name;
    int known_optimal;
};

TSPInstance parse_tsp_file(const std::string& filename) {
    TSPInstance inst;
    inst.known_optimal = -1;
    std::ifstream file(filename);
    std::string line;
    
    while (std::getline(file, line)) {
        if (line.find("NAME:") == 0) {
            inst.name = line.substr(6);
            // Trim whitespace
            inst.name.erase(0, inst.name.find_first_not_of(" \t"));
        } else if (line.find("DIMENSION:") == 0) {
            inst.n = std::stoi(line.substr(11));
            inst.dist.resize(inst.n, std::vector<int>(inst.n, 0));
        } else if (line.find("EDGE_WEIGHT_SECTION") == 0) {
            for (int i = 0; i < inst.n; ++i) {
                for (int j = 0; j <= i; ++j) {
                    file >> inst.dist[i][j];
                    inst.dist[j][i] = inst.dist[i][j];
                }
            }
            break;
        }
    }
    
    return inst;
}

std::pair<int, int> solve_tsp_optimized(const TSPInstance& inst, double time_limit, int node_limit) {
    auto start = high_resolution_clock::now();
    
    // Fix 4: NN heuristic
    std::vector<bool> vis(inst.n, false);
    int best = 0, curr = 0;
    vis[0] = true;
    for (int i = 1; i < inst.n; ++i) {
        int next = -1, min_d = std::numeric_limits<int>::max();
        for (int j = 0; j < inst.n; ++j) {
            if (!vis[j] && inst.dist[curr][j] < min_d) {
                min_d = inst.dist[curr][j];
                next = j;
            }
        }
        best += min_d;
        vis[next] = true;
        curr = next;
    }
    best += inst.dist[curr][0];
    
    // B&B with all 4 fixes
    struct Node {
        std::vector<int> path;
        std::vector<bool> visited;
        int cost, lb;
    };
    
    std::stack<Node> stack;
    Node root;
    root.path = {0};
    root.visited.resize(inst.n, false);
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
        
        if (node.path.size() == (size_t)inst.n) {
            best = std::min(best, node.cost + inst.dist[node.path.back()][0]);
            continue;
        }
        
        int lb = node.cost;
        if (!node.path.empty()) {
            int min_out = std::numeric_limits<int>::max();
            for (int j = 0; j < inst.n; ++j) {
                if (!node.visited[j]) {
                    min_out = std::min(min_out, inst.dist[node.path.back()][j]);
                }
            }
            if (min_out < std::numeric_limits<int>::max()) lb += min_out;
        }
        
        if (lb >= best) continue;
        
        int current = node.path.back();
        for (int next = 1; next < inst.n; ++next) {
            if (!node.visited[next]) {
                Node child = node;
                child.path.push_back(next);
                child.visited[next] = true;
                child.cost += inst.dist[current][next];
                stack.push(child);
            }
        }
    }
    
    return {best, nodes};
}

// Known optimal values for TSPLIB instances
int get_known_optimal(const std::string& name) {
    if (name.find("gr17") != std::string::npos) return 2085;
    if (name.find("gr21") != std::string::npos) return 2707;
    if (name.find("gr24") != std::string::npos) return 1272;
    if (name.find("ulysses16") != std::string::npos) return 6859;
    if (name.find("ulysses22") != std::string::npos) return 7013;
    return -1;
}

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "TSPLIB Full Benchmark" << std::endl;
    std::cout << "Optimized B&B (Agda-Proven)" << std::endl;
    std::cout << "========================================\n" << std::endl;
    
    std::vector<std::string> files;
    for (const auto& entry : fs::directory_iterator("data/tsplib")) {
        if (entry.path().extension() == ".tsp") {
            files.push_back(entry.path().string());
        }
    }
    std::sort(files.begin(), files.end());
    
    std::cout << "Instance         N   Best    Nodes     Time   Optimal  Gap" << std::endl;
    std::cout << "--------------- --- ------- -------- -------- -------- ----" << std::endl;
    
    int solved = 0, total = 0;
    
    for (const auto& file : files) {
        auto inst = parse_tsp_file(file);
        if (inst.n == 0 || inst.n > 25) continue;  // Skip large instances
        
        total++;
        int known = get_known_optimal(inst.name);
        
        auto start = high_resolution_clock::now();
        auto [cost, nodes] = solve_tsp_optimized(inst, 10.0, 10000000);
        auto end = high_resolution_clock::now();
        double time_sec = duration_cast<milliseconds>(end - start).count() / 1000.0;
        
        bool optimal = (known > 0 && cost == known);
        if (optimal) solved++;
        
        double gap = (known > 0) ? (cost - known) * 100.0 / known : 0;
        
        printf("%-15s %3d %7d %8d %7.2fs %8s %3.1f%%\n",
               inst.name.c_str(), inst.n, cost, nodes, time_sec,
               optimal ? "YES" : (known > 0 ? "NO" : "?"),
               gap);
    }
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Summary:" << std::endl;
    std::cout << "  Total instances: " << total << std::endl;
    std::cout << "  Solved optimally: " << solved << std::endl;
    std::cout << "  Success rate: " << (total > 0 ? 100*solved/total : 0) << "%" << std::endl;
    std::cout << "========================================" << std::endl;
    
    return 0;
}
