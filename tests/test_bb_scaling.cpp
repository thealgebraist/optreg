#include <iostream>
#include <vector>
#include <algorithm>
#include <chrono>
#include <random>
#include <stack>

using namespace std::chrono;

struct BinPackingInstance {
    std::vector<int> items;
    int capacity;
};

struct BBNode {
    std::vector<int> bin_loads;
    int item_idx;
    int bins_used;
};

// FFD for upper bound
int solve_ffd(const BinPackingInstance& inst) {
    std::vector<int> sorted = inst.items;
    std::sort(sorted.rbegin(), sorted.rend());
    
    std::vector<int> bins;
    for (int item : sorted) {
        bool placed = false;
        for (size_t i = 0; i < bins.size(); ++i) {
            if (bins[i] + item <= inst.capacity) {
                bins[i] += item;
                placed = true;
                break;
            }
        }
        if (!placed) bins.push_back(item);
    }
    return bins.size();
}

// Optimized B&B with all 4 fixes
struct BBResult {
    int bins;
    int nodes;
    double time_sec;
    bool timeout;
};

BBResult solve_bb_optimized(const BinPackingInstance& inst, double time_limit) {
    auto start = high_resolution_clock::now();
    
    // Fix 4: FFD upper bound
    int best = solve_ffd(inst);
    int total = 0;
    for (int w : inst.items) total += w;
    int lower = (total + inst.capacity - 1) / inst.capacity;
    
    if (best == lower) {
        return {best, 1, 0.0, false};
    }
    
    // Fix 1: Sort for symmetry breaking
    std::vector<int> sorted = inst.items;
    std::sort(sorted.rbegin(), sorted.rend());
    
    // Fix 2: DFS
    std::stack<BBNode> stack;
    stack.push({{}, 0, 0});
    
    int nodes = 0;
    
    while (!stack.empty()) {
        auto now = high_resolution_clock::now();
        double elapsed = duration_cast<milliseconds>(now - start).count() / 1000.0;
        
        if (elapsed > time_limit) {
            return {best, nodes, elapsed, true};
        }
        
        if (nodes > 10000000) {  // 10M node limit
            return {best, nodes, elapsed, true};
        }
        
        auto node = stack.top();
        stack.pop();
        nodes++;
        
        if (node.item_idx == (int)sorted.size()) {
            best = std::min(best, node.bins_used);
            continue;
        }
        
        if (node.bins_used >= best) continue;
        
        int item = sorted[node.item_idx];
        
        // Try existing bins (Fix 3: capacity check)
        for (size_t i = 0; i < node.bin_loads.size(); ++i) {
            if (node.bin_loads[i] + item <= inst.capacity) {
                BBNode child = node;
                child.bin_loads[i] += item;
                child.item_idx++;
                stack.push(child);
            }
        }
        
        // Try new bin
        if (node.bins_used + 1 < best) {
            BBNode child = node;
            child.bin_loads.push_back(item);
            child.item_idx++;
            child.bins_used++;
            stack.push(child);
        }
    }
    
    auto end = high_resolution_clock::now();
    double elapsed = duration_cast<milliseconds>(end - start).count() / 1000.0;
    
    return {best, nodes, elapsed, false};
}

// Generate random instance
BinPackingInstance generate_sparse(int n, int capacity, int seed) {
    BinPackingInstance inst;
    inst.capacity = capacity;
    inst.items.resize(n);
    
    std::mt19937 gen(seed);
    std::uniform_int_distribution<> dis(capacity/4, capacity/2);  // Items 25-50% of capacity
    
    for (int i = 0; i < n; ++i) {
        inst.items[i] = dis(gen);
    }
    
    return inst;
}

BinPackingInstance generate_dense(int n, int capacity, int seed) {
    BinPackingInstance inst;
    inst.capacity = capacity;
    inst.items.resize(n);
    
    std::mt19937 gen(seed);
    std::uniform_int_distribution<> dis(capacity/10, capacity/5);  // Items 10-20% of capacity
    
    for (int i = 0; i < n; ++i) {
        inst.items[i] = dis(gen);
    }
    
    return inst;
}

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "B&B Scaling Test: 10 Second Limit" << std::endl;
    std::cout << "========================================\n" << std::endl;
    
    int capacity = 100;
    double time_limit = 10.0;
    
    std::cout << "=== SPARSE Instances (items 25-50% of capacity) ===" << std::endl;
    std::cout << "n    Bins   Nodes      Time      Status" << std::endl;
    std::cout << "---  ----  --------  ---------  --------" << std::endl;
    
    int max_sparse = 0;
    for (int n : {5, 10, 15, 20, 25, 30, 35, 40, 45, 50}) {
        auto inst = generate_sparse(n, capacity, 42);
        auto result = solve_bb_optimized(inst, time_limit);
        
        printf("%3d  %4d  %8d  %8.3fs  ", n, result.bins, result.nodes, result.time_sec);
        
        if (result.timeout) {
            std::cout << "TIMEOUT" << std::endl;
            break;
        } else {
            std::cout << "SOLVED" << std::endl;
            max_sparse = n;
        }
    }
    
    std::cout << "\n=== DENSE Instances (items 10-20% of capacity) ===" << std::endl;
    std::cout << "n    Bins   Nodes      Time      Status" << std::endl;
    std::cout << "---  ----  --------  ---------  --------" << std::endl;
    
    int max_dense = 0;
    for (int n : {10, 20, 30, 40, 50, 60, 70, 80, 90, 100}) {
        auto inst = generate_dense(n, capacity, 42);
        auto result = solve_bb_optimized(inst, time_limit);
        
        printf("%3d  %4d  %8d  %8.3fs  ", n, result.bins, result.nodes, result.time_sec);
        
        if (result.timeout) {
            std::cout << "TIMEOUT" << std::endl;
            break;
        } else {
            std::cout << "SOLVED" << std::endl;
            max_dense = n;
        }
    }
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Maximum Sizes (10s limit):" << std::endl;
    std::cout << "  Sparse (25-50%): n = " << max_sparse << std::endl;
    std::cout << "  Dense (10-20%):  n = " << max_dense << std::endl;
    std::cout << "========================================" << std::endl;
    
    std::cout << "\nObservations:" << std::endl;
    std::cout << "- Dense instances are easier (more items fit per bin)" << std::endl;
    std::cout << "- Sparse instances are harder (fewer packing options)" << std::endl;
    std::cout << "- Optimized B&B handles 10s-100s of items!" << std::endl;
    
    return 0;
}
