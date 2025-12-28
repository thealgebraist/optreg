#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
#include <chrono>
#include "interior_point.h"

using namespace optreg;
using namespace std::chrono;

// Bin Packing Problem
struct BinPackingInstance {
    int num_items;
    int bin_capacity;
    std::vector<int> item_sizes;
};

// Generate random bin packing instance
BinPackingInstance generate_random_instance(int n_items, int capacity, int seed) {
    BinPackingInstance inst;
    inst.num_items = n_items;
    inst.bin_capacity = capacity;
    inst.item_sizes.resize(n_items);
    
    std::mt19937 gen(seed);
    std::uniform_int_distribution<> dis(capacity/4, capacity/2);  // Items 25-50% of capacity
    
    for (int i = 0; i < n_items; ++i) {
        inst.item_sizes[i] = dis(gen);
    }
    
    return inst;
}

// First Fit Decreasing Heuristic
int solve_ffd(const BinPackingInstance& inst) {
    std::vector<int> items = inst.item_sizes;
    std::sort(items.rbegin(), items.rend());  // Sort descending
    
    std::vector<int> bin_loads;
    
    for (int item : items) {
        bool placed = false;
        for (size_t j = 0; j < bin_loads.size(); ++j) {
            if (bin_loads[j] + item <= inst.bin_capacity) {
                bin_loads[j] += item;
                placed = true;
                break;
            }
        }
        if (!placed) {
            bin_loads.push_back(item);
        }
    }
    
    return bin_loads.size();
}

// Formulate as LP (simplified - using bin assignment variables)
// min Σy_j s.t. Σx_ij = 1 for all i, Σw_i*x_ij ≤ C*y_j for all j
LPProblem formulate_binpacking_lp(const BinPackingInstance& inst) {
    int n = inst.num_items;
    int m = std::min(n, 20);  // Max bins (upper bound)
    
    LPProblem prob;
    
    // Variables: x_ij (item i in bin j) + y_j (bin j used)
    int n_vars = n * m + m;
    prob.c = Vector::Zero(n_vars);
    
    // Objective: minimize number of bins
    for (int j = 0; j < m; ++j) {
        prob.c(n*m + j) = 1.0;  // y_j
    }
    
    // Constraints: each item in exactly one bin
    int n_constraints = n;
    prob.A.resize(n_constraints, n_vars);
    prob.b.resize(n_constraints);
    
    std::vector<Eigen::Triplet<double>> triplets;
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < m; ++j) {
            triplets.push_back({i, i*m + j, 1.0});
        }
        prob.b(i) = 1.0;
    }
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    // Bounds
    prob.lower_bound = Vector::Zero(n_vars);
    prob.upper_bound = Vector::Ones(n_vars);
    
    return prob;
}

int solve_ip_relaxation(const BinPackingInstance& inst, double time_limit_sec) {
    auto prob = formulate_binpacking_lp(inst);
    
    InteriorPointSolver solver;
    solver.set_max_iterations(100);
    solver.set_tolerance(0.01);
    
    auto start = high_resolution_clock::now();
    auto sol = solver.solve(prob);
    auto end = high_resolution_clock::now();
    
    double elapsed = duration_cast<milliseconds>(end - start).count() / 1000.0;
    
    if (elapsed > time_limit_sec || !sol.optimal) {
        return -1;  // Failed or timeout
    }
    
    // Extract bin count from solution
    int n = inst.num_items;
    int m = std::min(n, 20);
    int bins_used = 0;
    
    for (int j = 0; j < m; ++j) {
        if (sol.x(n*m + j) > 0.5) {  // y_j > 0.5 means bin used
            bins_used++;
        }
    }
    
    return bins_used;
}

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "Bin Packing: IP vs Heuristic" << std::endl;
    std::cout << "========================================" << std::endl;
    std::cout << "Testing on random instances (2s limit)" << std::endl;
    std::cout << std::endl;
    
    std::vector<int> sizes = {5, 8, 10, 12, 15};
    int capacity = 100;
    
    int heuristic_wins = 0;
    int ip_wins = 0;
    int ties = 0;
    int ip_failures = 0;
    
    std::cout << "Size  FFD   IP    Time   Result" << std::endl;
    std::cout << "----  ---  ---   -----  --------" << std::endl;
    
    for (int size : sizes) {
        for (int seed = 0; seed < 3; ++seed) {
            auto inst = generate_random_instance(size, capacity, seed);
            
            // Heuristic
            auto heur_start = high_resolution_clock::now();
            int heur_bins = solve_ffd(inst);
            auto heur_end = high_resolution_clock::now();
            double heur_time = duration_cast<microseconds>(heur_end - heur_start).count() / 1000.0;
            
            // IP
            auto ip_start = high_resolution_clock::now();
            int ip_bins = solve_ip_relaxation(inst, 2.0);
            auto ip_end = high_resolution_clock::now();
            double ip_time = duration_cast<milliseconds>(ip_end - ip_start).count() / 1000.0;
            
            std::string result;
            if (ip_bins == -1) {
                result = "IP FAIL";
                ip_failures++;
            } else if (ip_bins < heur_bins) {
                result = "IP WINS";
                ip_wins++;
            } else if (ip_bins > heur_bins) {
                result = "FFD WINS";
                heuristic_wins++;
            } else {
                result = "TIE";
                ties++;
            }
            
            printf("%4d  %3d  %3d  %5.2fs  %s\n", 
                   size, heur_bins, ip_bins == -1 ? -1 : ip_bins, ip_time, result.c_str());
        }
    }
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Summary:" << std::endl;
    std::cout << "  FFD wins:    " << heuristic_wins << std::endl;
    std::cout << "  IP wins:     " << ip_wins << std::endl;
    std::cout << "  Ties:        " << ties << std::endl;
    std::cout << "  IP failures: " << ip_failures << std::endl;
    std::cout << "========================================" << std::endl;
    
    std::cout << "\nConclusion: ";
    if (ip_failures > 10) {
        std::cout << "IP solver not suitable for bin packing" << std::endl;
    } else if (heuristic_wins > ip_wins) {
        std::cout << "FFD heuristic is better" << std::endl;
    } else {
        std::cout << "IP solver competitive!" << std::endl;
    }
    
    return 0;
}
