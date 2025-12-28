#include "bin_packing_neon.hpp"
#include <iostream>
#include <vector>
#include <random>
#include <chrono>
#include <numeric>
#include <algorithm>

// =============================================================================
// Exact Solver (B&B) - Ported from Python for Baseline
// =============================================================================

class ExactBinPackingSolver {
    std::vector<int> items;
    int capacity;
    int n;
    int min_bins;
    std::vector<int> current_bins;
    int l1_bound;

public:
    ExactBinPackingSolver(const std::vector<int>& items_in, int cap) 
        : items(items_in), capacity(cap), n(items_in.size()) {
        std::sort(items.rbegin(), items.rend());
        long long sum_w = 0;
        for(int w : items) sum_w += w;
        l1_bound = (sum_w + capacity - 1) / capacity; // ceil
        min_bins = n;
    }

    int solve() {
        // FFD Init
        std::vector<int> ffd_bins;
        for(int item : items) {
            bool placed = false;
            for(int &bin : ffd_bins) {
                if(bin + item <= capacity) {
                    bin += item;
                    placed = true;
                    break;
                }
            }
            if(!placed) ffd_bins.push_back(item);
        }
        min_bins = ffd_bins.size();
        if(min_bins == l1_bound) return min_bins;

        current_bins.clear();
        backtrack(0);
        return min_bins;
    }

private:
    void backtrack(int item_idx) {
        if((int)current_bins.size() >= min_bins) return;
        
        // Lower bound check
        long long rem_sum = 0;
        for(int k=item_idx; k<n; ++k) rem_sum += items[k];
        int bound = current_bins.size() + (rem_sum + capacity - 1) / capacity;
        if(bound >= min_bins) return;

        if(item_idx == n) {
            if((int)current_bins.size() < min_bins) min_bins = current_bins.size();
            return;
        }

        int item = items[item_idx];
        
        // Try existing
        for(int i=0; i<current_bins.size(); ++i) {
            if(current_bins[i] + item <= capacity) {
                current_bins[i] += item;
                backtrack(item_idx + 1);
                current_bins[i] -= item;
                if(min_bins == l1_bound) return;
            }
        }

        // Try new
        if((int)current_bins.size() + 1 < min_bins) {
            current_bins.push_back(item);
            backtrack(item_idx + 1);
            current_bins.pop_back();
        }
    }
};

// =============================================================================
// Main Benchmark
// =============================================================================

int main() {
    using namespace optreg;
    
    int n_instances = 4096;
    int capacity = 100;
    
    std::mt19937 rng(12345);
    std::uniform_int_distribution<int> n_dist(10, 16); // Match Python test range
    std::uniform_int_distribution<int> w_dist(10, 70);
    
    int exact_matches = 0;
    int neon_better = 0; // Should be impossible if Exact is correct
    int neon_worse = 0;
    
    // Timers
    double neon_time = 0;
    double exact_time = 0;
    
    for (int i = 0; i < n_instances; ++i) {
        int n = n_dist(rng);
        std::vector<int> items(n);
        for(int j=0; j<n; ++j) items[j] = w_dist(rng);
        
        // NEON
        auto t1 = std::chrono::high_resolution_clock::now();
        NeonBinPackingSolver neon_solver(items, capacity);
        int neon_bins = neon_solver.solve();
        auto t2 = std::chrono::high_resolution_clock::now();
        neon_time += std::chrono::duration<double>(t2 - t1).count();
        
        // EXACT
        auto t3 = std::chrono::high_resolution_clock::now();
        ExactBinPackingSolver exact_solver(items, capacity);
        int exact_bins = exact_solver.solve();
        auto t4 = std::chrono::high_resolution_clock::now();
        exact_time += std::chrono::duration<double>(t4 - t3).count();
        
        if (neon_bins == exact_bins) {
            exact_matches++;
        } else if (neon_bins < exact_bins) {
            neon_better++; // Sign of Exact Solver bug or logic error?
        } else {
            neon_worse++;
        }
        
        if ((i+1) % 500 == 0) std::cout << "Processed " << i+1 << "...\n";
    }
    
    std::cout << "\n--- Neon vs Optimal Results (N=" << n_instances << ", n<17) ---\n";
    
    std::cout << "Optimality:\n";
    std::cout << "  Exact Matches: " << exact_matches << " (" << (double)exact_matches/n_instances*100.0 << "%)\n";
    std::cout << "  Neon Failed (Found Worse): " << neon_worse << " (" << (double)neon_worse/n_instances*100.0 << "%)\n";
    std::cout << "  Neon Won (Found Better - Should be 0): " << neon_better << "\n";
    
    std::cout << "\nTiming:\n";
    // We already know Neon is ~0.004s total.
    std::cout << "  Neon Total Time:  " << neon_time << "s\n";
    std::cout << "  Exact Total Time: " << exact_time << "s\n";
    std::cout << "  Speedup: " << exact_time / neon_time << "x\n";
    
    return 0;
}
