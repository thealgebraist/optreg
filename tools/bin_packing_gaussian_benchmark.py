import csv
import time
import math
import random
import statistics
import copy

# ==============================================================================
# Exact Solver (B&B)
# ==============================================================================

class BinPackingSolverOptimized:
    def __init__(self, items, capacity):
        self.items = sorted(items, reverse=True)
        self.capacity = capacity
        self.n = len(items)
        self.min_bins = self.n
        self.current_bins = []
        self.l1_bound = math.ceil(sum(items) / self.capacity)

    def solve(self):
        # FFD Init
        ffd_bins = []
        for item in self.items:
            placed = False
            for i in range(len(ffd_bins)):
                if ffd_bins[i] + item <= self.capacity:
                    ffd_bins[i] += item
                    placed = True
                    break
            if not placed:
                ffd_bins.append(item)
        self.min_bins = len(ffd_bins)
        if self.min_bins == self.l1_bound: return self.min_bins

        self.current_bins = []
        self._backtrack(0)
        return self.min_bins

    def _backtrack(self, item_idx):
        if len(self.current_bins) >= self.min_bins: return
        rem_sum = sum(self.items[item_idx:])
        lower_bound = len(self.current_bins) + math.ceil(rem_sum / self.capacity)
        if lower_bound >= self.min_bins: return
        if item_idx == self.n:
            self.min_bins = min(self.min_bins, len(self.current_bins))
            return
        
        item = self.items[item_idx]
        for i in range(len(self.current_bins)):
            if self.current_bins[i] + item <= self.capacity:
                self.current_bins[i] += item
                self._backtrack(item_idx + 1)
                self.current_bins[i] -= item
                if self.min_bins == self.l1_bound: return

        if len(self.current_bins) + 1 < self.min_bins:
            self.current_bins.append(item)
            self._backtrack(item_idx + 1)
            self.current_bins.pop()

# ==============================================================================
# Gaussian Walk Heuristic (Stochastic Best Fit)
# ==============================================================================

class HeuristicGaussianFit:
    """
    Stochastically perturbed Best Fit Decreasing.
    
    Algorithm:
    1. Sort items Decreasing.
    2. For each item:
       - Calculate 'score' for each valid bin.
       - Base Score = Remainder (Capacity - Load - Item). We want to MINIMIZE this (Best Fit).
       - Perturbation: Score' = Score + Gaussian(0, sigma).
       - Select bin with Minimum Score'.
       - If no bin fits, open new one.
    3. Repeat K times and return Best Solution.
    """
    def __init__(self, items, capacity, sigma=5.0, restarts=10):
        self.items = sorted(items, reverse=True)
        self.capacity = capacity
        self.sigma = sigma
        self.restarts = restarts
        
    def solve(self):
        best_bins_count = len(self.items) # Worst case
        
        for _ in range(self.restarts):
            bins = []
            
            for item in self.items:
                # Find valid bins
                candidates = []
                for i, load in enumerate(bins):
                    if load + item <= self.capacity:
                        gap = self.capacity - load - item
                        # Add Gaussian noise
                        # Score: Lower is better (Best Fit)
                        score = gap + random.gauss(0, self.sigma)
                        candidates.append((score, i))
                        
                if candidates:
                    # Pick best (lowest score) candidate
                    candidates.sort(key=lambda x: x[0])
                    best_idx = candidates[0][1]
                    bins[best_idx] += item
                else:
                    # Open new bin
                    bins.append(item)
            
            best_bins_count = min(best_bins_count, len(bins))
            
        return best_bins_count

# ==============================================================================
# FFD (Deterministic)
# ==============================================================================

def solve_ffd(items, capacity):
    sorted_items = sorted(items, reverse=True)
    bins = []
    for item in sorted_items:
        placed = False
        for i in range(len(bins)):
            if bins[i] + item <= capacity:
                bins[i] += item
                placed = True
                break
        if not placed:
            bins.append(item)
    return len(bins)

# ==============================================================================
# Benchmark
# ==============================================================================

def run_benchmark():
    n_instances = 4096
    capacity = 100
    sigma = 10.0 # Standard deviation for noise
    restarts = 10 
    
    # Validation counters
    ffd_wins = 0
    gauss_wins = 0
    draws = 0
    opt_matches_ffd = 0
    opt_matches_gauss = 0
    
    print(f"Benchmarking Gaussian Fit (Sigma={sigma}, K={restarts}) vs FFD/Opt...")
    random.seed(42)
    
    t0_global = time.time()
    
    for i in range(n_instances):
        n_items = random.randint(10, 15)
        items = [random.randint(10, 70) for _ in range(n_items)]
        
        # 1. Optimal B&B
        opt_solver = BinPackingSolverOptimized(items, capacity)
        opt_bins = opt_solver.solve()
        
        # 2. FFD
        ffd_bins = solve_ffd(items, capacity)
        
        # 3. Gaussian
        gauss_solver = HeuristicGaussianFit(items, capacity, sigma, restarts)
        gauss_bins = gauss_solver.solve()
        
        # Stats
        if ffd_bins == opt_bins: opt_matches_ffd += 1
        if gauss_bins == opt_bins: opt_matches_gauss += 1
        
        if ffd_bins < gauss_bins: ffd_wins += 1
        elif gauss_bins < ffd_bins: gauss_wins += 1
        else: draws += 1
        
        if (i+1) % 500 == 0:
            print(f"Processed {i+1}...")
            
    total_time = time.time() - t0_global
            
    print("\n--- Gaussian Heuristic Results ---")
    print(f"Instances: {n_instances}")
    print(f"Overall Speed: {n_instances/total_time:.1f} inst/s")
    
    print(f"\nExact Optimality:")
    print(f"  FFD:      {opt_matches_ffd}/{n_instances} ({opt_matches_ffd/n_instances*100:.2f}%)")
    print(f"  Gaussian: {opt_matches_gauss}/{n_instances} ({opt_matches_gauss/n_instances*100:.2f}%)")
    
    print(f"\nHead-to-Head (FFD vs Gaussian):")
    print(f"  FFD Wins:   {ffd_wins}")
    print(f"  Gauss Wins: {gauss_wins}")
    print(f"  Draws:      {draws}")

    with open("bin_packing_gaussian_results.md", "w") as f:
        f.write("# Bin Packing Gaussian Heuristic Results\n\n")
        f.write(f"Analyzed **{n_instances}** instances ($n<16$) using **Stochastic Best Fit** ($\\sigma={sigma}, K={restarts}$).\n\n")
        
        f.write("## Performance\n")
        f.write(f"- **Optimality Rate**: **{opt_matches_gauss/n_instances*100:.2f}%**\n")
        f.write(f"- **FFD Optimality**: {opt_matches_ffd/n_instances*100:.2f}%\n\n")
        
        f.write("## Head-to-Head\n")
        f.write(f"- Gaussian vs FFD Draws: {draws} ({draws/n_instances*100:.1f}%)\n")
        if gauss_wins > 0:
            f.write(f"- **Gaussian SURPRISE Wins**: {gauss_wins} (Beat FFD!)\n")
        else:
            f.write(f"- Gaussian Wins: 0\n")
            
        f.write("\n## Conclusion\n")
        if opt_matches_gauss >= opt_matches_ffd:
             f.write("The Gaussian Walk matched or exceeded FFD's performance through simple stochastic variation.\n")
        else:
             f.write("Deterministic FFD is superior. Adding noise to the 'score' degraded performance compared to the clean greedy signal.\n")

if __name__ == "__main__":
    run_benchmark()
