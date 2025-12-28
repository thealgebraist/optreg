import csv
import time
import math
import random
import statistics
import copy

# ==============================================================================
# Solver with Full Assignment Extraction
# ==============================================================================

class BinPackingSolverGeometric:
    """
    Solves BPP exactly and returns the final bin configuration.
    """
    def __init__(self, items, capacity):
        self.items = sorted(items, reverse=True)
        self.capacity = capacity
        self.n = len(items)
        self.min_bins = self.n
        self.current_bins = []
        self.best_bins_state = [] # List of sums of best configuration

    def solve(self):
        # Upper Bound (FFD) as initial
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
        self.best_bins_state = list(ffd_bins) # Copy FFD state as best
        
        l1 = math.ceil(sum(self.items) / self.capacity)
        if self.min_bins == l1:
            return self.min_bins, self.best_bins_state

        self.current_bins = []
        self._backtrack(0)
        return self.min_bins, self.best_bins_state

    def _backtrack(self, item_idx):
        if len(self.current_bins) >= self.min_bins:
            return

        rem_sum = sum(self.items[item_idx:])
        current_used_space = sum(self.current_bins)
        available = (len(self.current_bins) * self.capacity) - current_used_space
        overflow = max(0, rem_sum - available)
        new_needed = math.ceil(overflow / self.capacity)
        
        if len(self.current_bins) + new_needed >= self.min_bins:
            return

        if item_idx == self.n:
            if len(self.current_bins) < self.min_bins:
                self.min_bins = len(self.current_bins)
                self.best_bins_state = list(self.current_bins)
            return

        item = self.items[item_idx]
        
        # Try existing
        for i in range(len(self.current_bins)):
            if self.current_bins[i] + item <= self.capacity:
                self.current_bins[i] += item
                self._backtrack(item_idx + 1)
                self.current_bins[i] -= item
                # Micro-optimization: if we just found a new best that equals LB, abort stack
                # (Not implemented here to keep recursion simple/safe)

        # Try new
        if len(self.current_bins) + 1 < self.min_bins:
            self.current_bins.append(item)
            self._backtrack(item_idx + 1)
            self.current_bins.pop()

# ==============================================================================
# Geometric Features
# ==============================================================================

def count_in_range(items, lower_frac, upper_frac, capacity):
    """Count items with weight in (lower * C, upper * C]"""
    # Note: Using strict > lower and <= upper is standard for L2/L3 definitions
    # But usually it's open/closed intervals. Let's do > lower * C and <= upper * C.
    low = lower_frac * capacity
    up = upper_frac * capacity
    return sum(1 for x in items if x > low and x <= up)

def conflict_density(items, capacity):
    """Probability that two randomly chosen items cannot fit in the same bin."""
    n = len(items)
    if n < 2: return 0.0
    conflicts = 0
    total_pairs = 0
    for i in range(n):
        for j in range(i+1, n):
            total_pairs += 1
            if items[i] + items[j] > capacity:
                conflicts += 1
    return conflicts / total_pairs if total_pairs > 0 else 0.0

def gini_coefficient(items):
    """Measure of inequality in item sizes."""
    if not items: return 0.0
    sorted_items = sorted(items)
    n = len(items)
    cum_sum = [0] * (n + 1)
    for i in range(n):
        cum_sum[i+1] = cum_sum[i] + sorted_items[i]
    
    numer = 0.0
    for i in range(n):
        numer += (i+1) * sorted_items[i]
    
    total = sum(items)
    if total == 0: return 0.0
    
    return (2 * numer) / (n * total) - (n + 1) / n

# ==============================================================================
# Main
# ==============================================================================

def run_analysis():
    n_instances = 4096 # Enough for correlation, faster than 8192
    capacity = 100
    results = []
    
    print(f"Generating and solving {n_instances} instances...")
    random.seed(999)
    
    start_t = time.time()
    
    for i in range(n_instances):
        n_items = random.randint(10, 19)
        items = [random.randint(10, 70) for _ in range(n_items)]
        
        solver = BinPackingSolverGeometric(items, capacity)
        opt_bins, final_config = solver.solve()
        
        # Base Metrics
        total_weight = sum(items)
        waste = (opt_bins * capacity) - total_weight
        waste_pct = (waste / (opt_bins * capacity)) * 100 if opt_bins > 0 else 0
        
        # Volumetric / Critical Region Metrics
        # Region 1: > 1/2 (Must be in separate bins)
        count_huge = count_in_range(items, 0.5, 1.0, capacity)
        # Region 2: (1/3, 1/2] (Can fit 2 but not 3)
        count_large = count_in_range(items, 1.0/3.0, 0.5, capacity)
        # Region 3: (1/4, 1/3] (Can fit 3 but not 4)
        count_medium = count_in_range(items, 0.25, 1.0/3.0, capacity)
        
        # Geometric Metrics
        conf_dens = conflict_density(items, capacity)
        gini = gini_coefficient(items)
        
        # Optimal Configuration Metrics
        # e.g. How "balanced" are the optimal bins?
        # Variance of the fill levels in the optimal solution.
        # If variance is high, optimal solution has some very full and some empty-ish bins.
        # If variance is low, all bins are equally full.
        fill_levels = final_config
        fill_variance = statistics.variance(fill_levels) if len(fill_levels) > 1 else 0.0
        
        results.append({
            "waste_pct": waste_pct,
            "n_items": n_items,
            "total_weight": total_weight,
            "count_huge": count_huge,      # > 1/2
            "count_large": count_large,    # 1/3 to 1/2
            "ratio_huge": count_huge / n_items,
            "ratio_large": count_large / n_items,
            "conflict_density": conf_dens,
            "gini_coeff": gini,
            "opt_fill_variance": fill_variance
        })
        
        if (i+1) % 1000 == 0:
            rate = (i+1) / (time.time() - start_t)
            print(f"Solved {i+1} ({rate:.1f} inst/s)...")

    # Correlations
    def correlation(key_x, key_y):
        xs = [r[key_x] for r in results]
        ys = [r[key_y] for r in results]
        try:
            mean_x = statistics.mean(xs)
            mean_y = statistics.mean(ys)
            stdev_x = statistics.stdev(xs)
            stdev_y = statistics.stdev(ys)
            if stdev_x == 0 or stdev_y == 0: return 0.0
            cov = sum((xi - mean_x)*(yi - mean_y) for xi, yi in zip(xs, ys)) / (len(xs) - 1)
            return cov / (stdev_x * stdev_y)
        except:
            return 0.0

    print("\n--- Geometric Correlations (Target: Waste %) ---")
    metrics = ["count_huge", "count_large", "ratio_huge", "ratio_large", 
               "conflict_density", "gini_coeff", "opt_fill_variance", "total_weight"]
    
    corrs = {m: correlation(m, "waste_pct") for m in metrics}
    
    for m, c in sorted(corrs.items(), key=lambda x: abs(x[1]), reverse=True):
        print(f"{m:20}: {c:.4f}")

    with open("bin_packing_geometric_patterns.md", "w") as f:
        f.write("# Bin Packing Geometric Analysis (N=4096)\n\n")
        f.write("Analyzed **4096** optimal solutions to correlate 'Waste %' with volumetric and geometric properties.\n\n")
        f.write("## Key Correlations\n\n")
        f.write("| Geometric Property | Correlation with Waste |\n")
        f.write("| :--- | :--- |\n")
        for m, c in sorted(corrs.items(), key=lambda x: abs(x[1]), reverse=True):
            f.write(f"| {m} | {c:.4f} |\n")
        
        f.write("\n## Metric Definitions\n")
        f.write("- **Conflict Density**: Probability that 2 random items *cannot* fit in the same bin.\n")
        f.write("- **Count Huge**: Items with $w > C/2$.\n")
        f.write("- **Count Large**: Items with $C/3 < w \\le C/2$.\n")
        f.write("- **Opt Fill Variance**: Variance of the used capacity across optimal bins.\n")

if __name__ == "__main__":
    run_analysis()
