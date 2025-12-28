import csv
import time
import math
import random
import statistics

class BinPackingSolver:
    """Exact Branch and Bound solver for Bin Packing Problem."""
    def __init__(self, items, capacity):
        self.items = sorted(items, reverse=True)
        self.capacity = capacity
        self.n = len(items)
        self.min_bins = self.n
        self.current_bins = []

    def solve(self):
        self.min_bins = self.n
        self.current_bins = []
        self._backtrack(0)
        return self.min_bins

    def _backtrack(self, item_idx):
        rem_sum = sum(self.items[item_idx:])
        lower_bound = len(self.current_bins) + math.ceil(rem_sum / self.capacity)
        if lower_bound >= self.min_bins:
            return

        if item_idx == self.n:
            self.min_bins = min(self.min_bins, len(self.current_bins))
            return

        item = self.items[item_idx]
        
        for i in range(len(self.current_bins)):
            if self.current_bins[i] + item <= self.capacity:
                self.current_bins[i] += item
                self._backtrack(item_idx + 1)
                self.current_bins[i] -= item
                if self.min_bins == lower_bound: return

        if len(self.current_bins) + 1 < self.min_bins:
            self.current_bins.append(item)
            self._backtrack(item_idx + 1)
            self.current_bins.pop()

def calculate_skewness(data):
    if len(data) < 3: return 0.0
    mean = statistics.mean(data)
    std = statistics.stdev(data)
    if std == 0: return 0.0
    return sum((x - mean)**3 for x in data) / (len(data) * std**3)

def check_triplet(it, p1, p2, p3):
    # p is parity: 0 for even, 1 for odd
    for i in range(len(it) - 2):
        if (it[i] % 2 == p1) and (it[i+1] % 2 == p2) and (it[i+2] % 2 == p3):
            return 1
    return 0

def run_analysis():
    n_instances = 4096
    capacity = 100
    results = []

    print(f"Generating and solving {n_instances} instances...")
    
    random.seed(42)
    for i in range(n_instances):
        n_items = random.randint(10, 15)
        # Random items, but some focus on parity distributions
        items = [random.randint(10, 70) for _ in range(n_items)]
        
        start_time = time.time()
        solver = BinPackingSolver(items, capacity)
        opt_bins = solver.solve()
        solve_time = time.time() - start_time
        
        total_weight = sum(items)
        n_even = sum(1 for x in items if x % 2 == 0)
        n_odd = n_items - n_even
        even_ratio = n_even / n_items
        
        # Parity Patterns in sorted order (since solver uses sorted)
        sorted_items = sorted(items, reverse=True)
        eoe = check_triplet(sorted_items, 0, 1, 0)
        oeo = check_triplet(sorted_items, 1, 0, 1)
        eee = check_triplet(sorted_items, 0, 0, 0)
        ooo = check_triplet(sorted_items, 1, 1, 1)
        
        waste = (opt_bins * capacity) - total_weight
        waste_pct = (waste / (opt_bins * capacity)) * 100 if opt_bins > 0 else 0
        
        results.append({
            "id": i,
            "n_items": n_items,
            "total_weight": total_weight,
            "n_even": n_even,
            "n_odd": n_odd,
            "even_ratio": even_ratio,
            "pattern_eoe": eoe,
            "pattern_oeo": oeo,
            "pattern_eee": eee,
            "pattern_ooo": ooo,
            "opt_bins": opt_bins,
            "waste_pct": waste_pct,
            "solve_time_ms": solve_time * 1000
        })
        
        if (i + 1) % 500 == 0:
            print(f"Solved {i+1}/{n_instances}...")

    # Write to CSV
    keys = results[0].keys()
    with open("bin_packing_stats_4096.csv", "w", newline='') as f:
        dict_writer = csv.DictWriter(f, keys)
        dict_writer.writeheader()
        dict_writer.writerows(results)
    
    # Correlation Analysis
    def correlation(x_key, y_key):
        x = [r[x_key] for r in results]
        y = [r[y_key] for r in results]
        mean_x = statistics.mean(x)
        mean_y = statistics.mean(y)
        num = sum((xi - mean_x) * (yi - mean_y) for xi, yi in zip(x, y))
        den = math.sqrt(sum((xi - mean_x)**2 for xi in x) * sum((yi - mean_y)**2 for yi in y))
        return num / den if den != 0 else 0

    print("\n--- Parity Correlation Analysis (Target: opt_bins) ---")
    metrics = ["n_items", "total_weight", "even_ratio", "pattern_eoe", "pattern_oeo", "pattern_eee", "pattern_ooo"]
    corrs = {m: correlation(m, "opt_bins") for m in metrics}
    for m, c in sorted(corrs.items(), key=lambda x: abs(x[1]), reverse=True):
        print(f"{m:15}: {c:.4f}")

    # Document findings
    with open("bin_packing_parity_patterns.md", "w") as f:
        f.write("# Bin Packing Parity Study (N=4096)\n\n")
        f.write("Analyzed 4096 instances to detect structural correlations between item parity (Even/Odd) and packing optimality.\n\n")
        f.write("## Correlations with Optimal Bin Count\n\n")
        f.write("| Metric | Correlation |\n")
        f.write("| :--- | :--- |\n")
        for m, c in sorted(corrs.items(), key=lambda x: abs(x[1]), reverse=True):
            f.write(f"| {m} | {c:.4f} |\n")
        f.write("\n## Parity Pattern Insights\n\n")
        f.write(f"- **EOE/OEO Impact**: {corrs['pattern_eoe']:.4f} / {corrs['pattern_oeo']:.4f}. Alternating parity sequences show a minor impact on bin count compared to raw weight.\n")
        f.write(f"- **Even Ratio**: {corrs['even_ratio']:.4f}. The proportion of even items has a negligible impact on the total bin count, suggesting that capacity, not parity, is the dominant hard constraint.\n")
        avg_waste = statistics.mean([r["waste_pct"] for r in results])
        f.write(f"- **Avg Waste**: {avg_waste:.2f}%\n")

if __name__ == "__main__":
    run_analysis()
