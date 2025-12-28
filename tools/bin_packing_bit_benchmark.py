import csv
import time
import math
import random
import statistics

# ==============================================================================
# Exact Solver (Reused for baseline)
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
        # Quick FFD check
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
# Bit-Set Heuristic: Iterative Bin Maximization
# ==============================================================================

class HeuristicBitMaximizer:
    """
    Greedy strategy that constructs bins one by one.
    For each new bin:
    1. Seed it with the largest available item.
    2. Solve the Subset Sum problem (via bitmask search) to fill the remaining capacity 
       as fully as possible using available items.
    
    This minimizes the variance of empty space (by forcing it to 0 per bin locally).
    """
    def __init__(self, items, capacity):
        # We need original indices for bitmasking, but sorting helps the seed strategy
        self.items = sorted(items, reverse=True)
        self.capacity = capacity
        self.n = len(items)
        
    def solve(self):
        remaining_mask = (1 << self.n) - 1
        bins_count = 0
        
        while remaining_mask > 0:
            bins_count += 1
            current_bin_load = 0
            
            # 1. Find largest available item (Seed)
            seed_idx = -1
            for i in range(self.n):
                if (remaining_mask >> i) & 1:
                    seed_idx = i
                    break # Items are sorted desc, so first found is largest
            
            # Start bin with seed
            current_bin_load = self.items[seed_idx]
            remaining_mask &= ~(1 << seed_idx)
            
            target = self.capacity - current_bin_load
            if target == 0: continue
            
            # 2. Find best subset to fill the rest
            # We want subset S of remaining_mask such that sum(S) <= target is MAXIMIZED
            best_subset_mask = 0
            best_subset_sum = 0
            
            # Helper for subset sum branch & bound / search
            # Since n < 16, this inner search is very small (max depth 15)
            # We pass a 'limit_mask' of items we can consider
            best_subset_mask, best_subset_sum = self._find_max_subset(remaining_mask, target)
            
            # Commit the best subset
            remaining_mask &= ~best_subset_mask
            
        return bins_count

    def _find_max_subset(self, mask, capacity_limit):
        # Iterative or Recursive DFS to find best subset sum
        # Returns (subset_mask, subset_sum)
        
        # Optimization: Filter candidates first
        candidates = []
        for i in range(self.n):
            if ((mask >> i) & 1) and (self.items[i] <= capacity_limit):
                candidates.append(i)
        
        best_sum = 0
        best_mask = 0
        
        # Stack: (index_in_candidates, current_sum, current_mask)
        stack = [(0, 0, 0)]
        
        while stack:
            idx, c_sum, c_mask = stack.pop()
            
            if c_sum > best_sum:
                best_sum = c_sum
                best_mask = c_mask
            
            if best_sum == capacity_limit:
                return best_mask, best_sum
            
            if idx >= len(candidates):
                continue
                
            item_idx = candidates[idx]
            w = self.items[item_idx]
            
            # Pruning: If even adding all remaining candidates can't beat best_sum? 
            # (Simple upper bound: current_sum + sum(remaining items))
            # Too costly to compute sum every time? Maybe. Let's stick to simple capacity check.
            
            # Branch 1: Include item (if fits)
            if c_sum + w <= capacity_limit:
                stack.append((idx + 1, c_sum + w, c_mask | (1 << item_idx)))
                
            # Branch 2: Exclude item
            # Only define exclusion branch if we theoretically could do better
            # Simple heuristic: Always traverse
            stack.append((idx + 1, c_sum, c_mask))
            
        return best_mask, best_sum

# ==============================================================================
# Standard FFD for Baseline Comparison
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
# Benchmarking
# ==============================================================================

def run_benchmark():
    n_instances = 4096
    capacity = 100
    
    # Store results
    gap_bit = 0.0
    gap_ffd = 0.0
    exact_match_bit = 0
    exact_match_ffd = 0
    t_bit = 0
    t_opt = 0
    
    print(f"Benchmarking Bit-Heuristic vs Optimal (N={n_instances}, n < 16)...")
    
    random.seed(42)
    
    for i in range(n_instances):
        n_items = random.randint(10, 15)
        items = [random.randint(10, 70) for _ in range(n_items)]
        
        # 1. Optimal
        t0 = time.time()
        opt_solver = BinPackingSolverOptimized(items, capacity)
        opt_bins = opt_solver.solve()
        t_opt += (time.time() - t0)
        
        # 2. Bit Heuristic
        t1 = time.time()
        bit_solver = HeuristicBitMaximizer(items, capacity)
        bit_bins = bit_solver.solve()
        t_bit += (time.time() - t1)
        
        # 3. FFD Heuristic
        ffd_bins = solve_ffd(items, capacity)
        
        if bit_bins == opt_bins: exact_match_bit += 1
        if ffd_bins == opt_bins: exact_match_ffd += 1
        gap_bit += (bit_bins - opt_bins)
        gap_ffd += (ffd_bins - opt_bins)
        
        if (i+1) % 500 == 0:
            print(f"Processed {i+1}...")

    # Report
    print("\n--- Benchmark Results ---")
    print(f"Instances: {n_instances}")
    print(f"Efficiency (Bit vs Opt): {(t_bit/t_opt)*100:.2f}% time")
    print(f"\nAccuracy (Bit-Set Heuristic):")
    print(f"  Exact Matches: {exact_match_bit}/{n_instances} ({exact_match_bit/n_instances*100:.2f}%)")
    print(f"  Avg Excess Bins: {gap_bit/n_instances:.4f}")
    
    print(f"\nAccuracy (Standard FFD):")
    print(f"  Exact Matches: {exact_match_ffd}/{n_instances} ({exact_match_ffd/n_instances*100:.2f}%)")
    print(f"  Avg Excess Bins: {gap_ffd/n_instances:.4f}")

    with open("bin_packing_bit_results.md", "w") as f:
        f.write("# Bin Packing Bit-Set Heuristic Evaluation\n\n")
        f.write(f"Analyzed **{n_instances}** instances ($n<16$).\n\n")
        f.write("## Performance\n")
        f.write(f"- **Bit-Set Strategy**: \"Iterative Bin Maximization\" (fill one bin perfectly, then repeat).\n")
        f.write(f"- **Exact Match Rate**: **{exact_match_bit/n_instances*100:.2f}%**\n")
        f.write(f"- **Avg Gap**: {gap_bit/n_instances:.4f} bins\n\n")
        f.write("## Comparison to FFD\n")
        f.write(f"- **FFD Exact Match**: {exact_match_ffd/n_instances*100:.2f}%\n")
        f.write(f"- **FFD Avg Gap**: {gap_ffd/n_instances:.4f} bins\n\n")
        f.write("## Conclusion\n")
        if exact_match_bit > exact_match_ffd:
            f.write("The Bit-Set Maximizer **outperforms** standard FFD. Minimizing local bin variance is effective.\n")
        else:
            f.write("The Bit-Set Maximizer **underperforms** or matches FFD. Global flexible placement (FFD) beats local greedy maximization for these small sizes.\n")

if __name__ == "__main__":
    run_benchmark()
