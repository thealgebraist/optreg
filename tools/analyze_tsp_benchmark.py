import csv
import collections
import numpy as np

def analyze_scale_benchmark():
    print("Analyzing TSP Scale Benchmark (1024 instances, n < 32)...")
    
    data = collections.defaultdict(lambda: collections.defaultdict(list))
    # data[n][solver] = [(obj, time), ...]
    
    with open('optreg/build/tsp_scale_benchmark.csv', 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            n = int(row['n'])
            solver = row['solver']
            obj = float(row['obj'])
            time = float(row['time_ms'])
            data[n][solver].append((obj, time))

    # For each n, find the best objective among heuristics to use as baseline
    # (Since we don't have optimal for all n < 32 in this fast benchmark)
    
    solvers = sorted(list(next(iter(data.values())).keys()))
    print(f"\n{'n':<4} | {'Solver':<20} | {'Avg Accuracy':<12} | {'Avg Time (ms)':<15}")
    print("-" * 60)

    for n in sorted(data.keys()):
        # Find best objective for this instance
        # Since we have multiple instances for the same n, we need to handle them individually
        # But for simplification in this report, let's group by n
        
        # Accurate way: regroup by instance
        instances = collections.defaultdict(list)
        with open('optreg/build/tsp_scale_benchmark.csv', 'r') as f:
            f.seek(0)
            reader = csv.DictReader(f)
            for row in reader:
                if int(row['n']) == n:
                    instances[row['instance']].append((row['solver'], float(row['obj']), float(row['time_ms'])))
        
        solver_stats = collections.defaultdict(lambda: {'acc': [], 'time': []})
        
        for inst_id, results in instances.items():
            best_obj = min(r[1] for r in results)
            for s, obj, t in results:
                accuracy = best_obj / obj if obj > 0 else 0
                solver_stats[s]['acc'].append(accuracy)
                solver_stats[s]['time'].append(t)
        
        for s in solvers:
            avg_acc = np.mean(solver_stats[s]['acc'])
            avg_time = np.mean(solver_stats[s]['time'])
            print(f"{n:<4} | {s:<20} | {avg_acc:.4f}       | {avg_time:.4f}")
        print("-" * 60)

    # Global summary
    print("\nGlobal Performance Summary:")
    global_stats = collections.defaultdict(lambda: {'acc': [], 'time': []})
    
    instances = collections.defaultdict(list)
    with open('optreg/build/tsp_scale_benchmark.csv', 'r') as f:
        f.seek(0)
        reader = csv.DictReader(f)
        for row in reader:
            instances[row['instance']].append((row['solver'], float(row['obj']), float(row['time_ms'])))
            
    for inst_id, results in instances.items():
        best_obj = min(r[1] for r in results)
        for s, obj, t in results:
            accuracy = best_obj / obj if obj > 0 else 0
            global_stats[s]['acc'].append(accuracy)
            global_stats[s]['time'].append(t)

    for s in solvers:
        print(f"{s:<20} | Avg Accuracy: {np.mean(global_stats[s]['acc']):.4f} | Avg Time: {np.mean(global_stats[s]['time']):.4f}ms")

if __name__ == "__main__":
    analyze_scale_benchmark()
