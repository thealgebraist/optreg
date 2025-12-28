import csv
import numpy as np
import collections

def load_instances(filepath, k='instance_id'):
    instances = collections.defaultdict(list)
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            instances[row[k]].append({
                'id': int(row['city_id']),
                'x': float(row['x']),
                'y': float(row['y'])
            })
    return instances

def load_solutions(filepath, k='instance_id'):
    solutions = collections.defaultdict(list)
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            solutions[row[k]].append(int(row['city_id']))
    return solutions

def analyze_high_confidence():
    print("Analyzing 2048 high-confidence instances (n <= 12)...")
    instances = load_instances('optreg/build/tsp_instances_expanded.csv')
    solutions = load_solutions('optreg/build/tsp_solutions_expanded.csv')
    
    edge_correlations = []
    selection_factors = []
    
    for inst_id, coords in instances.items():
        if inst_id not in solutions: continue
        
        tour = solutions[inst_id]
        n = len(coords)
        pts = {p['id']: (p['x'], p['y']) for p in coords}
        
        # All possible edges
        all_edges = []
        for v1_id in range(n):
            for v2_id in range(v1_id + 1, n):
                d = np.sqrt((pts[v1_id][0] - pts[v2_id][0])**2 + (pts[v1_id][1] - pts[v2_id][1])**2)
                all_edges.append((v1_id, v2_id, d))
                
        # Optimal edges
        opt_edges = set()
        for i in range(n):
            u, v = tour[i], tour[(i+1)%n]
            opt_edges.add(tuple(sorted((u, v))))
            
        avg_all = np.mean([e[2] for e in all_edges])
        avg_opt = np.mean([e[2] for e in all_edges if tuple(sorted((e[0], e[1]))) in opt_edges])
        selection_factors.append(avg_opt / avg_all)
        
        # Correlation: edge length vs "is in optimal"
        lengths = [e[2] for e in all_edges]
        is_opt = [1 if tuple(sorted((e[0], e[1]))) in opt_edges else 0 for e in all_edges]
        edge_correlations.append(np.corrcoef(lengths, is_opt)[0, 1])

    print(f"Average Selection Factor (High Confidence): {np.mean(selection_factors):.4f}")
    print(f"Average Edge Length Correlation (High Confidence): {np.mean(edge_correlations):.4f}")

if __name__ == "__main__":
    analyze_high_confidence()
