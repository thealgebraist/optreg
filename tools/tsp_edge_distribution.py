import csv
import numpy as np
import collections
import scipy.optimize
# Removed matplotlib as it is not available in the environment

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

def model_boltzmann(L, A, beta):
    return A * np.exp(-beta * L)

def fit_distribution():
    print("Loading 2048 instances for distribution modeling...")
    instances = load_instances('optreg/build/tsp_instances_expanded.csv')
    solutions = load_solutions('optreg/build/tsp_solutions_expanded.csv')
    
    all_lengths = []
    opt_lengths = []
    
    # Collect all edges and normalized lengths
    for inst_id, coords in instances.items():
        if inst_id not in solutions: continue
        
        tour = solutions[inst_id]
        n = len(coords)
        pts = {p['id']: (p['x'], p['y']) for p in coords}
        
        inst_all_edges = []
        for v1_id in range(n):
            for v2_id in range(v1_id + 1, n):
                d = np.sqrt((pts[v1_id][0] - pts[v2_id][0])**2 + (pts[v1_id][1] - pts[v2_id][1])**2)
                inst_all_edges.append((v1_id, v2_id, d))
        
        avg_d = np.mean([e[2] for e in inst_all_edges])
        
        opt_edges = set()
        for i in range(n):
            u, v = tour[i], tour[(i+1)%n]
            opt_edges.add(tuple(sorted((u, v))))
            
        for u, v, d in inst_all_edges:
            norm_d = d / avg_d
            all_lengths.append(norm_d)
            if tuple(sorted((u, v))) in opt_edges:
                opt_lengths.append(norm_d)
    
    # Binning
    bins = np.linspace(0, 3, 31)
    counts_all, _ = np.histogram(all_lengths, bins=bins)
    counts_opt, _ = np.histogram(opt_lengths, bins=bins)
    
    bin_centers = (bins[:-1] + bins[1:]) / 2
    
    # Probability (masking zero counts to avoid division by zero)
    mask = counts_all > 10 # Require at least 10 edges in a bin for statistical significance
    prob = np.zeros_like(bin_centers)
    prob[mask] = counts_opt[mask] / counts_all[mask]
    
    # Only fit on valid bins
    x_data = bin_centers[mask]
    y_data = prob[mask]
    
    # Fit Boltzmann-like distribution: P(L) = A * exp(-beta * L)
    popt, pcov = scipy.optimize.curve_fit(model_boltzmann, x_data, y_data, p0=[0.8, 2.0])
    A_fit, beta_fit = popt
    
    print(f"\nModel: P(L_norm) = {A_fit:.4f} * exp(-{beta_fit:.4f} * L_norm)")
    
    # Calculate R-squared
    residuals = y_data - model_boltzmann(x_data, *popt)
    ss_res = np.sum(residuals**2)
    ss_tot = np.sum((y_data - np.mean(y_data))**2)
    r_squared = 1 - (ss_res / ss_tot)
    print(f"R-squared: {r_squared:.4f}")
    
    # Print some data points
    print("\nBin Centers | Empirical Prob | Fitted Prob")
    print("-" * 40)
    for x, y_emp in zip(x_data, y_data):
        y_fit = model_boltzmann(x, *popt)
        print(f"{x:11.2f} | {y_emp:14.4f} | {y_fit:11.4f}")

if __name__ == "__main__":
    fit_distribution()
