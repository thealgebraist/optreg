import csv
import numpy as np
import math
from scipy.stats import pearsonr
import os

def solve_analysis():
    print("Loading exhaustive 4x4 data...")
    instances = []
    with open("optreg/build/exhaustive_tsp_4x4.csv", "r") as f:
        reader = csv.DictReader(f)
        for row in reader:
            instances.append({
                "nodes": [int(row["n1"]), int(row["n2"]), int(row["n3"]), int(row["n4"])],
                "opt_dist": float(row["opt_dist"]),
                "opt_edges": row["opt_edges"].split(";")
            })

    # 1. Map edges (u,v) to 0..119
    edge_map = {}
    idx = 0
    for u in range(16):
        for v in range(u + 1, 16):
            edge_map[(u, v)] = idx
            idx += 1
    
    # Precompute edge lengths and node positions
    grid = []
    for y in range(4):
        for x in range(4):
            grid.append((x, y))
    
    edge_lengths = {}
    for (u, v), k in edge_map.items():
        d = math.sqrt((grid[u][0]-grid[v][0])**2 + (grid[u][1]-grid[v][1])**2)
        edge_lengths[k] = d

    # 2. Build Adjacency Participation Matrix
    # Matrix of (1820 instances) x (120 edges)
    data = np.zeros((len(instances), 120), dtype=int)
    for i, inst in enumerate(instances):
        for edge_str in inst["opt_edges"]:
            try:
                u, v = sorted([int(x) for x in edge_str.split("-")])
                k = edge_map[(u, v)]
                data[i, k] = 1
            except:
                pass

    # 3. Covariance Analysis
    print("Computing 120x120 edge covariance matrix...")
    cov_matrix = np.cov(data, rowvar=False)
    # Save the covariance matrix to CSV
    np.savetxt("optreg/build/exhaustive_edge_covariance.csv", cov_matrix, delimiter=",")
    
    # Correlation matrix for summary
    cor_matrix = np.corrcoef(data, rowvar=False)
    cor_matrix = np.nan_to_num(cor_matrix)
    
    top_cors = []
    for i in range(120):
        for j in range(i + 1, 120):
            if abs(cor_matrix[i, j]) > 0.1: # Lowered threshold for sparse data
                top_cors.append((i, j, cor_matrix[i, j]))
    
    top_cors.sort(key=lambda x: -abs(x[2]))

    # 4. Correlation Tests: Edges vs Nodes
    # Define "Node Centrality" as distance from grid center (1.5, 1.5)
    node_centrality = []
    for x, y in grid:
        node_centrality.append(math.sqrt((x-1.5)**2 + (y-1.5)**2))
    
    # Participation rate for each edge
    participation_rate = np.mean(data, axis=0)
    
    # Correlation between edge length and participation
    edge_len_arr = np.array([edge_lengths[k] for k in range(120)])
    corr_len, _ = pearsonr(edge_len_arr, participation_rate)
    
    # Correlation between edge degree (average of node degrees in instances where they participate)
    # A bit redundant for 4x4, but let's fulfill the request.
    # We'll calculate the total global degree (participation sum) for each node.
    node_participation = np.zeros(16)
    for k in range(120):
        u, v = {v_idx: k_idx for k_idx, v_idx in edge_map.items()}[k]
        node_participation[u] += participation_rate[k]
        node_participation[v] += participation_rate[k]

    # 5. Boltzmann Constant Estimation
    length_bins = {}
    for k in range(120):
        l = round(edge_lengths[k], 4)
        if l not in length_bins:
            length_bins[l] = {"total_possible": 0, "total_opt": 0}
        length_bins[l]["total_possible"] += 91 # binom(14,2)
        length_bins[l]["total_opt"] += np.sum(data[:, k])
    
    L_vals = []
    log_P_vals = []
    for l, stats in sorted(length_bins.items()):
        if stats["total_opt"] > 0:
            p = stats["total_opt"] / stats["total_possible"]
            L_vals.append(l)
            log_P_vals.append(math.log(p))
    
    beta = 0
    if len(L_vals) > 1:
        slope, intercept = np.polyfit(L_vals, log_P_vals, 1)
        beta = -slope

    # Results Summary
    print("\n=== Exhaustive Study Summary ===")
    print(f"Total Instances: {len(instances)}")
    print(f"Total Edges Possible: 120")
    print(f"Avg Participation Rate: {np.mean(participation_rate):.4f}")
    print(f"Correlation (Edge Optimality vs Edge Length): {corr_len:.4f}")
    if top_cors:
        print(f"Top Edge pair Correlation: {top_cors[0][2]:.4f}")
    print(f"Discrete Boltzmann Constant beta: {beta:.4f}")
    
    # Save Boltzmann Stats to file
    with open("optreg/build/exhaustive_boltzmann_stats.csv", "w") as f:
        f.write("length,log_prob\n")
        for l, lp in zip(L_vals, log_P_vals):
            f.write(f"{l},{lp}\n")

if __name__ == "__main__":
    solve_analysis()
