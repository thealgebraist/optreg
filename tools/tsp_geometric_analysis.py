import csv
import numpy as np
import collections

def load_csv(filepath):
    data = []
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            data.append({k: float(v) for k, v in row.items()})
    return data

def analyze_geometric_study():
    print("Analyzing TSP Geometric Study Results...")
    
    base_features = load_csv('optreg/build/tsp_base_geometric.csv')
    removal_results = load_csv('optreg/build/tsp_removal_results.csv')
    
    # 1. Correlation: Angle at node vs Tour Stability after removal
    # Group base features by inst/node
    features_map = {}
    for f in base_features:
        features_map[(int(f['instance_id']), int(f['node_id']))] = f['angle']
    
    angles = []
    ious = []
    for res in removal_results:
        key = (int(res['instance_id']), int(res['removed_node_id']))
        if key in features_map:
            angles.append(features_map[key])
            ious.append(res['edge_iou'])
            
    if angles:
        corr = np.corrcoef(angles, ious)[0, 1]
        print(f"Correlation (Angle at Node vs Edge IoU after removal): {corr:.4f}")
        
        # Split by sharp vs blunt angles
        sharp = [ious[i] for i in range(len(angles)) if angles[i] < 90]
        blunt = [ious[i] for i in range(len(angles)) if angles[i] >= 90]
        
        if sharp: print(f"Avg IoU for sharp angles (<90): {np.mean(sharp):.4f}")
        if blunt: print(f"Avg IoU for blunt angles (>=90): {np.mean(blunt):.4f}")

    # 2. Geometric Patterns: Angle Distribution
    all_angles = [f['angle'] for f in base_features]
    print(f"\nOptimal Tour Angle Stats:")
    print(f"  Mean Angle: {np.mean(all_angles):.2f}°")
    print(f"  Median Angle: {np.median(all_angles):.2f}°")
    print(f"  Std Dev: {np.std(all_angles):.2f}°")
    
    # 3. Simple Geometric Pruning Rules?
    # Connected nodes vs Non-connected nodes (Randomly sampled from base_features instances)
    # We can't easily get non-connected pairs without the original instances, 
    # but we can look at the distribution of optimal edge lengths vs global average.
    
    # Let's check for "Angle Smoothness"
    # Correlation between angle at node i and average angle at its tour neighbors
    # Create tour adjacency
    adj = collections.defaultdict(list)
    for f in base_features:
        adj[int(f['instance_id'])].append(f)
        
    smoothness_corrs = []
    for inst_id, nodes in adj.items():
        if len(nodes) < 4: continue
        # Sort by tour order? The base_features list is already in tour order per instance
        inst_angles = [n['angle'] for n in nodes]
        n_inst = len(inst_angles)
        neighbor_avg_angles = []
        for i in range(n_inst):
            avg = (inst_angles[(i - 1) % n_inst] + inst_angles[(i + 1) % n_inst]) / 2.0
            neighbor_avg_angles.append(avg)
        smoothness_corrs.append(np.corrcoef(inst_angles, neighbor_avg_angles)[0, 1])
        
    print(f"\nAverage Angle Smoothness (Correlation i vs neighbors): {np.mean(smoothness_corrs):.4f}")

if __name__ == "__main__":
    analyze_geometric_study()
