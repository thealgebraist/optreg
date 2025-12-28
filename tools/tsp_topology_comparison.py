import csv
import numpy as np
import collections

def load_instances(filepath):
    instances = collections.defaultdict(list)
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            instances[row['instance_id']].append({
                'id': int(row['city_id']),
                'x': float(row['x']),
                'y': float(row['y'])
            })
    return instances

def load_solutions(filepath):
    solutions = collections.defaultdict(list)
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            solutions[row['instance_id']].append(int(row['city_id']))
    return solutions

def get_turn(p1, p2, p3):
    """Returns 'L' for left, 'R' for right."""
    ux, uy = p2[0] - p1[0], p2[1] - p1[1]
    vx, vy = p3[0] - p2[0], p3[1] - p2[1]
    cp = ux * vy - uy * vx
    return 'L' if cp > 0 else 'R'

def get_angle(p1, p2, p3):
    ux, uy = p1[0] - p2[0], p1[1] - p2[1]
    vx, vy = p3[0] - p2[0], p3[1] - p2[1]
    dot = ux * vx + uy * vy
    mag_u = np.sqrt(ux**2 + uy**2)
    mag_v = np.sqrt(vx**2 + vy**2)
    if mag_u < 1e-9 or mag_v < 1e-9: return 180.0
    cos_theta = np.clip(dot / (mag_u * mag_v), -1.0, 1.0)
    return np.degrees(np.arccos(cos_theta))

def analyze_topology():
    print("Loading data for comparative analysis...")
    instances = load_instances('optreg/build/tsp_comp_instances.csv')
    opt_solutions = load_solutions('optreg/build/tsp_comp_solutions_opt.csv')
    boltz_solutions = load_solutions('optreg/build/tsp_comp_solutions_boltz.csv')

    stats = {
        'opt': {'turns': [], 'angles': [], 'lengths': [], 'patterns': collections.Counter()},
        'boltz': {'turns': [], 'angles': [], 'lengths': [], 'patterns': collections.Counter()}
    }

    for inst_id, coords_list in instances.items():
        if inst_id not in opt_solutions or inst_id not in boltz_solutions: continue
        
        pts = {p['id']: (p['x'], p['y']) for p in coords_list}
        
        for key in ['opt', 'boltz']:
            tour = opt_solutions[inst_id] if key == 'opt' else boltz_solutions[inst_id]
            n = len(tour)
            if n < 3: continue
            
            # 1. Turn Directions and Patterns
            turns = []
            for i in range(n):
                p1 = pts[tour[(i-1)%n]]
                p2 = pts[tour[i]]
                p3 = pts[tour[(i+1)%n]]
                turns.append(get_turn(p1, p2, p3))
                stats[key]['angles'].append(get_angle(p1, p2, p3))
                
                # Length
                d = np.sqrt((p2[0]-p3[0])**2 + (p2[1]-p3[1])**2)
                stats[key]['lengths'].append(d)

            # 2. Extract triplets (patterns)
            for i in range(n):
                pattern = "".join([turns[(i+j)%n] for j in range(3)])
                stats[key]['patterns'][pattern] += 1

    # Print Results
    print("\n=== Turn Pattern Frequency (Triplets) ===")
    print(f"{'Pattern':10} | {'Optimal %':12} | {'Boltzmann %':12} | {'Diff':8}")
    print("-" * 55)
    
    all_patterns = sorted(set(stats['opt']['patterns'].keys()) | set(stats['boltz']['patterns'].keys()))
    opt_total = sum(stats['opt']['patterns'].values())
    boltz_total = sum(stats['boltz']['patterns'].values())

    for p in all_patterns:
        o_freq = stats['opt']['patterns'][p] / opt_total * 100
        b_freq = stats['boltz']['patterns'][p] / boltz_total * 100
        diff = b_freq - o_freq
        print(f"{p:10} | {o_freq:11.2f}% | {b_freq:11.2f}% | {diff:+.2f}%")

    print("\n=== Geometric Distributions ===")
    print(f"{'Metric':20} | {'Optimal':12} | {'Boltzmann':12}")
    print("-" * 50)
    print(f"{'Mean Turn Angle':20} | {np.mean(stats['opt']['angles']):11.2f}° | {np.mean(stats['boltz']['angles']):11.2f}°")
    print(f"{'Median Turn Angle':20} | {np.median(stats['opt']['angles']):11.2f}° | {np.median(stats['boltz']['angles']):11.2f}°")
    print(f"{'Mean Edge Length':20} | {np.mean(stats['opt']['lengths']):11.2f}  | {np.mean(stats['boltz']['lengths']):11.2f}")
    
    # Net Rotation (Chirality)
    # L = +1, R = -1. Average per instance.
    # We can just sum L vs R globally as well.
    opt_l = sum(1 for a in all_patterns if a.startswith('L')) # This is wrong, patterns overlap.
    # Let's count globally
    opt_l_count = stats['opt']['patterns']['LLL'] + stats['opt']['patterns']['LLR'] + stats['opt']['patterns']['LRL'] + stats['opt']['patterns']['LRR']
    # Better: just use the raw turn list if we saved it. We didn't save global turn list correctly.
    # Let's recalibrate.
    
    l_opt = sum(v for k, v in stats['opt']['patterns'].items() if k[0] == 'L')
    r_opt = sum(v for k, v in stats['opt']['patterns'].items() if k[0] == 'R')
    l_boltz = sum(v for k, v in stats['boltz']['patterns'].items() if k[0] == 'L')
    r_boltz = sum(v for k, v in stats['boltz']['patterns'].items() if k[0] == 'R')
    
    print(f"{'Left Turn Bias':20} | {l_opt/(l_opt+r_opt)*100:11.2f}% | {l_boltz/(l_boltz+r_boltz)*100:11.2f}%")

if __name__ == "__main__":
    analyze_topology()
