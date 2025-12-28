import csv
import math

def mean(data):
    if not data: return 0
    return sum(data) / len(data)

def std_dev(data):
    if len(data) < 2: return 0
    m = mean(data)
    variance = sum((x - m) ** 2 for x in data) / (len(data) - 1)
    return math.sqrt(variance)

def correlation(x, y):
    if len(x) != len(y) or len(x) < 2: return 0
    mx, my = mean(x), mean(y)
    sx, sy = std_dev(x), std_dev(y)
    if sx == 0 or sy == 0: return 0
    
    cov = sum((xi - mx) * (yi - my) for xi, yi in zip(x, y)) / (len(x) - 1)
    return cov / (sx * sy)

def covariance(x, y):
    if len(x) != len(y) or len(x) < 2: return 0
    mx, my = mean(x), mean(y)
    cov = sum((xi - mx) * (yi - my) for xi, yi in zip(x, y)) / (len(x) - 1)
    return cov

def analyze():
    print("Loading fft_analysis.csv...")
    try:
        with open("fft_analysis.csv", "r") as f:
            reader = csv.DictReader(f)
            rows = list(reader)
    except FileNotFoundError:
        print("File not found.")
        return

    tsp_rows = [r for r in rows if r['problem'] == 'TSP']
    col_rows = [r for r in rows if r['problem'] == 'Coloring']
    
    print(f"\nTotal Samples: {len(tsp_rows)} TSP, {len(col_rows)} Coloring")
    
    # 1. TSP Analysis
    if tsp_rows:
        print("\n--- TSP Optimal FFT Analysis (Harmonics 1 and 3) ---")
        cost = [float(r['cost']) for r in tsp_rows]
        c1 = [float(r['fft_c1']) for r in tsp_rows]
        c3 = [float(r['fft_c3']) for r in tsp_rows]
        
        # Additional features for completeness
        c2 = [float(r['fft_c2']) for r in tsp_rows]
        c4 = [float(r['fft_c4']) for r in tsp_rows]
        
        print(f"Cost Mean: {mean(cost):.2f}, Std: {std_dev(cost):.2f}")
        print("-" * 40)
        print(f"|C1| (Fundamental):")
        print(f"  Mean: {mean(c1):.4f}, Std: {std_dev(c1):.4f}")
        print(f"  Covariance(Cost, |C1|): {covariance(cost, c1):.4f}")
        print(f"  Correlation(Cost, |C1|): {correlation(cost, c1):.4f}")
        
        print("-" * 40)
        print(f"|C3| (Triangularity):")
        print(f"  Mean: {mean(c3):.4f}, Std: {std_dev(c3):.4f}")
        print(f"  Covariance(Cost, |C3|): {covariance(cost, c3):.4f}")
        print(f"  Correlation(Cost, |C3|): {correlation(cost, c3):.4f}")
        
        print("-" * 40)
        print(f"Other Correlations:")
        print(f"  Corr(Cost, |C2|): {correlation(cost, c2):.4f}")
        print(f"  Corr(Cost, |C4|): {correlation(cost, c4):.4f}")


if __name__ == "__main__":
    analyze()
