# Bin Packing Statistical Patterns

Analyzed 512 random instances (N=10-15, Cap=100).

## Correlations with Optimal Bins

| Metric | Correlation |
| :--- | :--- |
| n_items | 0.6303 |
| total_weight | 0.9329 |
| avg_size | 0.7106 |
| skew_size | -0.5652 |

## Key Findings

- Average Waste: 12.81%
- Finding: Total weight is the strongest predictor of bin count, followed by item count.
- Finding: Skewness has a minor inverse impact on bin efficiency.
