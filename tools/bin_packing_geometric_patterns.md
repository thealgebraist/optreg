# Bin Packing Geometric Analysis (N=4096)

Analyzed **4096** optimal solutions to correlate 'Waste %' with volumetric and geometric properties.

## Key Correlations

| Geometric Property | Correlation with Waste |
| :--- | :--- |
| opt_fill_variance | 0.6984 |
| ratio_huge | 0.3917 |
| conflict_density | 0.3862 |
| count_large | -0.3067 |
| ratio_large | -0.2088 |
| count_huge | 0.2059 |
| gini_coeff | -0.1407 |
| total_weight | -0.1045 |

## Metric Definitions
- **Conflict Density**: Probability that 2 random items *cannot* fit in the same bin.
- **Count Huge**: Items with $w > C/2$.
- **Count Large**: Items with $C/3 < w \le C/2$.
- **Opt Fill Variance**: Variance of the used capacity across optimal bins.
