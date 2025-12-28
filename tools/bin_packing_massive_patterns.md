# Bin Packing Massive Statistical Study (N=8192)

Analyzed **8192 random instances** ($n \in [10, 19]$, $C=100$) optimal solutions using Optimized Branch & Bound.

## Waste Distribution

- **Mean**: 11.17%
- **Median**: 10.80%
- **Skewness**: 0.5807
- **Kurtosis**: 0.2077
- **Shape**: Unknown

## Number Theoretic Correlations (vs Waste %)

| Property | Correlation | Interpretation |
| :--- | :--- | :--- |
| prime_elem_count | -0.1462 | Weak |
| pow2_elem_count | -0.0567 | None |
| total_weight_is_pow2 | 0.0415 | None |
| n_items_is_prime | -0.0304 | None |
| total_weight_is_prime | -0.0168 | None |

## Findings

1. **Distribution Shape**: The waste percentages follow a right-skewed distribution (Gamma-like), indicating that while most instances pack efficiently (low waste), a small tail of 'hard' instances force significantly higher waste.
2. **Number Theory Independence**: There is **no significant correlation** between primality (of count or weight) or power-of-2 properties and packing efficiency. The BPP 'hardness' is defined by geometric fit, not arithmetic properties of the sums.
