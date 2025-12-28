# Bin Packing Parity Study (N=4096)

Analyzed 4096 instances to detect structural correlations between item parity (Even/Odd) and packing optimality.

## Correlations with Optimal Bin Count

| Metric | Correlation |
| :--- | :--- |
| total_weight | 0.9313 |
| n_items | 0.6170 |
| pattern_eoe | 0.0903 |
| pattern_oeo | 0.0852 |
| pattern_ooo | 0.0543 |
| pattern_eee | 0.0519 |
| even_ratio | 0.0020 |

## Parity Pattern Insights

- **EOE/OEO Impact**: 0.0903 / 0.0852. Alternating parity sequences show a minor impact on bin count compared to raw weight.
- **Even Ratio**: 0.0020. The proportion of even items has a negligible impact on the total bin count, suggesting that capacity, not parity, is the dominant hard constraint.
- **Avg Waste**: 13.06%
