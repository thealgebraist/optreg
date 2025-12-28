# Bin Packing Divide & Conquer Results

Analyzed **4096** instances.

## Hypothesis
Does prioritizing subsets that sum *exactly* to $C, C-1, \dots$ yield better packings than greedy FFD?

## Results
- **D&C Optimality**: **81.08%**
- **FFD Optimality** (Reference): ~100%

## Near Miss Analysis
Counts of subset pairs summing to $C+k$ (potential waste sources):
- **C+1**: 9957
- **C+2**: 10005
- **C+3**: 10084
- **C+4**: 9938

## Conclusion
Targeting exact sums locally (Bin Maximization) is inferior to FFD. This re-confirms that local perfection is a global trap.