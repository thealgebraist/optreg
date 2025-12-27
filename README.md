# optreg - Optimal Register Allocator

Optimal register allocation using Linear Programming and Branch-and-Bound.

## Features

- **Foundation (Tasks 1-4)** ✅
  - IR parsing and CFG construction
  - Live range analysis (backward dataflow)
  - Interference graph construction
  
- **LP Solver (Tasks 5-8)** ✅
  - Interior point method with KKT system
  - Primal-dual Newton steps
  - Convergence checking
  
- **Graph Coloring IP** ✅
  - Register allocation as graph coloring
  - Spill cost calculation
  - LP-based allocation

- **Benchmark**
  - 256 random test cases
  - Heuristic vs optimal comparison
  - Performance metrics

## Build

```bash
# Requires Eigen
brew install eigen

# Build
make

# Run benchmark
make mediumrandom
```

## Implementation

- **C++23** with Eigen for matrix operations
- Interior point solver for LP relaxation
- Graph coloring formulation for register allocation
- Greedy heuristic baseline

## Formal Verification

Agda proofs available for:
- Numerical stability properties
- Non-convergence cases (unbounded/infeasible)
- KKT condition correctness

See parent directory for Agda modules.
