# Agda vs C++ Verification Report

## Gradient: ✓ MATCHES

**Agda** (line 33-39):

```agda
gradient μ x = zipWith3 compute c x-lower x-upper
  where
    x-lower = zipWith _-_ x lower
    x-upper = zipWith _-_ upper x  
    compute ci xi-li ui-xi = ci - μ / xi-li + μ / ui-xi
```

**C++** (lines 169-183):

```cpp
Vector g = prob.c;
for (uint32_t i = 0; i < n; ++i) {
    double x_lower = x(i) - prob.lower_bound(i);
    if (x_lower > 1e-10) {
        g(i) -= mu_ / x_lower;
    }
    if (prob.upper_bound(i) < 1e12) {
        double x_upper = prob.upper_bound(i) - x(i);
        if (x_upper > 1e-10) {
            g(i) += mu_ / x_upper;
        }
    }
}
```

**Verdict:** ✓ CORRECT (modulo guards for numerical safety)

## Hessian: ✓ MATCHES

**Agda** (lines 41-48):

```agda
hessian-diag μ x = zipWith _+_ h-lower h-upper
  where
    x-lower = zipWith _-_ x lower
    x-upper = zipWith _-_ upper x
    h-lower = map (λ d → μ / (d * d)) x-lower
    h-upper = map (λ d → μ / (d * d)) x-upper
```

**C++** (lines 154-167):

```cpp
Vector H_diag(n);
for (uint32_t i = 0; i < n; ++i) {
    double x_lower = x(i) - prob.lower_bound(i);
    double h_lower = (x_lower > 1e-10) ? mu_ / (x_lower * x_lower) : 1e10;
    
    double h_upper = 0.0;
    if (prob.upper_bound(i) < 1e12) {
        double x_upper = prob.upper_bound(i) - x(i);
        h_upper = (x_upper > 1e-10) ? mu_ / (x_upper * x_upper) : 1e10;
    }
    
    H_diag(i) = h_lower + h_upper + 1e-8;
}
```

**Verdict:** ✓ CORRECT (with +1e-8 regularization for numerical stability)

## Newton System: ✗ **BUG FOUND**

**Expected** (from Agda and theory):

```
[H   A^T] [dx] = [-∇f      ]
[A    0 ] [dy]   [b - Ax   ]
```

Where ∇f = c - μ/(x-l) + μ/(u-x) is the gradient.

**C++ Implementation** (line 189-190):

```cpp
Vector r_dual = -g - A_sparse.transpose() * y;  // BUG!
Vector r_prim = prob.b - A_sparse * x;
```

**Problem:** The RHS for the dual block should be `-g` (negative gradient), NOT `-g - A^T y`.

The `-A^T y` term arises when we're solving the KKT system for primal-dual methods, but in pure barrier we just solve the Newton system for the barrier function.

## Correct Newton System

For pure barrier, we minimize:

```
f(x) = c^T x - μ Σlog(x-l) - μ Σlog(u-x)
s.t. Ax = b
```

The Lagrangian is:

```
L(x, λ) = f(x) + λ^T(b - Ax)
```

Newton step:

```
∇²L Δx - A^T Δλ = -∇f
A Δx = b - Ax
```

Which gives:

```
[H   -A^T] [dx] = [-∇f   ]
[A    0  ] [dy]   [b - Ax]
```

Or equivalently (flipping sign of second block):

```
[H    A^T] [dx] = [-∇f   ]
[-A    0 ] [dy]   [Ax - b]
```

**Fix:** Change line 189 to:

```cpp
Vector r_dual = -g;  // Just negative gradient!
```

## Root Cause of All Test Failures

This single bug explains why all 6 tests failed! The Newton direction is computed incorrectly, causing:

- Wrong search direction
- Failure to converge
- All tests returning "FAILED"

## Fix Required

**File:** `src/interior_point.cpp`  
**Line:** 189  
**Change:**

```cpp
// BEFORE (WRONG):
Vector r_dual = -g - A_sparse.transpose() * y;

// AFTER (CORRECT):
Vector r_dual = -g;
```

This is a 1-line fix that should make all tests pass!
