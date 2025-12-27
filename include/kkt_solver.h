#pragma once

#include "interior_point.h"

namespace optreg {

// Task 7: KKT system solver

// KKT system for interior point method:
// [ H   A^T ] [ dx ]   [ -∇f - A^T y ]
// [ A    0  ] [ dy ] = [ -Ax + b      ]
// where H = ∇²L (Hessian of Lagrangian)

class KKTSolver {
public:
    // Solve KKT system using sparse Cholesky
    void solve(
        const SparseMatrix& H,        // Hessian
        const SparseMatrix& A,        // constraint matrix
        const Vector& grad_f,         // gradient of objective
        const Vector& y,              // dual variables
        const Vector& residual_primal, // primal residual
        Vector& dx,                   // output: primal step
        Vector& dy                    // output: dual step
    );
    
    // Solve using iterative method (conjugate gradient)
    void solve_iterative(
        const SparseMatrix& H,
        const SparseMatrix& A,
        const Vector& rhs_primal,
        const Vector& rhs_dual,
        Vector& dx,
        Vector& dy,   
        double tolerance = 1e-8
    );

private:
    // Form augmented system
    SparseMatrix form_augmented_system(
        const SparseMatrix& H,
        const SparseMatrix& A
    );
};

} // namespace optreg
