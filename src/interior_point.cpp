#include "interior_point.h"
#include "accelerate_solver.h"
#include "eigen_solver.h"
#include <iostream>
#include <chrono>
#include <algorithm>
#include <cmath>

namespace optreg {
    
#ifdef __APPLE__
struct InteriorPointSolver::AMXSolvers {
    AccelerateSparseSolver sparse;
    AccelerateDenseSolver dense;
};
#endif

InteriorPointSolver::InteriorPointSolver() 
    : mu_(1.0), tolerance_(1e-8), max_iters_(100), verbose_(false) {
}

InteriorPointSolver::~InteriorPointSolver() = default;

void InteriorPointSolver::reset_solvers() {
#ifdef __APPLE__
    if (!amx_solvers_) {
        amx_solvers_ = std::make_unique<AMXSolvers>();
    } else {
        amx_solvers_->sparse.reset_symbolic();
    }
#endif
}

LPSolution InteriorPointSolver::solve(const LPProblem& problem) {
    reset_solvers(); 
    LPSolution solution;
    
    uint32_t n = problem.c.size();
    uint32_t m = problem.b.size();
    
    if (n == 0) {
        solution.optimal = false;
        solution.iterations = 0;
        return solution;
    }
    
    // Initialize primal variables at midpoint of bounds
    solution.x.resize(n);
    for (uint32_t i = 0; i < n; ++i) {
        double lower = problem.lower_bound(i);
        double upper = problem.upper_bound(i);
        if (upper < 1e12) {
            solution.x(i) = 0.5 * (lower + upper);
        } else {
            solution.x(i) = std::max(lower, 0.0) + 1.0;
        }
        // Ensure strictly interior
        if (solution.x(i) <= lower) solution.x(i) = lower + 0.01;
        if (upper < 1e12 && solution.x(i) >= upper) solution.x(i) = upper - 0.01;
    }
    
    solution.y = Vector::Zero(m);
    
    if (verbose_) {
        std::cout << "Pure Barrier Method - Initial point:" << std::endl;
        std::cout << "  x = " << solution.x.transpose() << std::endl;
        std::cout << "  mu = " << mu_ << std::endl;
    }
    
    // Main interior point loop
    auto last_print_time = std::chrono::steady_clock::now();
    for (uint32_t iter = 0; iter < max_iters_; ++iter) {
        // Print status periodically (Pure Barrier - no s,z)
        auto now = std::chrono::steady_clock::now();
        if (verbose_ && (iter < 5 || std::chrono::duration_cast<std::chrono::milliseconds>(now - last_print_time).count() >= 500)) {
            double primal_res = (problem.A * solution.x - problem.b).norm();
            double grad_norm = 0.0;
            Vector g = problem.c;
            for (uint32_t i = 0; i < n; ++i) {
                double x_lower = solution.x(i) - problem.lower_bound(i);
                if (x_lower > 1e-10) g(i) -= mu_ / x_lower;
                if (problem.upper_bound(i) < 1e12) {
                    double x_upper = problem.upper_bound(i) - solution.x(i);
                    if (x_upper > 1e-10) g(i) += mu_ / x_upper;
                }
            }
            grad_norm = g.norm();
            std::cout << "  Iter " << iter << ": mu=" << mu_ 
                      << ", primal_res=" << primal_res
                      << ", grad_norm=" << grad_norm << std::endl;
            last_print_time = now;
        }
        
        if (check_convergence(problem, solution.x, solution.y)) {
            if (verbose_) {
                std::cout << "\n  ✓ Converged at iteration " << iter << "\n";
            }
            solution.optimal = true;
            solution.iterations = iter + 1;
            solution.objective = problem.c.dot(solution.x);
            return solution;
        }
        
        // Compute Newton step (pure barrier - no s, z)
        Vector dx, dy;
        compute_newton_step(problem, solution.x, solution.y, dx, dy);
        
        // Line search
        double alpha = line_search_bounded(problem, solution.x, dx);
        
        // Update variables
        solution.x += alpha * dx;
        solution.y += alpha * dy;
        
        // Update barrier parameter (pure barrier)
        // μ should decrease each iteration, NOT depend on "gap"
        mu_ *= 0.1;  // Decrease by factor of 10 each iteration
        if (mu_ < 1e-10) mu_ = 1e-10;  // Floor to avoid underflow
    }
    
    // Did not converge
    solution.optimal = false;
    solution.iterations = max_iters_;
    // solution.objective = problem.c.dot(solution.x); // Objective is only meaningful for optimal solutions
    
    return solution;
}

void InteriorPointSolver::compute_newton_step(
    const LPProblem& prob,
    const Vector& x,
    const Vector& y,
    Vector& dx,
    Vector& dy
) {
    uint32_t n = x.size();
    uint32_t m = y.size();
    
    dx = Vector::Zero(n);
    dy = Vector::Zero(m);
    
    if (n == 0) return;
    
    const Eigen::SparseMatrix<double>& A_sparse = prob.A;
    
    // PURE BARRIER METHOD
    // Hessian: H = μ/x² + μ/(u-x)² (diagonal)
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
    
    // Gradient: g = c - μ/(x-l) + μ/(u-x)  
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
    
    // Newton-KKT system (Pure Barrier - matches Agda):
    // [H   A^T] [dx] = [-∇f      ]
    // [A    0 ] [dy]   [b - Ax   ]
    // where ∇f = g (already computed gradient)
    
    Vector r_dual = -g;  // RHS for dual block: just negative gradient
    Vector r_prim = prob.b - A_sparse * x;  // RHS for primal block
    
    // Solve via Schur complement: (A H^{-1} A^T) dy = r_prim + A H^{-1} r_dual
    if (m > 0) {
        Vector H_inv_diag = H_diag.cwiseInverse();
        
        // Scale A by H^{-1}
        Eigen::SparseMatrix<double> A_scaled = A_sparse;
        for (int k = 0; k < A_scaled.outerSize(); ++k) {
            for (Eigen::SparseMatrix<double>::InnerIterator it(A_scaled, k); it; ++it) {
                it.valueRef() *= H_inv_diag(it.col());
            }
        }
        
        Eigen::SparseMatrix<double> AHA = A_scaled * A_sparse.transpose();
        for (int i = 0; i < AHA.rows(); ++i) {
            AHA.coeffRef(i, i) += 1e-9;
        }
        
        Vector rhs = r_prim + A_scaled * r_dual;
        
        // Try solvers
        bool solved = false;
        
#ifdef __APPLE__
        if (backend_ == LinearSolverBackend::AMXDense || backend_ == LinearSolverBackend::Auto) {
            Eigen::MatrixXd AHA_dense = Eigen::MatrixXd(AHA);
            if (amx_solvers_->dense.solve(AHA_dense, rhs, dy)) {
                solved = true;
            }
        }
        
        if (!solved && (backend_ == LinearSolverBackend::AMX || backend_ == LinearSolverBackend::Auto)) {
            if (amx_solvers_->sparse.solve(AHA, rhs, dy, true)) {
                solved = true;
            }
        }
#endif
        
        if (!solved) {
            EigenSparseSolver eigen_solver;
            eigen_solver.set_verbose(verbose_);
            if (eigen_solver.solve(AHA, rhs, dy)) {
                solved = true;
            } else {
                Eigen::MatrixXd AHA_dense = Eigen::MatrixXd(AHA);
                dy = AHA_dense.fullPivLu().solve(rhs);
                solved = true;
            }
        }
        
        if (solved) {
            dx = H_inv_diag.asDiagonal() * (r_dual - A_sparse.transpose() * dy);
        }
    } else {
        dy = Vector::Zero(0);
        dx = H_diag.cwiseInverse().cwiseProduct(r_dual);
    }
}

// Add method to also check upper bounds
double InteriorPointSolver::line_search_bounded(
    const LPProblem& prob,
    const Vector& x,
    const Vector& dx
) {
    double alpha = 1.0;
    
    // Keep x strictly interior: l < x < u
    for (int i = 0; i < x.size(); ++i) {
        // Lower bound: x + α·dx > l
        if (dx(i) < 0) {
            double max_step = (x(i) - prob.lower_bound(i)) / (-dx(i));
            alpha = std::min(alpha, 0.99 * max_step);
        }
        
        // Upper bound: x + α·dx < u
        if (dx(i) > 0 && prob.upper_bound(i) < 1e12) {
            double max_step = (prob.upper_bound(i) - x(i)) / dx(i);
            alpha = std::min(alpha, 0.99 * max_step);
        }
    }
    
    return std::max(alpha, 1e-8);
}

bool InteriorPointSolver::check_convergence(
    const LPProblem& prob,
    const Vector& x,
    const Vector& y
) {
    // Barrier method: converge when μ → 0 and constraints satisfied
    // NOTE: Gradient norm is NOT a valid criterion! 
    // At optimum, ∇f → c (original objective gradient) as μ → 0
    double primal_res = (prob.A * x - prob.b).norm();
    
    return mu_ < tolerance_ && primal_res < tolerance_;
}

} // namespace optreg
