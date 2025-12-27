#include "interior_point.h"
#include <cmath>
#include <iostream>
#include <chrono>
#include <Eigen/Sparse>
#include <Eigen/SparseCholesky>
#include "accelerate_solver.h"
#include "eigen_solver.h"

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
    
    // Initialize primal variables: start at midpoint of bounds
    solution.x.resize(n);
    for (uint32_t i = 0; i < n; ++i) {
        double lower = problem.lower_bound(i);
        double upper = problem.upper_bound(i);
        
        // Choose midpoint if both bounds are finite
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
    solution.s = problem.c - Eigen::MatrixXd(problem.A).transpose() * solution.y;
    
    // Ensure s > 0 (dual feasibility)
    for (uint32_t i = 0; i < n; ++i) {
        if (solution.s(i) <= 0) {
            solution.s(i) = 1.0;
        }
    }
    
    // Main interior point loop
    auto last_print_time = std::chrono::steady_clock::now();
    for (uint32_t iter = 0; iter < max_iters_; ++iter) {
        // Print status approx 2 times/sec
        auto now = std::chrono::steady_clock::now();
        if (verbose_ && std::chrono::duration_cast<std::chrono::milliseconds>(now - last_print_time).count() >= 500) {
            double gap = solution.x.dot(solution.s);
            std::cout << "  Iter " << iter << ": gap=" << gap 
                      << ", mu=" << mu_ << "\r" << std::flush;
            last_print_time = now;
        }
        
        // Check convergence
        if (check_convergence(problem, solution.x, solution.y, solution.s)) {
            if (verbose_) {
                std::cout << "\n  ✓ Converged at iteration " << iter << "\n";
            }
            solution.optimal = true;
            solution.iterations = iter + 1;
            solution.objective = problem.c.dot(solution.x);
            return solution;
        }
        
        // Compute Newton step
        Vector dx, dy, ds;
        compute_newton_step(problem, solution.x, solution.y, solution.s, dx, dy, ds);
        
        // Line search for step size (respects upper bounds)
        double alpha = line_search_bounded(problem, solution.x, solution.s, dx, ds);
        
        // Update variables
        solution.x += alpha * dx;
        solution.y += alpha * dy;
        solution.s += alpha * ds;
        
        // Update barrier parameter
        double gap = solution.x.dot(solution.s);
        double mu_new = gap / n / 10.0; // Aggressive decrease
        // Predictor-corrector heuristic would be better, but simple is robust
        mu_ = std::min(mu_, mu_new);
        if (mu_ < 1e-10) mu_ = 1e-10;
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
    const Vector& s,
    Vector& dx,
    Vector& dy,
    Vector& ds
) {
    uint32_t n = x.size();
    uint32_t m = y.size();
    
    // Initialize output
    dx = Vector::Zero(n);
    dy = Vector::Zero(m);
    ds = Vector::Zero(n);
    
    if (n == 0) return;
    
    // A is already sparse in LPProblem
    const Eigen::SparseMatrix<double>& A_sparse = prob.A;
    
    // Compute diagonal Hessian: H = S X^{-1} + μ/(U-X)^2 for upper bounds
    Vector H_diag(n);
    for (uint32_t i = 0; i < n; ++i) {
        double h_lower = s(i) / x(i);
        double h_upper = 0.0;
        
        // Add upper bound barrier term if upper bound is finite
        if (prob.upper_bound(i) < 1e12) {
            double gap_upper = prob.upper_bound(i) - x(i);
            if (gap_upper > 1e-10) {
                h_upper = mu_ / (gap_upper * gap_upper);
            } else {
                h_upper = 1e10; // Large penalty if too close to bound
            }
        }
        
        H_diag(i) = h_lower + h_upper + 1e-8; 
    }
    
    // Right-hand side with lower and upper bound barrier gradients
    Vector r_dual = -prob.c + A_sparse.transpose() * y + s;
    for (uint32_t i = 0; i < n; ++i) {
        // Lower bound barrier: -μ/x
        r_dual(i) -= mu_ / x(i);
        
        // Upper bound barrier: μ/(u - x)
        if (prob.upper_bound(i) < 1e12) {
            double gap_upper = prob.upper_bound(i) - x(i);
            if (gap_upper > 1e-10) {
                r_dual(i) += mu_ / gap_upper;
            }
        }
    }
    
    Vector r_prim = -(A_sparse * x - prob.b);
    
    // Solve reduced system: (A H^{-1} A^T) dy = r_prim - A H^{-1} r_dual
    if (m > 0) {
        Vector H_inv_diag = H_diag.cwiseInverse();
        
        // Form A H^{-1} A^T efficiently using sparse operations
        // D is H_inv_diag
        // Scale columns of A by D
        Eigen::SparseMatrix<double> A_scaled = A_sparse;
        for (int k=0; k < A_scaled.outerSize(); ++k) {
            for (Eigen::SparseMatrix<double>::InnerIterator it(A_scaled, k); it; ++it) {
                it.valueRef() *= H_inv_diag(it.col());
            }
        }
        
        // AHA = A * H^{-1} * A^T
        Eigen::SparseMatrix<double> AHA = A_scaled * A_sparse.transpose();
        
        // Add small regularization for stability
        for (int i = 0; i < AHA.rows(); ++i) {
            AHA.coeffRef(i, i) += 1e-9;
        }
        
        Vector rhs = r_prim - A_scaled * r_dual;
        
        bool solved = false;
        
        // Strategy Selection
        bool try_amx_sparse = (backend_ == LinearSolverBackend::AMX);
        bool try_amx_dense = (backend_ == LinearSolverBackend::Auto || backend_ == LinearSolverBackend::AMXDense);
        bool try_eigen = (backend_ == LinearSolverBackend::Auto || backend_ == LinearSolverBackend::EigenSparse);
        bool try_dense = (backend_ == LinearSolverBackend::Auto || backend_ == LinearSolverBackend::EigenDense);
        
#ifdef __APPLE__
        if (try_amx_dense && !solved) {
            Eigen::MatrixXd AHA_dense = Eigen::MatrixXd(AHA);
            if (amx_solvers_->dense.solve(AHA_dense, rhs, dy)) {
                solved = true;
            }
        }

        if (try_amx_sparse && !solved) {
            if (amx_solvers_->sparse.solve(AHA, rhs, dy, true)) {
                 solved = true;
            }
        }
#endif

        if (try_eigen && !solved) {
            EigenSparseSolver eigen_solver;
            eigen_solver.set_verbose(verbose_);
            if (eigen_solver.solve(AHA, rhs, dy)) {
                solved = true;
            }
        }
        
        // Dense Solver Logic
        // In Auto mode, EigenSparseSolver falls back to Dense QR internally.
        // But if explicitly set to EigenDense, or if backend forced, we do it here.
        if (try_dense && !solved) {
             if(verbose_) std::cout << "  (Using Dense methods) ";
             Eigen::MatrixXd AHA_dense = Eigen::MatrixXd(AHA);
             dy = AHA_dense.fullPivLu().solve(rhs); // Full pivoting LU for stability
             solved = true; 
        }
        
        if (!solved && verbose_) std::cout << " [ALL SOLVERS FAILED] ";

        // Back-substitute for dx
        if (solved) {
            dx = H_inv_diag.asDiagonal() * (r_dual - A_sparse.transpose() * dy);
        }
        
    } else {
        // No constraints
        dy = Vector::Zero(0);
        dx = (s.cwiseProduct(x.cwiseInverse())).cwiseInverse().cwiseProduct(r_dual);
    }
    
    // ds computation remains same
    for (uint32_t i = 0; i < n; ++i) {
        ds(i) = (mu_ - s(i) * dx(i)) / x(i) - s(i);
    }
}

double InteriorPointSolver::line_search(
    const Vector& x,
    const Vector& s,
    const Vector& dx,
    const Vector& ds
) {
    double alpha = 1.0;
    
    // Find maximum step that keeps x, s > 0
    for (int i = 0; i < x.size(); ++i) {
        if (dx(i) < 0) {
            alpha = std::min(alpha, -0.95 * x(i) / dx(i));
        }
        if (ds(i) < 0) {
            alpha = std::min(alpha, -0.95 * s(i) / ds(i));
        }
    }
    
    return std::max(alpha, 1e-8);
}

// Add method to also check upper bounds
double InteriorPointSolver::line_search_bounded(
    const LPProblem& prob,
    const Vector& x,
    const Vector& s,
    const Vector& dx,
    const Vector& ds
) {
    double alpha = 1.0;
    
    // Find maximum step that keeps x, s > 0 and x < u
    for (int i = 0; i < x.size(); ++i) {
        if (dx(i) < 0) {
            alpha = std::min(alpha, -0.95 * x(i) / dx(i));
        }
        if (ds(i) < 0) {
            alpha = std::min(alpha, -0.95 * s(i) / ds(i));
        }
        // Upper bound check
        if (dx(i) > 0 && prob.upper_bound(i) < 1e12) {
            double gap = prob.upper_bound(i) - x(i);
            if (gap > 0) {
                alpha = std::min(alpha, 0.95 * gap / dx(i));
            }
        }
    }
    
    return std::max(alpha, 1e-8);
}

bool InteriorPointSolver::check_convergence(
    const LPProblem& prob,
    const Vector& x,
    const Vector& y,
    const Vector& s
) {
    // Check KKT conditions:
    // 1. Primal feasibility: ||Ax - b|| < tol
    Vector residual_primal = prob.A * x - prob.b;
    double primal_norm = residual_primal.norm();
    
    // 2. Dual feasibility: ||s - c + A^T y|| < tol
    Vector residual_dual = s - prob.c + prob.A.transpose() * y;
    double dual_norm = residual_dual.norm();
    
    // 3. Complementarity: |x^T s| < tol
    double gap = std::abs(x.dot(s));
    
    return (primal_norm < tolerance_) && 
           (dual_norm < tolerance_) && 
           (gap < tolerance_);
}

} // namespace optreg
