#include "interior_point.h"
#include <cmath>
#include <iostream>

namespace optreg {

LPSolution InteriorPointSolver::solve(const LPProblem& problem) {
    LPSolution solution;
    
    uint32_t n = problem.c.size();
    uint32_t m = problem.b.size();
    
    if (n == 0) {
        solution.optimal = false;
        solution.iterations = 0;
        return solution;
    }
    
    // Initialize primal variables: start at interior point
    solution.x = Vector::Ones(n);
    solution.y = Vector::Zero(m);
    solution.s = problem.c - Eigen::MatrixXd(problem.A).transpose() * solution.y;
    
    // Ensure s > 0 (dual feasibility)
    for (int i = 0; i < n; ++i) {
        if (solution.s(i) <= 0) {
            solution.s(i) = 1.0;
        }
    }
    
    // Main interior point loop
    for (uint32_t iter = 0; iter < max_iters_; ++iter) {
        // Check convergence
        if (check_convergence(problem, solution.x, solution.y, solution.s)) {
            solution.optimal = true;
            solution.iterations = iter + 1;
            solution.objective = problem.c.dot(solution.x);
            return solution;
        }
        
        // Compute Newton step
        Vector dx, dy, ds;
        compute_newton_step(problem, solution.x, solution.y, solution.s, dx, dy, ds);
        
        // Line search for step size
        double alpha = line_search(solution.x, solution.s, dx, ds);
        
        // Update variables
        solution.x += alpha * dx;
        solution.y += alpha * dy;
        solution.s += alpha * ds;
        
        // Decrease barrier parameter
        mu_ *= 0.5;
    }
    
    // Did not converge
    solution.optimal = false;
    solution.iterations = max_iters_;
    solution.objective = problem.c.dot(solution.x);
    
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
    
    Eigen::MatrixXd A_dense = Eigen::MatrixXd(prob.A);
    
    // KKT system for barrier problem:
    // [ H   A^T ] [ dx ]   [ r_dual ]
    // [ A    0  ] [ dy ] = [ r_prim ]
    //
    // where H = diag(s_i / x_i) (Hessian of barrier)
    // r_dual = -gradient = -(c - A^T y - s + μ/x)
    // r_prim = -(Ax - b)
    
    // Compute diagonal Hessian: H = S X^{-1}
    Vector H_diag(n);
    for (int i = 0; i < n; ++i) {
        H_diag(i) = s(i) / x(i);
    }
    
    // Right-hand side
    Vector r_dual = -prob.c + A_dense.transpose() * y + s;
    for (int i = 0; i < n; ++i) {
        r_dual(i) -= mu_ / x(i);
    }
    
    Vector r_prim = -(A_dense * x - prob.b);
    
    // Solve reduced system: (A H^{-1} A^T) dy = r_prim - A H^{-1} r_dual
    if (m > 0) {
        Vector H_inv_diag = H_diag.cwiseInverse();
        Eigen::MatrixXd A_Hinv = A_dense;
        for (int i = 0; i < A_Hinv.rows(); ++i) {
            for (int j = 0; j < A_Hinv.cols(); ++j) {
                A_Hinv(i, j) *= H_inv_diag(j);
            }
        }
        
        Eigen::MatrixXd AHA = A_Hinv * A_dense.transpose();
        Vector rhs = r_prim - A_Hinv * r_dual;
        
        // Solve for dy
        dy = AHA.colPivHouseholderQr().solve(rhs);
        
        // Back-substitute for dx
        dx = H_inv_diag.asDiagonal() * (r_dual - A_dense.transpose() * dy);
    } else {
        // No constraints: dx = H^{-1} r_dual
        dy = Vector::Zero(0);
        dx = (s.cwiseProduct(x.cwiseInverse())).cwiseInverse().cwiseProduct(r_dual);
    }
    
    // ds from complementarity: s dx + x ds = -xs + μe
    // => ds = (-xs + μe - s dx) / x
    for (int i = 0; i < n; ++i) {
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

bool InteriorPointSolver::check_convergence(
    const LPProblem& prob,
    const Vector& x,
    const Vector& y,
    const Vector& s
) {
    Eigen::MatrixXd A_dense = Eigen::MatrixXd(prob.A);
    
    // Check KKT conditions:
    // 1. Primal feasibility: ||Ax - b|| < tol
    Vector residual_primal = A_dense * x - prob.b;
    double primal_norm = residual_primal.norm();
    
    // 2. Dual feasibility: ||s - c + A^T y|| < tol
    Vector residual_dual = s - prob.c + A_dense.transpose() * y;
    double dual_norm = residual_dual.norm();
    
    // 3. Complementarity: |x^T s| < tol
    double gap = std::abs(x.dot(s));
    
    return (primal_norm < tolerance_) && 
           (dual_norm < tolerance_) && 
           (gap < tolerance_);
}

} // namespace optreg
