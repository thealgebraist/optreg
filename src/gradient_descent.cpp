#include "gradient_descent.h"
#include <iostream>
#include <cmath>

namespace optreg {

LPSolution GradientDescentSolver::solve(const LPProblem& problem) {
    LPSolution solution;
    uint32_t n = problem.c.size();
    uint32_t m = problem.b.size();
    
    // Initialize x (non-negative)
    solution.x = Vector::Ones(n);
    // GD formulation doesn't use dual vars y, s explicitly in update
    solution.y = Vector::Zero(m);
    
    // Convert A to dense for simplicity in this baseline benchmark
    Eigen::MatrixXd A = Eigen::MatrixXd(problem.A);
    
    // Lipschitz constant estimate for step size: L approx rho * ||A^T A||
    // For safety, we use small fixed learning rate or adaptive
    // User requested "vanilla", but pure fixed LR often diverges instantly with high Rho.
    // We'll use a simple Armijo rule or small fixed.
    
    double lr = learning_rate_;
    
    for (uint32_t i = 0; i < max_iters_; ++i) {
        // 1. Compute Gradient of L(x) = c^T x + rho/2 ||Ax - b||^2
        // Grad = c + rho * A^T (Ax - b)
        Vector residue = A * solution.x - problem.b;
        Vector grad = problem.c + rho_ * A.transpose() * residue;
        
        // 2. Variable Update: x = max(0, x - lr * grad)  (Projected Gradient)
        Vector x_new = solution.x - lr * grad;
        
        // Projection onto non-negative orthant
        for (int j = 0; j < n; ++j) {
            if (x_new(j) < 0) x_new(j) = 0;
        }
        
        // Check change for convergence
        double diff = (x_new - solution.x).norm();
        solution.x = x_new;
        
        double feasibility_err = residue.norm();
        
        if (verbose_ && i % 100 == 0) {
            std::cout << "  GD Iter " << i << ": |Ax-b|=" << feasibility_err 
                      << " |dx|=" << diff << "\r" << std::flush;
        }
        
        if (diff < 1e-6 && feasibility_err < 1e-3) {
            if (verbose_) std::cout << "\n  Converged (GD)\n";
            solution.optimal = true;
            solution.iterations = i;
            solution.objective = problem.c.dot(solution.x);
            return solution;
        }
    }
    
    solution.optimal = false;
    solution.iterations = max_iters_;
    solution.objective = problem.c.dot(solution.x);
    if (verbose_) std::cout << "\n  Max iters reached (GD)\n";
    return solution;
}

} // namespace optreg
