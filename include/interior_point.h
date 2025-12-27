#pragma once

#include <vector>
#include <Eigen/Dense>
#include <Eigen/Sparse>

namespace optreg {

// Task 5-6: LP formulation and interior point solver

using Matrix = Eigen::MatrixXd;
using Vector = Eigen::VectorXd;
using SparseMatrix = Eigen::SparseMatrix<double>;

struct LPProblem {
    // min c^T x
    // s.t. Ax = b
    //      x >= 0
    Vector c;           // objective coefficients
    SparseMatrix A;     // constraint matrix
    Vector b;           // RHS  
    Vector lower_bound; // variable lower bounds
    Vector upper_bound; // variable upper bounds
};

struct LPSolution {
    Vector x;           // primal variables
    Vector y;           // dual variables (equality)
    Vector s;           // dual slack variables
    double objective;   // objective value
    bool optimal;       // convergence flag
    uint32_t iterations;
};

// Task 6: Primal-dual interior point method
class InteriorPointSolver {
public:
    InteriorPointSolver() : max_iters_(100), tolerance_(1e-6), mu_(0.1) {}
    
    LPSolution solve(const LPProblem& problem);
    
    void set_tolerance(double tol) { tolerance_ = tol; }
    void set_max_iterations(uint32_t max_it) { max_iters_ = max_it; }
    
private:
    uint32_t max_iters_;
    double tolerance_;
    double mu_;  // barrier parameter
    
    // Compute Newton step for KKT system
    void compute_newton_step(
        const LPProblem& prob,
        const Vector& x,
        const Vector& y,
        const Vector& s,
        Vector& dx,
        Vector& dy,
        Vector& ds
    );
    
    // Line search for step size
    double line_search(
        const Vector& x,
        const Vector& s,
        const Vector& dx,
        const Vector& ds
    );
    
    // Check KKT conditions
    bool check_convergence(
        const LPProblem& prob,
        const Vector& x,
        const Vector& y,
        const Vector& s
    );
};

} // namespace optreg
