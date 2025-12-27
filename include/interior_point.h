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
    Vector y;           // dual variables (equality constraints)
    // Note: s, z removed - computed implicitly from barrier: s = μ/x, z = μ/(u-x)
    double objective;   // objective value
    bool optimal;       // convergence flag
    uint32_t iterations;
};

// Task 6: Primal-dual interior point method
class InteriorPointSolver {
public:
    InteriorPointSolver();
    ~InteriorPointSolver();
    
    LPSolution solve(const LPProblem& problem);
    
    enum class LinearSolverBackend {
        AMX,        // Sparse solver (currently unstable)
        AMXDense,   // Dense solver using LAPACK
        EigenSparse,
        EigenDense,
        Auto
    };

    void set_tolerance(double tol) { tolerance_ = tol; }
    void set_max_iterations(uint32_t iters) { max_iters_ = iters; }
    void set_verbose(bool v) { verbose_ = v; }
    void set_linear_solver_backend(LinearSolverBackend backend) { 
        backend_ = backend; 
        reset_solvers();
    }
    
    void reset_solvers();

private:
#ifdef __APPLE__
    struct AMXSolvers;
    std::unique_ptr<AMXSolvers> amx_solvers_;
#endif
    
    double mu_;            // Barrier parameter
    double tolerance_;     // Convergence tolerance
    uint32_t max_iters_;   // Maximum iterations
    bool verbose_;         // Print status updates
    LinearSolverBackend backend_ = LinearSolverBackend::Auto;
    
    // Compute Newton step for KKT system
    void compute_newton_step(
        const LPProblem& prob,
        const Vector& x,
        const Vector& y,
        Vector& dx,
        Vector& dy
    );
    
    double line_search(
        const Vector& x,
        const Vector& dx
    );
    
    double line_search_bounded(
        const LPProblem& prob,
        const Vector& x,
        const Vector& dx
    );
    
    // Check KKT conditions
    bool check_convergence(
        const LPProblem& prob,
        const Vector& x,
        const Vector& y
    );
};

} // namespace optreg
