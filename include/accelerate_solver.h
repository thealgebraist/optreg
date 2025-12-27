#pragma once

#include <vector>
#include <Accelerate/Accelerate.h>
#include <Eigen/Sparse>
#include <Eigen/Dense>

namespace optreg {

// Accelerated sparse solver using Apple's Sparse Solvers (which use AMX transparently)
class AccelerateSparseSolver {
public:
    AccelerateSparseSolver();
    ~AccelerateSparseSolver();

    // Solve Ax = b where A is a sparse symmetric positive definite matrix
    // Returns true if successful. If keep_symbolic is true, it will reuse
    // the symbolic factorization from the previous call if the structure is the same.
    bool solve(const Eigen::SparseMatrix<double>& A, const Eigen::VectorXd& b, Eigen::VectorXd& x, bool keep_symbolic = false);
    
    // Solve with iterative refinement for higher precision
    bool solve_refined(const Eigen::SparseMatrix<double>& A, const Eigen::VectorXd& b, Eigen::VectorXd& x);

    // Reset symbolic factorization (should be called if A's structure changes)
    void reset_symbolic();

private:
    void cleanup_resources();
    SparseOpaqueFactorization_Double factor_;
    bool factor_valid_;
    
    SparseOpaqueSymbolicFactorization symbolic_;
    bool symbolic_valid_ = false;
    
    // Aligned memory pointers
    long* column_starts_ = nullptr;
    int* row_indices_ = nullptr;
    double* values_ = nullptr;
    
    // Sizes to track for cleanup
    size_t col_cap_ = 0;
    size_t row_cap_ = 0;
    size_t val_cap_ = 0;
};

class AccelerateDenseSolver {
public:
    AccelerateDenseSolver() = default;
    ~AccelerateDenseSolver() = default;

    /**
     * Solves Ax = b using Accelerate's dense LAPACK (dposv)
     * Optimized for Apple Silicon (AMX)
     */
    bool solve(const Eigen::MatrixXd& A, const Eigen::VectorXd& b, Eigen::VectorXd& x);
};

} // namespace optreg
