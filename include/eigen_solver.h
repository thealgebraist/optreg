#pragma once

#include <Eigen/Sparse>
#include <Eigen/Dense>

namespace optreg {

// Wrapper for Eigen's sparse solvers (LLT, LDLT, QR)
class EigenSparseSolver {
public:
    EigenSparseSolver() = default;
    
    // Solve Ax = b
    // Tries Cholesky (LLT) first, then LDLT, then QR
    bool solve(const Eigen::SparseMatrix<double>& A, const Eigen::VectorXd& b, Eigen::VectorXd& x);

    // Set verbose for debugging
    void set_verbose(bool v) { verbose_ = v; }

private:
    bool verbose_ = false;
};

} // namespace optreg
