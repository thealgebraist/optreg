#include "eigen_solver.h"
#include <iostream>
#include <Eigen/SparseCholesky>
#include <Eigen/SparseQR>

namespace optreg {

bool EigenSparseSolver::solve(const Eigen::SparseMatrix<double>& A, const Eigen::VectorXd& b, Eigen::VectorXd& x) {
    bool solved = false;
    
    // 1. Try SimplicialLLT (Fastest, for SPD)
    Eigen::SimplicialLLT<Eigen::SparseMatrix<double>> llt;
    llt.compute(A);
    
    if (llt.info() == Eigen::Success) {
        x = llt.solve(b);
        if (llt.info() == Eigen::Success) {
            solved = true;
            // Optional refinement
            Eigen::VectorXd res = b - A * x;
            if (res.norm() > 1e-6) {
                x += llt.solve(res);
            }
        }
    }
    
    // 2. Try SimplicialLDLT (More stable for indefinite/semi-definite)
    if (!solved) {
        if (verbose_) std::cout << "  (Eigen: Falling back to LDLT) ";
        Eigen::SimplicialLDLT<Eigen::SparseMatrix<double>> ldlt;
        ldlt.compute(A);
        if (ldlt.info() == Eigen::Success) {
            x = ldlt.solve(b);
            solved = true;
        }
    }
    
    // 3. Try SparseQR (Stable, handles rank deficient)
    if (!solved) {
        if (verbose_) std::cout << "  (Eigen: Falling back to QR) ";
        Eigen::SparseQR<Eigen::SparseMatrix<double>, Eigen::COLAMDOrdering<int>> qr;
        qr.compute(A);
        if (qr.info() == Eigen::Success) {
            x = qr.solve(b);
            solved = true;
        }
    }
    
    // 4. Try Dense QR (Last resort)
    if (!solved) {
        if (verbose_) std::cout << "  (Eigen: Falling back to Dense QR) ";
        Eigen::MatrixXd A_dense = Eigen::MatrixXd(A);
        x = A_dense.colPivHouseholderQr().solve(b);
        solved = true; // Dense QR almost always works technically
    }
    
    return solved;
}

} // namespace optreg
