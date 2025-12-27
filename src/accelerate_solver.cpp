#include "accelerate_solver.h"
#include <iostream>
#include <cstring>
#include <cstdlib>

namespace optreg {

AccelerateSparseSolver::AccelerateSparseSolver() : factor_valid_(false), symbolic_valid_(false) {}

AccelerateSparseSolver::~AccelerateSparseSolver() {
    if (factor_valid_) {
        SparseCleanup(factor_);
    }
    if (symbolic_valid_) {
        SparseCleanup(symbolic_);
    }
    cleanup_resources();
}

void AccelerateSparseSolver::reset_symbolic() {
    if (symbolic_valid_) {
        SparseCleanup(symbolic_);
        symbolic_valid_ = false;
    }
}

// AMX Instructions
// #define AMX_SET() asm volatile(".word 0x00201220")
// #define AMX_CLR() asm volatile(".word 0x00201221")

void AccelerateSparseSolver::cleanup_resources() {
    if (column_starts_) std::free(column_starts_);
    if (row_indices_) std::free(row_indices_);
    if (values_) std::free(values_);
    column_starts_ = nullptr;
    row_indices_ = nullptr;
    values_ = nullptr;
}

bool AccelerateSparseSolver::solve(const Eigen::SparseMatrix<double>& A, const Eigen::VectorXd& b, Eigen::VectorXd& x, bool keep_symbolic) {
    if (A.rows() == 0) return true;
    if (!A.isCompressed()) return false;
    
    // If the structure changed or we aren't keeping it, reset
    if (!keep_symbolic && symbolic_valid_) {
        reset_symbolic();
    }

    // Clean up previous numeric factor
    if (factor_valid_) {
        SparseCleanup(factor_);
        factor_valid_ = false;
    }
    
    // AMX/Accelerate Cholesky requires the UPPER triangle only for symmetric matrices.
    Eigen::SparseMatrix<double> U_tmp = A.triangularView<Eigen::Upper>();
    U_tmp.makeCompressed();
    
    // For IP, the structure of AHA is constant. We only need the symbolic part once.
    // If we already have it, we just need to update the values.
    
    // Optimization: If keep_symbolic is true and we have one, assume structure is SAME.
    // We still need to extract values in the same order.
    // Eigen's triangularView extraction might be slow to do every iteration.
    
    int n = U_tmp.rows();
    int nz = U_tmp.nonZeros();
    
    // Reallocate if needed with 64-byte alignment
    if (n + 1 > (int)col_cap_) {
        if (column_starts_) std::free(column_starts_);
        int ret = posix_memalign((void**)&column_starts_, 64, (n + 1) * sizeof(long));
        if (ret != 0) return false;
        col_cap_ = n + 1;
    }
    if (nz > (int)row_cap_) {
        if (row_indices_) std::free(row_indices_);
        int ret = posix_memalign((void**)&row_indices_, 64, nz * sizeof(int));
        if (ret != 0) return false;
        row_cap_ = nz;
    }
    if (nz > (int)val_cap_) {
        if (values_) std::free(values_);
        int ret = posix_memalign((void**)&values_, 64, nz * sizeof(double));
        if (ret != 0) return false;
        val_cap_ = nz;
    }
    
    // Copy data
    for (int i = 0; i <= n; ++i) column_starts_[i] = (long)U_tmp.outerIndexPtr()[i];
    for (int i = 0; i < nz; ++i) row_indices_[i] = (int)U_tmp.innerIndexPtr()[i];
    for (int i = 0; i < nz; ++i) values_[i] = U_tmp.valuePtr()[i];
    
    // Define sparse matrix structure
    SparseMatrix_Double A_acc;
    std::memset(&A_acc, 0, sizeof(A_acc));
    A_acc.structure.rowCount = n;
    A_acc.structure.columnCount = n;
    A_acc.structure.columnStarts = column_starts_;
    A_acc.structure.rowIndices = row_indices_;
    A_acc.structure.attributes.kind = SparseSymmetric;
    A_acc.structure.blockSize = 1;
    A_acc.data = values_;
    
    if (!symbolic_valid_) {
        // Symbolic Factorization
        SparseSymbolicFactorOptions options;
        std::memset(&options, 0, sizeof(options));
        options.control = SparseDefaultControl;
        options.orderMethod = SparseOrderDefault;
        options.malloc = malloc;
        options.free = free;
        
        symbolic_ = SparseFactor(SparseFactorizationCholesky, A_acc.structure, options);
        if (symbolic_.status != SparseStatusOK) return false;
        symbolic_valid_ = true;
    }
    
    // Numerical Factorization
    SparseNumericFactorOptions numeric_options;
    std::memset(&numeric_options, 0, sizeof(numeric_options));
    numeric_options.control = SparseDefaultControl;
    numeric_options.scalingMethod = SparseScalingDefault;
    
    factor_ = SparseFactor(symbolic_, A_acc, numeric_options);
    
    if (factor_.status != SparseStatusOK) {
        factor_valid_ = false;
        return false;
    }
    factor_valid_ = true;
    
    // Solve
    if (b.size() != n) return false;

    x.resize(n);
    x.resize(n);
    DenseVector_Double b_dense;
    b_dense.count = n;
    b_dense.data = (double*)b.data();
    
    DenseVector_Double x_dense;
    x_dense.count = n;
    x_dense.data = (double*)x.data();
    
    SparseSolve(factor_, b_dense, x_dense);
    
    return true;
}

bool AccelerateSparseSolver::solve_refined(const Eigen::SparseMatrix<double>& A, const Eigen::VectorXd& b, Eigen::VectorXd& x) {
    if (!solve(A, b, x)) return false;
    return true;
}


bool AccelerateDenseSolver::solve(const Eigen::MatrixXd& A, const Eigen::VectorXd& b, Eigen::VectorXd& x) {
    if (A.rows() == 0) return true;
    if (A.rows() != A.cols()) return false;
    
    int n = A.rows();
    int nrhs = 1;
    int info = 0;
    
    // We need to copy A because dposv overwrites it with the factor
    Eigen::MatrixXd A_copy = A;
    x = b; // dposv overwrites b with the solution x
    
    char uplo = 'U'; // Use upper triangle
    int lda = n;
    int ldb = n;
    
    // LAPACK dposv: Solves A*X = B for a symmetric positive definite matrix A
    // using the Cholesky factorization A = U^H * U or A = L * L^H.
    dposv_(&uplo, &n, &nrhs, A_copy.data(), &lda, x.data(), &ldb, &info);
    
    if (info != 0) {
        std::cerr << "AccelerateDenseSolver (dposv) failed with info=" << info << std::endl;
        return false;
    }
    
    return true;
}

} // namespace optreg
