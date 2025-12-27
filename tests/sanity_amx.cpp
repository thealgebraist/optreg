#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include "accelerate_solver.h"
#include <Eigen/Sparse>

using namespace optreg;

void test_amx_data_types() {
    std::cout << "--- [AMX] Testing Data Types ---" << std::endl;
#ifdef __arm64__
    std::cout << "Platform: arm64" << std::endl;
    __fp16 h1 = 1.0f;
    __fp16 h2 = 2.0f;
    __fp16 h3 = h1 + h2;
    std::cout << "fp16 sum (1.0 + 2.0): " << (float)h3 << std::endl;
    if ((float)h3 == 3.0f) std::cout << "PASS: fp16 arithmetic works." << std::endl;
    // Check Accelerate integer types
#else
    std::cout << "Platform: non-arm64 (skipping fp16)" << std::endl;
#endif
    std::cout << "sizeof(long): " << sizeof(long) << std::endl;
}

void test_amx_solve_accuracy() {
    std::cout << "\n--- [AMX] Testing Sparse Solver Accuracy ---" << std::endl;
    int n = 3;
    Eigen::SparseMatrix<double> A(n, n);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 4.0});
    triplets.push_back({0, 1, 1.0});
    triplets.push_back({1, 0, 1.0});
    triplets.push_back({1, 1, 4.0});
    triplets.push_back({1, 2, 1.0});
    triplets.push_back({2, 1, 1.0});
    triplets.push_back({2, 2, 4.0});
    A.setFromTriplets(triplets.begin(), triplets.end());
    
    Eigen::VectorXd b(n);
    b << 1, 2, 3;
    
    AccelerateSparseSolver solver;
    Eigen::VectorXd x(n);
    bool success = solver.solve(A, b, x);
    
    if (success) {
        std::cout << "[AMX] Solve Result: " << x.transpose() << std::endl;
        // Known solution for this 3x3 system:
        // x0 = 1/14, x1 = 4/14, x2 = 13/14 ? No, let's just check residual.
        Eigen::VectorXd residual = A * x - b;
        double error = residual.norm();
        std::cout << "Solve Residual: " << error << std::endl;
        if (error < 1e-9) std::cout << "PASS: AMX solve accurate." << std::endl;
        else std::cout << "FAIL: AMX solve inaccuracy." << std::endl;
    } else {
        std::cout << "FAIL: AMX solver failed (Check structure/ABI)." << std::endl;
    }
}

void test_dense_solver() {
    std::cout << "\n--- [AMX] Testing Dense Solver Accuracy ---" << std::endl;
    int n = 3;
    Eigen::MatrixXd A(n, n);
    A << 4, 1, 2,
         1, 5, 3,
         2, 3, 6;
    
    Eigen::VectorXd b(n);
    b << 7, 9, 11;
    
    AccelerateDenseSolver solver;
    Eigen::VectorXd x(n);
    bool success = solver.solve(A, b, x);
    
    if (success) {
        std::cout << "[AMX] Dense Result: " << x.transpose() << std::endl;
        Eigen::VectorXd expected = A.partialPivLu().solve(b);
        double error = (x - expected).norm();
        std::cout << "Dense Solve Error vs Eigen: " << error << std::endl;
        if (error < 1e-12) std::cout << "PASS: AMX dense solve accurate." << std::endl;
        else std::cout << "FAIL: AMX dense solve inaccuracy." << std::endl;
    } else {
        std::cout << "FAIL: AMX dense solver failed." << std::endl;
    }
}

int main() {
    try {
        test_amx_data_types();
        test_dense_solver();
        test_amx_solve_accuracy(); // Should work now!
        std::cout << "\nAMX SANITY TESTS COMPLETED SUCCESSFULLY." << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "CRITICAL FAILURE: " << e.what() << std::endl;
        return 1;
    }
    return 0;
}
