#include <iostream>
#include "accelerate_solver.h"
#include <Eigen/Sparse>
#include <Eigen/Dense>
#include <vector>

using namespace optreg;

int main() {
    std::cout << "Testing AMX (Accelerate) vs Eigen Solver..." << std::endl;

    // Simple 3x3 system
    // [ 4  1  0 ] [ x0 ]   [ 1 ]
    // [ 1  4  1 ] [ x1 ] = [ 2 ]
    // [ 0  1  4 ] [ x2 ]   [ 3 ]
    // Solution should be easy to find. symmetric pos def.

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
    A.makeCompressed();

    Eigen::VectorXd b(n);
    b << 1, 2, 3;

    Eigen::VectorXd x_amx(n);
    Eigen::VectorXd x_eigen(n);

    // 1. Eigen Solver (SimplicialLLT for SPD)
    {
        std::cout << "[Eigen] Solving..." << std::endl;
        Eigen::SimplicialLLT<Eigen::SparseMatrix<double>> solver;
        solver.compute(A);
        if(solver.info() != Eigen::Success) {
            std::cout << "[Eigen] Factorization failed." << std::endl;
        } else {
            x_eigen = solver.solve(b);
            std::cout << "[Eigen] Result: " << x_eigen.transpose() << std::endl;
        }
    }

    // 2. AMX (Accelerate) Solver
    {
        std::cout << "[AMX] Solving..." << std::endl;
        AccelerateSparseSolver solver;
        bool success = solver.solve(A, b, x_amx);
        if (success) {
            std::cout << "[AMX] Result: " << x_amx.transpose() << std::endl;
        } else {
            std::cout << "[AMX] Failed." << std::endl;
        }
    }

    // Compare
    double error = (x_amx - x_eigen).norm();
    std::cout << "Difference norm: " << error << std::endl;
    if (error < 1e-9) std::cout << "PASS" << std::endl;
    else std::cout << "FAIL" << std::endl;

    return 0;
}
