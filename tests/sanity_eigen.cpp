#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include <Eigen/Sparse>
#include <Eigen/Dense>
#include "interior_point.h"
#include "gradient_descent.h"

using namespace optreg;

void test_eigen_data_types() {
    std::cout << "--- [Eigen] Testing Data Types ---" << std::endl;
    float f32 = 1.0f / 3.0f;
    double f64 = 1.0 / 3.0;
    std::cout << "f32: " << std::setprecision(10) << f32 << std::endl;
    std::cout << "f64: " << std::setprecision(10) << f64 << std::endl;
    
    int32_t i32 = 2147483647;
    int64_t i64 = 2147483647LL + 1LL;
    std::cout << "i32 max: " << i32 << std::endl;
    std::cout << "i64 max+1: " << i64 << std::endl;
    
    if (i64 > i32) std::cout << "PASS: i64 correctly holds larger value." << std::endl;
}

void test_eigen_matrix_ops() {
    std::cout << "\n--- [Eigen] Testing Matrix-Vector Operations ---" << std::endl;
    int n = 100;
    Eigen::SparseMatrix<double> A(n, n);
    A.setIdentity();
    A *= 2.0;

    Eigen::VectorXd x = Eigen::VectorXd::Random(n);
    Eigen::VectorXd y = A * x;

    double error = (y - 2.0 * x).norm();
    std::cout << "Sparse SpMV error: " << error << std::endl;
    if (error < 1e-12) std::cout << "PASS: Matrix-vector product correct." << std::endl;
}

void test_eigen_gd_stability() {
    std::cout << "\n--- [Eigen] Testing Gradient Descent Stability ---" << std::endl;
    LPProblem problem;
    int n = 4;
    problem.c = Eigen::VectorXd::Ones(n);
    problem.A.resize(1, n);
    problem.A.insert(0, 0) = 1.0;
    problem.A.insert(0, 1) = 1.0;
    problem.A.insert(0, 2) = 1.0;
    problem.A.insert(0, 3) = 1.0;
    problem.b.resize(1);
    problem.b[0] = 1.0;
    problem.lower_bound = Eigen::VectorXd::Zero(n);
    problem.upper_bound = Eigen::VectorXd::Constant(n, 1.0);

    GradientDescentSolver solver;
    solver.set_max_iters(1000);
    solver.set_rho(10.0);
    solver.set_learning_rate(0.01);
    
    LPSolution sol = solver.solve(problem);
    
    std::cout << "GD Objective: " << sol.objective << std::endl;
    std::cout << "GD Solution sum: " << sol.x.sum() << " (expected ~1.0)" << std::endl;
    
    if (std::abs(sol.x.sum() - 1.0) < 0.1) {
        std::cout << "PASS: GD converged to feasible region." << std::endl;
    }
}

int main() {
    try {
        test_eigen_data_types();
        test_eigen_matrix_ops();
        test_eigen_gd_stability();
        std::cout << "\nEIGEN SANITY TESTS COMPLETED SUCCESSFULLY." << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "CRITICAL FAILURE: " << e.what() << std::endl;
        return 1;
    }
    return 0;
}
