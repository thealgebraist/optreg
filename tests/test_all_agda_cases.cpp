#include <iostream>
#include <cassert>
#include <cmath>
#include "interior_point.h"

using namespace optreg;

// Test utilities
bool approx_equal(double a, double b, double tol = 1e-3) {
    return std::abs(a - b) < tol;
}

bool vector_approx_equal(const Vector& a, const Vector& b, double tol = 1e-3) {
    if (a.size() != b.size()) return false;
    for (int i = 0; i < a.size(); ++i) {
        if (!approx_equal(a(i), b(i), tol)) return false;
    }
    return true;
}

// CASE 1: 2D Box LP (Should Work with Pure Barrier)
bool test_case1_2d_box() {
    std::cout << "\n=== Case 1: 2D Box LP ===" << std::endl;
    std::cout << "min x + y s.t. x + y = 1, 0 <= x,y <= 1" << std::endl;
    
    LPProblem prob;
    prob.c.resize(2);
    prob.c << 1.0, 1.0;
    
    prob.A.resize(1, 2);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 1.0});
    triplets.push_back({0, 1, 1.0});
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob.b.resize(1);
    prob.b << 1.0;
    
    prob.lower_bound.resize(2);
    prob.lower_bound << 0.0, 0.0;
    
    prob.upper_bound.resize(2);
    prob.upper_bound << 1.0, 1.0;
    
    InteriorPointSolver solver;
    solver.set_max_iterations(50);
    solver.set_tolerance(1e-4);
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "CONVERGED" : "FAILED") << std::endl;
    if (sol.optimal) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << std::endl;
    }
    
    return sol.optimal && approx_equal(sol.objective, 1.0, 0.1);
}

// CASE 2: 1D Trivial (Should Always Work)
bool test_case2_1d_trivial() {
    std::cout << "\n=== Case 2: 1D Trivial ===" << std::endl;
    std::cout << "min x s.t. x = 0.5, 0 <= x <= 1" << std::endl;
    
    LPProblem prob;
    prob.c.resize(1);
    prob.c << 1.0;
    
    prob.A.resize(1, 1);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 1.0});
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob.b.resize(1);
    prob.b << 0.5;
    
    prob.lower_bound.resize(1);
    prob.lower_bound << 0.0;
    
    prob.upper_bound.resize(1);
    prob.upper_bound << 1.0;
    
    InteriorPointSolver solver;
    solver.set_max_iterations(20);
    solver.set_tolerance(1e-6);
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "CONVERGED" : "FAILED") << std::endl;
    if (sol.optimal) {
        std::cout << "  x = " << sol.x(0) << std::endl;
        std::cout << "  obj = " << sol.objective << std::endl;
    }
    
    return sol.optimal && approx_equal(sol.x(0), 0.5, 0.01);
}

// CASE 3: Unbounded from Above (Should Work)
bool test_case3_unbounded_above() {
    std::cout << "\n=== Case 3: Unbounded from Above ===" << std::endl;
    std::cout << "min x + y s.t. x + y = 2, x,y >= 0 (no upper)" << std::endl;
    
    LPProblem prob;
    prob.c.resize(2);
    prob.c << 1.0, 1.0;
    
    prob.A.resize(1, 2);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 1.0});
    triplets.push_back({0, 1, 1.0});
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob.b.resize(1);
    prob.b << 2.0;
    
    prob.lower_bound.resize(2);
    prob.lower_bound << 0.0, 0.0;
    
    prob.upper_bound.resize(2);
    prob.upper_bound << 1e15, 1e15;
    
    InteriorPointSolver solver;
    solver.set_max_iterations(50);
    solver.set_tolerance(1e-5);
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "CONVERGED" : "FAILED") << std::endl;
    if (sol.optimal) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << std::endl;
    }
    
    return sol.optimal && approx_equal(sol.objective, 2.0, 0.1);
}

// CASE 4: Tight Bounds (Challenging)
bool test_case4_tight_bounds() {
    std::cout << "\n=== Case 4: Tight Bounds ===" << std::endl;
    std::cout << "min x + y s.t. x + y = 1, 0.49 <= x,y <= 0.51" << std::endl;
    
    LPProblem prob;
    prob.c.resize(2);
    prob.c << 1.0, 1.0;
    
    prob.A.resize(1, 2);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 1.0});
    triplets.push_back({0, 1, 1.0});
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob.b.resize(1);
    prob.b << 1.0;
    
    prob.lower_bound.resize(2);
    prob.lower_bound << 0.49, 0.49;
    
    prob.upper_bound.resize(2);
    prob.upper_bound << 0.51, 0.51;
    
    InteriorPointSolver solver;
    solver.set_max_iterations(100);
    solver.set_tolerance(1e-4);
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "CONVERGED" : "FAILED") << std::endl;
    if (sol.optimal) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << std::endl;
    }
    
    return sol.optimal && approx_equal(sol.objective, 1.0, 0.1);
}

// CASE 6: 3-Variable LP (Should Work - No Upper Bounds)
bool test_case6_3var_lp() {
    std::cout << "\n=== Case 6: 3-Variable LP ===" << std::endl;
    std::cout << "min x + 2y + 3z s.t. x + y + z = 2, x,y,z >= 0" << std::endl;
    
    LPProblem prob;
    prob.c.resize(3);
    prob.c << 1.0, 2.0, 3.0;
    
    prob.A.resize(1, 3);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 1.0});
    triplets.push_back({0, 1, 1.0});
    triplets.push_back({0, 2, 1.0});
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob.b.resize(1);
    prob.b << 2.0;
    
    prob.lower_bound.resize(3);
    prob.lower_bound << 0.0, 0.0, 0.0;
    
    prob.upper_bound.resize(3);
    prob.upper_bound << 1e15, 1e15, 1e15;
    
    InteriorPointSolver solver;
    solver.set_max_iterations(50);
    solver.set_tolerance(1e-5);
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "CONVERGED" : "FAILED") << std::endl;
    if (sol.optimal) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << ", " << sol.x(2) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << std::endl;
    }
    
    // Optimal: x=2, y=z=0, obj=2
    return sol.optimal && approx_equal(sol.objective, 2.0, 0.1);
}

// CASE 8: Multiple Optimal Solutions (Zero Objective)
bool test_case8_multiple_optima() {
    std::cout << "\n=== Case 8: Multiple Optima ===" << std::endl;
    std::cout << "min 0 s.t. x + y = 1, 0 <= x,y <= 1" << std::endl;
    
    LPProblem prob;
    prob.c.resize(2);
    prob.c << 0.0, 0.0;  // Zero objective!
    
    prob.A.resize(1, 2);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 1.0});
    triplets.push_back({0, 1, 1.0});
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob.b.resize(1);
    prob.b << 1.0;
    
    prob.lower_bound.resize(2);
    prob.lower_bound << 0.0, 0.0;
    
    prob.upper_bound.resize(2);
    prob.upper_bound << 1.0, 1.0;
    
    InteriorPointSolver solver;
    solver.set_max_iterations(50);
    solver.set_tolerance(1e-4);
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "CONVERGED" : "FAILED") << std::endl;
    if (sol.optimal) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << std::endl;
        std::cout << "  (Should find analytic center ~[0.5, 0.5])" << std::endl;
    }
    
    return sol.optimal && approx_equal(sol.objective, 0.0, 0.01);
}

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "Interior Point Solver: Unit Tests" << std::endl;
    std::cout << "Testing Pure Barrier Method on Agda Cases" << std::endl;
    std::cout << "========================================" << std::endl;
    
    int passed = 0;
    int total = 0;
    
    #define RUN_TEST(test) do { \
        total++; \
        if (test()) { \
            std::cout << "✓ PASSED" << std::endl; \
            passed++; \
        } else { \
            std::cout << "✗ FAILED" << std::endl; \
        } \
    } while(0)
    
    RUN_TEST(test_case1_2d_box);
    RUN_TEST(test_case2_1d_trivial);
    RUN_TEST(test_case3_unbounded_above);
    RUN_TEST(test_case4_tight_bounds);
    RUN_TEST(test_case6_3var_lp);
    RUN_TEST(test_case8_multiple_optima);
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Summary: " << passed << "/" << total << " tests passed" << std::endl;
    std::cout << "========================================" << std::endl;
    
    return (passed == total) ? 0 : 1;
}
