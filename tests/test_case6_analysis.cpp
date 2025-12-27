#include <iostream>
#include <cassert>
#include "interior_point.h"

using namespace optreg;

// Test different initializations for Case 6
void test_case6_midpoint() {
    std::cout << "=== Case 6.1: Midpoint Init (Expected: FAIL) ===" << std::endl;
    
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
    
    std::cout << "Result: " << (sol.optimal ? "PASS" : "FAIL") << std::endl;
    if (sol.x.size() > 0) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << ", " << sol.x(2) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << " (expected: 2)" << std::endl;
    }
    std::cout << "  (Midpoint [0.67, 0.67, 0.67] fails due to centering force)" << std::endl;
}

void test_case6_weighted_init() {
    std::cout << "\n=== Case 6.2: Weighted Init (Expected: PASS) ===" << std::endl;
    std::cout << "Using x₀ = [1.5, 0.3, 0.2] (biased toward low-cost x)" << std::endl;
    
    // TODO: Need to modify solver to accept custom initialization
    std::cout << "  SKIPPED: Requires custom init support" << std::endl;
}

void test_case6_relaxed_tolerance() {
    std::cout << "\n=== Case 6.3: Relaxed Tolerance (Test Convergence) ===" << std::endl;
    
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
    solver.set_max_iterations(100);
    solver.set_tolerance(0.1);  // Much more relaxed
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "PASS" : "FAIL") << std::endl;
    if (sol.x.size() > 0) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << ", " << sol.x(2) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << std::endl;
        
        // Check if close to analytic center
        double dist_to_center = std::abs(sol.x(0) - 0.67) + 
                                std::abs(sol.x(1) - 0.67) + 
                                std::abs(sol.x(2) - 0.67);
        std::cout << "  Distance to center [0.67,0.67,0.67]: " << dist_to_center << std::endl;
    }
}

void test_case6_small_bounds() {
    std::cout << "\n=== Case 6.4: With Upper Bounds (Force Corner) ===" << std::endl;
    
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
    prob.upper_bound << 2.0, 0.5, 0.5;  // Force y,z to be small
    
    InteriorPointSolver solver;
    solver.set_max_iterations(50);
    solver.set_tolerance(1e-4);
    
    LPSolution sol = solver.solve(prob);
    
    std::cout << "Result: " << (sol.optimal ? "PASS" : "FAIL") << std::endl;
    if (sol.x.size() > 0) {
        std::cout << "  x = [" << sol.x(0) << ", " << sol.x(1) << ", " << sol.x(2) << "]" << std::endl;
        std::cout << "  obj = " << sol.objective << " (expected: ~2)" << std::endl;
    }
}

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "Case 6 Analysis: 4 Different Tests" << std::endl;
    std::cout << "========================================" << std::endl;
    
    test_case6_midpoint();
    test_case6_weighted_init();
    test_case6_relaxed_tolerance();
    test_case6_small_bounds();
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Analysis: Barrier method converges to" << std::endl;
    std::cout << "analytic center, not LP optimum when" << std::endl;
    std::cout << "optimum is at boundary (y=z=0)." << std::endl;
    std::cout << "========================================" << std::endl;
    
    return 0;
}
