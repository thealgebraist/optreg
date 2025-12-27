#include <iostream>
#include "interior_point.h"

using namespace optreg;

int main() {
    // Test 1: Simple 2D LP with known solution
    // min   x + y
    // s.t.  x + y = 1
    //       0 <= x, y <= 1
    // Optimal: x* = y* = 0.5, obj = 1.0
    
    std::cout << "=== Test 1: 2D LP with box constraints ===" << std::endl;
    std::cout << "min x + y s.t. x + y = 1, 0 <= x,y <= 1" << std::endl;
    std::cout << "Expected: x* = y* = 0.5, obj* = 1.0" << std::endl << std::endl;
    
    LPProblem prob1;
    prob1.c.resize(2);
    prob1.c << 1.0, 1.0;
    
    prob1.A.resize(1, 2);
    std::vector<Eigen::Triplet<double>> triplets;
    triplets.push_back({0, 0, 1.0});
    triplets.push_back({0, 1, 1.0});
    prob1.A.setFromTriplets(triplets.begin(), triplets.end());
    
    prob1.b.resize(1);
    prob1.b << 1.0;
    
    prob1.lower_bound.resize(2);
    prob1.lower_bound << 0.0, 0.0;
    
    prob1.upper_bound.resize(2);
    prob1.upper_bound << 1.0, 1.0;
    
    InteriorPointSolver solver;
    solver.set_verbose(true);
    solver.set_max_iterations(20);  // Reduce for debugging
    solver.set_tolerance(1e-6);
    
    LPSolution sol1 = solver.solve(prob1);
    
    std::cout << "\nResult:" << std::endl;
    std::cout << "  Converged: " << (sol1.optimal ? "YES" : "NO") << std::endl;
    std::cout << "  Iterations: " << sol1.iterations << std::endl;
    if (sol1.optimal) {
        std::cout << "  x = " << sol1.x(0) << std::endl;
        std::cout << "  y = " << sol1.x(1) << std::endl;
        std::cout << "  Objective: " << sol1.objective << std::endl;
        
        double error = std::abs(sol1.x(0) - 0.5) + std::abs(sol1.x(1) - 0.5) + std::abs(sol1.objective - 1.0);
        std::cout << "  Error: " << error << std::endl;
        
        if (error < 1e-4) {
            std::cout << "  ✓ TEST PASSED" << std::endl;
        } else {
            std::cout << "  ✗ TEST FAILED" << std::endl;
        }
    } else {
        std::cout << "  ✗ TEST FAILED (no convergence)" << std::endl;
    }
    
    return 0;
}
