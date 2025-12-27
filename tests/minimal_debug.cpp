#include <iostream>
#include "interior_point.h"

using namespace optreg;

int main() {
    // Minimal test: 2D Box LP
    std::cout << "=== Minimal Debug Test: 2D Box LP ===" << std::endl;
    
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
    solver.set_verbose(true);
    solver.set_max_iterations(10);
    solver.set_tolerance(1e-4);
    
    std::cout << "\nCalling solve()..." << std::endl;
    LPSolution sol = solver.solve(prob);
    
    std::cout << "\n=== Result ===" << std::endl;
    std::cout << "Converged: " << (sol.optimal ? "YES" : "NO") << std::endl;
    std::cout << "Iterations: " << sol.iterations << std::endl;
    if (sol.x.size() > 0) {
        std::cout << "x = [" << sol.x(0) << ", " << sol.x(1) << "]" << std::endl;
        std::cout << "Objective: " << sol.objective << std::endl;
    }
    
    return sol.optimal ? 0 : 1;
}
