#include "tsp_solver.h"
#include "tsplib_parser.h"
#include "branch_bound.h"
#include <iostream>

using namespace optreg;

int main() {
    // Small 5-node instance for debugging
    TSPInstance instance;
    instance.dimension = 5;
    instance.adj.resize(5, std::vector<double>(5, 0));
    
    // Create a simple distance matrix
    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            if (i == j) instance.adj[i][j] = 0;
            else instance.adj[i][j] = std::abs(i - j) * 10 + (i + j) % 3;
        }
    }
    
    std::cout << "=== Testing TSP Formulation on K5 ===" << std::endl;
    std::cout << "Distance matrix:" << std::endl;
    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            std::cout << instance.adj[i][j] << " ";
        }
        std::cout << std::endl;
    }
    
    TSPSolver tsp_solver;
    LPProblem prob = tsp_solver.formulate_ip(instance);
    
    std::cout << "\nLP Problem Stats:" << std::endl;
    std::cout << "  Variables: " << prob.c.size() << std::endl;
    std::cout << "  Constraints: " << prob.b.size() << std::endl;
    std::cout << "  Nonzeros in A: " << prob.A.nonZeros() << std::endl;
    
    // Try to solve it directly
    InteriorPointSolver ip_solver;
    ip_solver.set_verbose(true);
    ip_solver.set_max_iterations(500);
    ip_solver.set_tolerance(1e-5);
    ip_solver.set_linear_solver_backend(InteriorPointSolver::LinearSolverBackend::EigenSparse);
    
    std::cout << "\n=== Solving LP Relaxation ===" << std::endl;
    LPSolution sol = ip_solver.solve(prob);
    
    std::cout << "\nResult:" << std::endl;
    std::cout << "  Optimal: " << (sol.optimal ? "YES" : "NO") << std::endl;
    std::cout << "  Iterations: " << sol.iterations << std::endl;
    if (sol.optimal) {
        std::cout << "  Objective: " << sol.objective << std::endl;
    }
    
    return 0;
}
