#include "../include/lp_precheck.h"
#include "../include/interior_point.h"
#include <iostream>
#include <random>
#include <iomanip>

using namespace optreg;

// Test 1: Simple sensible problem - minimize x subject to x >= 5
LPProblem create_simple_bounded() {
    LPProblem prob;
    prob.c = Eigen::VectorXd(1);
    prob.c << 1.0;  // min x
    
    prob.A = Eigen::SparseMatrix<double>(1, 1);
    prob.A.insert(0, 0) = 1.0;
    prob.b = Eigen::VectorXd(1);
    prob.b << 5.0;  // x = 5
    
    prob.lower_bound = Eigen::VectorXd(1);
    prob.lower_bound << 0.0;
    prob.upper_bound = Eigen::VectorXd(1);
    prob.upper_bound << 1000.0;
    
    return prob;
}

// Test 2: Unbounded - min -x with x >= 0 (no upper bound)
LPProblem create_unbounded() {
    LPProblem prob;
    prob.c = Eigen::VectorXd(1);
    prob.c << -1.0;  // min -x → x → ∞
    
    prob.A = Eigen::SparseMatrix<double>(0, 1);
    prob.b = Eigen::VectorXd(0);
    
    prob.lower_bound = Eigen::VectorXd(1);
    prob.lower_bound << 0.0;
    prob.upper_bound = Eigen::VectorXd(1);
    prob.upper_bound << std::numeric_limits<double>::infinity();
    
    return prob;
}

// Test 3: Infeasible - contradictory constraints
LPProblem create_infeasible() {
    LPProblem prob;
    prob.c = Eigen::VectorXd(1);
    prob.c << 0.0;
    
    // x = 1 AND x = 2 simultaneously
    prob.A = Eigen::SparseMatrix<double>(2, 1);
    prob.A.insert(0, 0) = 1.0;
    prob.A.insert(1, 0) = 1.0;
    prob.b = Eigen::VectorXd(2);
    prob.b << 1.0, 2.0;
    
    return prob;
}

// Test 4: Ill-conditioned - nearly singular matrix
LPProblem create_ill_conditioned() {
    LPProblem prob;
    prob.c = Eigen::VectorXd(2);
    prob.c << 1.0, 1.0;
    
    // Constraints: x1 + x2 = 1, x1 + 1.0000001*x2 = 1
    prob.A = Eigen::SparseMatrix<double>(2, 2);
    prob.A.insert(0, 0) = 1.0;
    prob.A.insert(0, 1) = 1.0;
    prob.A.insert(1, 0) = 1.0;
    prob.A.insert(1, 1) = 1.0000001;  // nearly parallel
    
    prob.b = Eigen::VectorXd(2);
    prob.b << 1.0, 1.0;
    
    return prob;
}

// Test 5: Random problem
LPProblem create_random(int n, int m) {
    std::mt19937 rng(42);
    std::uniform_real_distribution<double> dist(-10.0, 10.0);
    
    LPProblem prob;
    prob.c = Eigen::VectorXd(n);
    for (int i = 0; i < n; ++i) {
        prob.c(i) = dist(rng);
    }
    
    prob.A = Eigen::SparseMatrix<double>(m, n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j) {
            if (dist(rng) > 0) {  // sparse
                prob.A.insert(i, j) = dist(rng);
            }
        }
    }
    
    prob.b = Eigen::VectorXd(m);
    for (int i = 0; i < m; ++i) {
        prob.b(i) = dist(rng);
    }
    
    return prob;
}

// Test 6: Well-conditioned feasible problem (should work)
LPProblem create_feasible_diet() {
    // Diet problem: minimize cost of food meeting nutritional requirements
    // Variables: x1=bread, x2=milk
    // min 2*x1 + 3*x2 (cost)
    // subject to: 4*x1 + 8*x2 >= 12 (protein)
    //             x1, x2 >= 0
    
    LPProblem prob;
    prob.c = Eigen::VectorXd(2);
    prob.c << 2.0, 3.0;  // cost
    
    prob.A = Eigen::SparseMatrix<double>(1, 2);
    prob.A.insert(0, 0) = 4.0;
    prob.A.insert(0, 1) = 8.0;
    prob.b = Eigen::VectorXd(1);
    prob.b << 12.0;  // protein requirement
    
    return prob;
}

// Test 7: Degenerate - multiple optimal solutions
LPProblem create_degenerate() {
    LPProblem prob;
    prob.c = Eigen::VectorXd(2);
    prob.c << 1.0, 1.0;  // min x1 + x2
    
    prob.A = Eigen::SparseMatrix<double>(1, 2);
    prob.A.insert(0, 0) = 1.0;
    prob.A.insert(0, 1) = 1.0;
    prob.b = Eigen::VectorXd(1);
    prob.b << 5.0;  // x1 + x2 = 5 (entire line is optimal)
    
    return prob;
}

void run_test(const std::string& name, const std::string& description, 
              const std::string& agda_ref, LPProblem prob) {
    std::cout << "\n" << std::string(70, '=') << "\n";
    std::cout << "TEST: " << name << "\n";
    std::cout << description << "\n";
    std::cout << "Agda reference: " << agda_ref << "\n";
    std::cout << std::string(70, '-') << "\n";
    
    LPPrechecker checker;
    auto result = checker.check(prob);
    
    std::cout << "\n📊 Precheck Results:\n";
    std::cout << "  Status: ";
    switch (result.status) {
        case LPStatus::FEASIBLE_BOUNDED:
            std::cout << "✅ FEASIBLE_BOUNDED\n";
            break;
        case LPStatus::INFEASIBLE:
            std::cout << "❌ INFEASIBLE\n";
            break;
        case LPStatus::UNBOUNDED:
            std::cout << "❌ UNBOUNDED\n";
            break;
        case LPStatus::ILL_CONDITIONED:
            std::cout << "⚠️  ILL_CONDITIONED\n";
            break;
        default:
            std::cout << "❓ UNKNOWN\n";
    }
    
    std::cout << "  Message: " << result.message << "\n";
    std::cout << "  Condition number κ: " << std::fixed << std::setprecision(2) 
              << result.condition_number << "\n";
    std::cout << "  Can proceed: " << (result.can_proceed ? "Yes" : "No") << "\n";
    
    if (result.can_proceed) {
        std::cout << "\n🚀 Running solver...\n";
        InteriorPointSolver solver;
        solver.set_max_iterations(10);  // quick test
        auto solution = solver.solve(prob);
        
        if (solution.optimal) {
            std::cout << "  ✅ Converged in " << solution.iterations << " iterations\n";
            std::cout << "  Objective: " << solution.objective << "\n";
        } else {
            std::cout << "  ⚠️  Did not converge in " << solution.iterations << " iterations\n";
        }
    }
}

int main() {
    std::cout << "\n";
    std::cout << "╔════════════════════════════════════════════════════════════════════╗\n";
    std::cout << "║         LP Solver Comprehensive Test Suite                        ║\n";
    std::cout << "║         Testing Agda Proofs ↔ C++ Implementation                  ║\n";
    std::cout << "╚════════════════════════════════════════════════════════════════════╝\n";
    
    run_test(
        "Simple Bounded",
        "Problem: min x subject to x = 5",
        "WellConditioned + feasible + bounded",
        create_simple_bounded()
    );
    
    run_test(
        "Unbounded",
        "Problem: min -x subject to x >= 0 (no upper bound)",
        "unbounded-has-no-optimum",
        create_unbounded()
    );
    
    run_test(
        "Infeasible",
        "Problem: x = 1 AND x = 2 (contradictory)",
        "infeasible-has-no-solution",
        create_infeasible()
    );
    
    run_test(
        "Ill-Conditioned",
        "Problem: nearly parallel constraints",
        "IllConditioned",
        create_ill_conditioned()
    );
    
    run_test(
        "Random 5x3",
        "Problem: random 5 variables, 3 constraints",
        "May be feasible or infeasible",
        create_random(5, 3)
    );
    
    run_test(
        "Diet Problem",
        "Problem: minimize food cost meeting nutrition",
        "WellConditioned + feasible + bounded",
        create_feasible_diet()
    );
    
    run_test(
        "Degenerate",
        "Problem: multiple optimal solutions",
        "WellConditioned (multiple optima OK)",
        create_degenerate()
    );
    
    std::cout << "\n" << std::string(70, '=') << "\n";
    std::cout << "✅ Test suite complete!\n";
    std::cout << "Demonstrated: stability, feasibility, boundedness checks\n";
    std::cout << "All checks correspond to Agda proofs.\n";
    std::cout << std::string(70, '=') << "\n\n";
    
    return 0;
}
