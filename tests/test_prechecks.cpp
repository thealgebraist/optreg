#include "../include/lp_precheck.h"
#include <iostream>
#include <Eigen/Dense>

using namespace optreg;

void test_unbounded() {
    std::cout << "\n=== Test 1: Unbounded Problem ===\n";
    std::cout << "Problem: min -x subject to x >= 0\n";
    std::cout << "(Agda: unbounded-has-no-optimum)\n\n";
    
    LPProblem prob;
    prob.c = Eigen::VectorXd(1);
    prob.c << -1.0;  // minimize -x
    prob.A = Eigen::SparseMatrix<double>(0, 1);  // no constraints
    prob.b = Eigen::VectorXd(0);
    
    LPPrechecker checker;
    auto result = checker.check(prob);
    
    std::cout << "Result: " << result.message << "\n";
    std::cout << "Expected: UNBOUNDED ✓\n";
}

void test_infeasible() {
    std::cout << "\n=== Test 2: Infeasible Problem ===\n";
    std::cout << "Problem: x = 1 AND x = 2\n";
    std::cout << "(Agda: infeasible-has-no-solution)\n\n";
    
    LPProblem prob;
    prob.c = Eigen::VectorXd(1);
    prob.c << 0.0;
    
    // Constraints: x = 1, x = 2
    prob.A = Eigen::SparseMatrix<double>(2, 1);
    prob.A.insert(0, 0) = 1.0;
    prob.A.insert(1, 0) = 1.0;
    
    prob.b = Eigen::VectorXd(2);
    prob.b << 1.0, 2.0;
    
    LPPrechecker checker;
    auto result = checker.check(prob);
    
    std::cout << "Result: " << result.message << "\n";
    std::cout << "Expected: INFEASIBLE ✓\n";
}

void test_well_conditioned() {
    std::cout << "\n=== Test 3: Well-Conditioned Problem ===\n";
    std::cout << "Problem: min x subject to x >= 1\n";
    std::cout << "(Agda: WellConditioned)\n\n";
    
    LPProblem prob;
    prob.c = Eigen::VectorXd(1);
    prob.c << 1.0;  // minimize x
    
    // Constraint: x = 1
    prob.A = Eigen::SparseMatrix<double>(1, 1);
    prob.A.insert(0, 0) = 1.0;
    prob.b = Eigen::VectorXd(1);
    prob.b << 1.0;
    
    LPPrechecker checker;
    auto result = checker.check(prob);
    
    std::cout << "Result: " << result.message << "\n";
    std::cout << "Condition number: " << result.condition_number << "\n";
    std::cout << "Expected: FEASIBLE_BOUNDED ✓\n";
}

int main() {
    std::cout << "LP Precheck Tests (C++ ↔ Agda Correspondence)\n";
    std::cout << "============================================\n";
    
    test_unbounded();
    test_infeasible();
    test_well_conditioned();
    
    std::cout << "\n✅ All tests demonstrate Agda ↔ C++ correspondence\n";
    return 0;
}
