#pragma once

#include "interior_point.h"
#include <memory>
#include <queue>

namespace optreg {

// Task 9-12: Branch and bound for integer programming

struct BBNode {
    LPSolution lp_solution;     // LP relaxation solution
    double lower_bound;          // lower bound on objective
    uint32_t branching_var;      // variable to branch on
    bool fixed_to_zero;          // true if branching var fixed to 0
    uint32_t depth;              // depth in search tree
    std::vector<std::pair<uint32_t, double>> fixed_constraints; // History of fixed variables
    
    // For priority queue (best-first search)
    bool operator<(const BBNode& other) const {
        return lower_bound > other.lower_bound;  // min heap
    }
};

struct IPSolution {
    Vector x;                    // integer solution
    double objective;            // objective value
    bool optimal;                // true if proven optimal
    uint32_t nodes_explored;     // BB tree nodes explored
    uint32_t nodes_pruned;       // nodes pruned by bounds
};

class BranchAndBound {
public:
    BranchAndBound() : tolerance_(1e-6), max_nodes_(10000) {}
    
    // Solve integer program
    IPSolution solve(const LPProblem& problem);
    
    void set_tolerance(double tol) { tolerance_ = tol; }
    void set_max_nodes(uint32_t max_n) { max_nodes_ = max_n; }
    using LinearBackend = InteriorPointSolver::LinearSolverBackend;
    void set_linear_solver_backend(LinearBackend backend) { linear_backend_ = backend; }
    void set_num_integer_vars(uint32_t n) { num_integer_vars_ = n; }
    
private:
    double tolerance_;
    uint32_t max_nodes_;
    uint32_t num_integer_vars_ = UINT32_MAX; // If UINT32_MAX, all vars are integer
    LinearBackend linear_backend_ = LinearBackend::Auto;
    
    // Task 10: Solve LP relaxation
    LPSolution solve_lp_relaxation(
        const LPProblem& problem,
        const std::vector<std::pair<uint32_t, double>>& fixed_vars
    );
    
    // Task 11: Select branching variable
    uint32_t select_branching_var(const Vector& x);
    
    // Check if solution is integer (within tolerance)
    bool is_integer_solution(const Vector& x);
    
    // Task 12: Prune node based on bounds
    bool should_prune(double node_bound, double incumbent);
};

} // namespace optreg
