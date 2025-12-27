#pragma once

#include "interior_point.h"
#include <Eigen/SVD>
#include <cmath>
#include <optional>

namespace optreg {

// Pre-flight checks before running interior point solver
// Based on formal verification in Agda

enum class LPStatus {
    FEASIBLE_BOUNDED,      // Good to solve
    INFEASIBLE,            // No feasible point
    UNBOUNDED,             // No finite optimum
    ILL_CONDITIONED,       // Numerical issues likely
    BOUNDARY_START         // Starting point not strictly interior
};

struct PreflightResult {
    LPStatus status;
    std::string message;
    double condition_number;  // κ(A) for conditioning check
    bool can_proceed;
};

class LPPrechecker {
public:
    LPPrechecker() 
        : condition_threshold_(1e6)  // κ > 10^6 considered ill-conditioned
        , feasibility_tol_(1e-8)
        , interior_tol_(1e-10)       // x_i > ε to be interior
    {}
    
    // Main precheck function
    PreflightResult check(const LPProblem& problem);
    
    void set_condition_threshold(double thresh) { condition_threshold_ = thresh; }
    void set_feasibility_tolerance(double tol) { feasibility_tol_ = tol; }
    
private:
    double condition_threshold_;
    double feasibility_tol_;
    double interior_tol_;
    
    // Check 1: Is constraint matrix well-conditioned?
    // Corresponds to Agda: WellConditioned vs IllConditioned
    bool check_conditioning(const SparseMatrix& A, double& cond_num);
    
    // Check 2: Is problem feasible?
    // Corresponds to Agda: primal-feasible
    bool check_feasibility(const LPProblem& problem);
    
    // Check 3: Is problem bounded?
    // Corresponds to Agda: unbounded-has-no-optimum
    bool check_boundedness(const LPProblem& problem);
    
    // Check 4: Is starting point strictly interior?
    // Corresponds to Agda: BadStartingPoint
    bool check_interior_start(const Vector& x0);
    
    // Helper: Detect unbounded ray
    std::optional<Vector> find_unbounded_ray(const LPProblem& problem);
    
    // Helper: Phase I for feasibility (find initial feasible point)
    std::optional<Vector> find_initial_feasible(const LPProblem& problem);
};

// Implementation

PreflightResult LPPrechecker::check(const LPProblem& problem) {
    PreflightResult result;
    
    // Check 1: Conditioning (Theorem 1 from NumericalStability.agda)
    double cond_num;
    if (!check_conditioning(problem.A, cond_num)) {
        result.status = LPStatus::ILL_CONDITIONED;
        result.message = "Constraint matrix is ill-conditioned (κ = " + 
                        std::to_string(cond_num) + " > " + 
                        std::to_string(condition_threshold_) + ")";
        result.condition_number = cond_num;
        result.can_proceed = false;
        return result;
    }
    
    result.condition_number = cond_num;
    
    // Check 2: Feasibility (NonConvergence.agda: infeasible-has-no-solution)
    if (!check_feasibility(problem)) {
        result.status = LPStatus::INFEASIBLE;
        result.message = "Problem is infeasible (no point satisfies Ax = b, x ≥ 0)";
        result.can_proceed = false;
        return result;
    }
    
    // Check 3: Boundedness (NonConvergence.agda: unbounded-has-no-optimum)
    if (!check_boundedness(problem)) {
        result.status = LPStatus::UNBOUNDED;
        result.message = "Problem is unbounded (objective can decrease to -∞)";
        result.can_proceed = false;
        return result;
    }
    
    // All checks passed
    result.status = LPStatus::FEASIBLE_BOUNDED;
    result.message = "Problem is well-posed (feasible, bounded, well-conditioned)";
    result.can_proceed = true;
    
    return result;
}

bool LPPrechecker::check_conditioning(const SparseMatrix& A, double& cond_num) {
    if (A.rows() == 0 || A.cols() == 0) {
        cond_num = 1.0;
        return true;
    }
    
    // Compute singular value decomposition for condition number
    // κ(A) = σ_max / σ_min
    Eigen::MatrixXd A_dense{A}; // convert to dense
    Eigen::JacobiSVD<Eigen::MatrixXd> svd{A_dense}; // uniform initialization avoids vexing parse
    auto singular_values = svd.singularValues();
    
    if (singular_values.size() == 0) {
        cond_num = std::numeric_limits<double>::infinity();
        return false;
    }
    
    double sigma_max = singular_values(0);
    double sigma_min = singular_values(singular_values.size() - 1);
    
    // Check for near-singularity
    if (sigma_min < 1e-12) {
        cond_num = std::numeric_limits<double>::infinity();
        return false;
    }
    
    cond_num = sigma_max / sigma_min;
    
    // Corresponds to Agda: κ ≤ threshold
    return cond_num <= condition_threshold_;
}

bool LPPrechecker::check_feasibility(const LPProblem& problem) {
    // Try to find an initial feasible point using Phase I
    // If Phase I succeeds, problem is feasible
    auto x0 = find_initial_feasible(problem);
    return x0.has_value();
}

std::optional<Vector> LPPrechecker::find_initial_feasible(
    const LPProblem& problem
) {
    // Phase I: minimize sum of artificial variables
    // If optimum is 0, original problem is feasible
    
    uint32_t n = problem.c.size();
    uint32_t m = problem.b.size();
    
    if (m == 0) {
        // No constraints, any x ≥ 0 is feasible
        return Vector::Ones(n);
    }
    
    // Create Phase I problem: min Σ a_i
    // subject to Ax + a = b, x ≥ 0, a ≥ 0
    // where a are artificial variables
    
    LPProblem phase1;
    phase1.c = Vector::Zero(n + m);
    phase1.c.tail(m) = Vector::Ones(m);  // objective: minimize artificials
    
    // Solve Phase I (simplified stub - full implementation needed)
    // For now, just check if Ax = b has solutions
    
    Eigen::MatrixXd A_dense(problem.A);
    Eigen::FullPivLU<Eigen::MatrixXd> lu(A_dense);
    
    if (lu.rank() < m) {
        // Underdetermined or inconsistent
        return std::nullopt;
    }
    
    // Try to find a basic feasible solution
    Vector x = lu.solve(problem.b);
    
    // Check if x ≥ 0
    if ((x.array() >= -feasibility_tol_).all()) {
        // Make strictly positive
        return x.cwiseMax(interior_tol_);
    }
    
    return std::nullopt;
}

bool LPPrechecker::check_boundedness(const LPProblem& problem) {
    // Check if there exists an unbounded ray
    // Ray: direction d such that Ad = 0, c^T d < 0
    // If such d exists, objective can decrease indefinitely
    
    auto ray = find_unbounded_ray(problem);
    
    // If ray exists, problem is unbounded
    return !ray.has_value();
}

std::optional<Vector> LPPrechecker::find_unbounded_ray(
    const LPProblem& problem
) {
    // Find direction d: Ad = 0, c^T d < 0
    
    uint32_t n = problem.c.size();
    uint32_t m = problem.b.size();
    
    if (m == 0) {
        // No constraints
        // If any c_i < 0, we have unbounded ray
        for (uint32_t i = 0; i < n; ++i) {
            if (problem.c(i) < -1e-8) {
                Vector d = Vector::Zero(n);
                d(i) = 1.0;
                return d;
            }
        }
        return std::nullopt;
    }
    
    // Find null space of A
    Eigen::MatrixXd A_dense(problem.A);
    Eigen::FullPivLU<Eigen::MatrixXd> lu(A_dense);
    Eigen::MatrixXd nullspace = lu.kernel();
    
    // Check if any null space vector has negative cost
    for (int i = 0; i < nullspace.cols(); ++i) {
        Vector d = nullspace.col(i);
        double cost = problem.c.dot(d);
        
        if (cost < -1e-8) {
            // Found unbounded ray
            return d;
        }
    }
    
    return std::nullopt;
}

bool LPPrechecker::check_interior_start(const Vector& x0) {
    // Check x_i > ε for all i
    // Corresponds to Agda: BadStartingPoint
    return (x0.array() > interior_tol_).all();
}

} // namespace optreg
