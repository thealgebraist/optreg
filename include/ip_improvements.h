#pragma once
#include <Eigen/Sparse>
#include <vector>
#include <memory>

namespace ip_improvements {

// ==============================================
// IMPROVEMENT 1: Sparse Factorization (Agda proof 1a, 1b)
// ==============================================

class SparseFactorization {
public:
    // Corresponds to Agda: proof-sparse-1a-amd
    explicit SparseFactorization(const Eigen::SparseMatrix<double>& A);
    
    // AMD (Approximate Minimum Degree) ordering
    // Agda: ordering = AMD-fill-reducing
    void compute_amd_ordering();
    
    // Symbolic factorization (structure only)
    // Agda: identifies sparsity pattern
    void symbolic_factorize();
    
    // Numeric factorization
    // Agda: operations = O(nnz * sqrt(n))
    void numeric_factorize();
    
    // Solve Ax = b
    // Agda: solve-correct
    Eigen::VectorXd solve(const Eigen::VectorXd& b);
    
    // Get statistics
    size_t get_nnz() const { return nnz_; }
    size_t get_fill_in() const { return fill_in_; }
    
private:
    Eigen::SparseMatrix<double> A_;
    Eigen::SimplicialLDLT<Eigen::SparseMatrix<double>> solver_;
    size_t nnz_;
    size_t fill_in_;
};

// ==============================================
// IMPROVEMENT 2: Mehrotra Predictor-Corrector (Agda proof 2a, 2b)
// ==============================================

struct PDState {
    Eigen::VectorXd x;  // Primal
    Eigen::VectorXd y;  // Dual (equality)
    Eigen::VectorXd s;  // Dual (inequality)
    double mu;          // Barrier parameter
    
    // Agda: posX, posS invariants
    bool is_strictly_feasible() const;
};

struct Direction {
    Eigen::VectorXd dx;
    Eigen::VectorXd dy;
    Eigen::VectorXd ds;
};

class MehrotraPC {
public:
    // Corresponds to Agda: proof-mehrotra-2a-adaptive
    Direction compute_affine_scaling_direction(const PDState& state);
    
    // Agda: σ = (gap-affine / gap-current)³
    double compute_centering_parameter(const PDState& state, 
                                       const Direction& affine_dir);
    
    // Agda: proof-mehrotra-2b-correction
    Direction compute_corrector_direction(const PDState& state,
                                         const Direction& affine_dir,
                                         double sigma);
    
    // Full predictor-corrector step
    // Agda: predictorCorrector
    PDState iterate(const PDState& state);
    
private:
    double compute_duality_gap(const PDState& state) const;
    double compute_step_size(const PDState& state, const Direction& dir) const;
};

// ==============================================
// IMPROVEMENT 3: KKT Regularization (Agda proof 3a, 3b)
// ==============================================

class KKTRegularization {
public:
    // Corresponds to Agda: proof-reg-3a-adaptive
    static double compute_adaptive_regularization(
        const Eigen::SparseMatrix<double>& KKT);
    
    // Agda: condition-number (KKT + δI) < 10¹⁰
    static Eigen::SparseMatrix<double> apply_regularization(
        const Eigen::SparseMatrix<double>& KKT,
        double delta);
    
    // Agda: proof-reg-3b-inertia
    struct InertiaInfo {
        int num_positive;
        int num_negative;
        int num_zero;
    };
    
    static InertiaInfo compute_inertia(
        const Eigen::SparseMatrix<double>& KKT);
    
    static bool check_inertia_correct(const InertiaInfo& inertia,
                                     int expected_pos, int expected_neg);
};

// ==============================================
// IMPROVEMENT 4: Preprocessing (Agda proof 4a, 4b)
// ==============================================

struct LPProblem {
    Eigen::SparseMatrix<double> A;
    Eigen::VectorXd b;
    Eigen::VectorXd c;
    Eigen::VectorXd lower;
    Eigen::VectorXd upper;
};

class Preprocessing {
public:
    // Agda: proof-prep-4a-remove-redundant
    static LPProblem remove_redundant_constraints(const LPProblem& lp);
    
    // Agda: proof-prep-4b-equilibration  
    struct ScalingFactors {
        Eigen::VectorXd row_scales;
        Eigen::VectorXd col_scales;
    };
    
    static ScalingFactors compute_geometric_mean_scaling(const LPProblem& lp);
    static LPProblem apply_scaling(const LPProblem& lp, 
                                   const ScalingFactors& scaling);
    
    // Detect fixed variables
    // Agda: FixedVar
    static std::vector<int> detect_fixed_variables(const LPProblem& lp);
    static LPProblem eliminate_fixed_variables(const LPProblem& lp,
                                               const std::vector<int>& fixed);
};

// ==============================================
// IMPROVEMENT 5: Homogeneous Self-Dual (Agda proof 5a, 5b)
// ==============================================

class HomogeneousSelfDual {
public:
    enum class Status {
        Feasible,
        Infeasible,
        Unknown
    };
    
    struct HSDState {
        Eigen::VectorXd z;  // Combined primal-dual-auxiliary
        double tau;         // Homogenizing variable
        double kappa;       // Auxiliary for infeasibility
        Status status;
    };
    
    // Agda: proof-hsd-5a-detection
    static Status detect_status(const HSDState& state, double tolerance);
    
    // Agda: proof-hsd-5b-warmstart
    static HSDState warm_start_from_previous(const HSDState& previous_solution);
    
    // Extract primal-dual solution from HSD
    static PDState extract_pd_solution(const HSDState& hsd_state);
    
    // Main iteration
    static HSDState iterate(const HSDState& state, const LPProblem& lp);
};

} // namespace ip_improvements
