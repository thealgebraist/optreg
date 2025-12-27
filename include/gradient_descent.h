#pragma once

#include "interior_point.h"

namespace optreg {

// Simple Gradient Descent solver for LP relaxation
// Uses Penalty Method: min c^T x + rho/2 ||Ax - b||^2 s.t. x >= 0
class GradientDescentSolver {
public:
    GradientDescentSolver() 
        : rho_(1000.0), learning_rate_(0.001), max_iters_(5000), verbose_(false) {}
    
    LPSolution solve(const LPProblem& problem);
    
    void set_rho(double rho) { rho_ = rho; }
    void set_learning_rate(double lr) { learning_rate_ = lr; }
    void set_max_iters(uint32_t iters) { max_iters_ = iters; }
    void set_verbose(bool v) { verbose_ = v; }
    
private:
    double rho_;           // Penalty parameter for equality constraints
    double learning_rate_; // Fixed step size (vanilla)
    uint32_t max_iters_;
    bool verbose_;
};

} // namespace optreg
