#pragma once
#include "tsplib_parser.h"
#include "interior_point.h"

namespace optreg {

struct TSPSolution {
    std::vector<int> tour;
    double cost;
    bool optimal;
    double time_ms;
};

class TSPSolver {
public:
    TSPSolver() = default;
    
    // Formulate TSP into LPProblem for Branch & Bound
    LPProblem formulate_ip(const TSPInstance& instance);
    
    // Extract tour from IP solution
    std::vector<int> extract_tour(const Vector& x, int n);
};

} // namespace optreg
