#pragma once
#include <chrono>
#include <string>
#include <optional>
#include <memory>

namespace optsolve {

// Solver result metrics
struct SolverMetrics {
    double solve_time_ms;
    size_t iterations;
    double objective_value;
    bool is_optimal;
    std::string solver_name;
};

// Abstract base class for all solvers
template<typename ProblemType, typename SolutionType>
class Solver {
public:
    virtual ~Solver() = default;
    
    // Main solve interface
    struct Result {
        SolutionType solution;
        SolverMetrics metrics;
        bool success;
    };
    
    Result solve(const ProblemType& problem) {
        auto start = std::chrono::high_resolution_clock::now();
        
        Result result;
        result.success = solve_impl(problem, result.solution, result.metrics);
        
        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
        result.metrics.solve_time_ms = duration.count() / 1000.0;
        result.metrics.solver_name = name();
        
        return result;
    }
    
    virtual std::string name() const = 0;
    
protected:
    // Implementation method to be overridden by subclasses
    virtual bool solve_impl(const ProblemType& problem, 
                           SolutionType& solution, 
                           SolverMetrics& metrics) = 0;
};

} // namespace optsolve
