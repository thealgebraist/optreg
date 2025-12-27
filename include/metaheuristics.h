#pragma once

#include "graph_coloring.h"
#include <vector>
#include <random>

namespace optreg {

// Base class or utilities for metaheuristics
class MetaheuristicSolver {
public:
    virtual ~MetaheuristicSolver() = default;
    
    // Solve returning best allocation found
    virtual RegisterAllocation solve(
        const ControlFlowGraph& cfg,
        const InterferenceGraph& graph,
        uint32_t num_regs,
        const std::unordered_map<uint32_t, double>& spill_costs
    ) = 0;
    
protected:
    // Helper to evaluate a solution (assignment)
    double evaluate(
        const std::vector<int32_t>& assignment,
        const InterferenceGraph& graph,
        const std::unordered_map<uint32_t, double>& spill_costs,
        uint32_t num_regs
    );
};

// 1. Tabu Search
class TabuSearchSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
    void set_max_iter(int iter) { max_iter_ = iter; }
private:
    int max_iter_ = 1000;
};

// 2. Simulated Annealing
class SimulatedAnnealingSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
    void set_init_temp(double t) { init_temp_ = t; }
private:
    double init_temp_ = 100.0;
};

// 3. Genetic Algorithm
class GeneticAlgorithmSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
    void set_pop_size(int size) { pop_size_ = size; }
private:
    int pop_size_ = 100;
};

// 4. Particle Swarm Optimization
class ParticleSwarmSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
    void set_num_particles(int n) { num_particles_ = n; }
private:
    int num_particles_ = 50;
};

// Bit-optimized Tabu Search
class TabuSearchBitSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
                      uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
};

// Guided Local Search (Classic)
class GuidedLocalSearchSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
                      uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
};

// Guided Local Search (Bit Array Optimized)
class GuidedLocalSearchBitSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
                      uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
};

// Safety Net Walk (Robust Random Walk)
class SafetyNetWalkSolver : public MetaheuristicSolver {
public:
    RegisterAllocation solve(const ControlFlowGraph& cfg, const InterferenceGraph& graph, 
                      uint32_t num_regs, const std::unordered_map<uint32_t, double>& spill_costs) override;
};

} // namespace optreg
