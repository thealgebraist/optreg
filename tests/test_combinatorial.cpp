#include "solver_base.hpp"
#include "problem_types.hpp"
#include "tsp_solvers.hpp"
#include "knapsack_solvers.hpp"
#include "sat_solvers.hpp"
#include "coloring_solvers.hpp"
#include "vertex_cover_solvers.hpp"
#include "clique_solvers.hpp"
#include "hamiltonian_solvers.hpp"
#include "set_cover_solvers.hpp"
#include "subset_sum_solvers.hpp"
#include "steiner_tree_solvers.hpp"
#include "all_advanced_solvers.hpp"
#include "all_mc_solvers.hpp"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <memory>
#include <functional>

using namespace optsolve;

// Test runner for a specific problem type
template<typename Problem, typename Solution, typename... Solvers>
void run_problem_tests(const std::string& problem_name, 
                       size_t num_instances,
                       std::function<Problem(size_t, unsigned)> generator,
                       std::ofstream& csv_out) {
    
    std::cout << "\n=== Testing " << problem_name << " ===" << std::endl;
    
    // Create solver instances
    std::vector<std::unique_ptr<Solver<Problem, Solution>>> solvers;
    (solvers.push_back(std::make_unique<Solvers>()), ...);
    
    for (size_t inst = 0; inst < num_instances; ++inst) {
        unsigned seed = 1000 + inst;
        Problem problem = generator(inst, seed);
        
        std::cout << "Instance " << (inst + 1) << "/" << num_instances << std::endl;
        
        for (auto& solver : solvers) {
            auto result = solver->solve(problem);
            
            bool valid = result.solution.is_valid(problem);
            
            csv_out << problem_name << ","
                   << inst << ","
                   << result.metrics.solver_name << ","
                   << result.metrics.solve_time_ms << ","
                   << result.metrics.objective_value << ","
                   << result.metrics.iterations << ","
                   << (result.metrics.is_optimal ? "optimal" : "heuristic") << ","
                   << (valid ? "valid" : "INVALID") << "\n";
                   
            std::cout << "  " << std::setw(30) << std::left << result.metrics.solver_name
                     << " Time: " << std::setw(8) << std::right << std::fixed << std::setprecision(2)
                     << result.metrics.solve_time_ms << "ms"
                     << " Obj: " << std::setw(10) << result.metrics.objective_value
                     << " " << (valid ? "✓" : "✗") << std::endl;
        }
    }
}

int main(int argc, char** argv) {
    std::string output_file = "solver_results.csv";
    
    if (argc > 2 && std::string(argv[1]) == "--output") {
        output_file = argv[2];
    }
    
    std::ofstream csv_out(output_file);
    csv_out << "Problem,Instance,Solver,Time_ms,Objective,Iterations,Type,Valid\n";
    
    const size_t n_instances = 16;
    
    std::cout << "Combinatorial Optimization Solver Suite\n";
    std::cout << "Testing " << n_instances << " instances per problem\n";
    std::cout << "========================================\n";
    
    // TSP - All 10 solvers
    run_problem_tests<TSPProblem, TSPSolution, 
        TSPNearestNeighbor, TSP2Opt, TSPBranchBound,
        TSPSparseAMX, TSPDenseAMX, TSPEigenSparse, TSPEigenDense, TSPInteriorPoint,
        TSPMonteCarlo, TSPMonteCarloRW, TSPPatternHeuristic, TSPGeometricHeuristic>(
        "TSP", n_instances,
        [](size_t i, unsigned seed) { return TSPProblem::random(8 + i % 5, seed); },
        csv_out
    );
    
    // Knapsack - All 10 solvers
    run_problem_tests<KnapsackProblem, KnapsackSolution, 
        KnapsackGreedy, KnapsackDP, KnapsackBranchBound,
        KnapsackSparseAMX, KnapsackDenseAMX, KnapsackEigenSparse, KnapsackEigenDense, KnapsackInteriorPoint,
        KnapsackMonteCarlo, KnapsackMonteCarloRW>(
        "Knapsack", n_instances,
        [](size_t i, unsigned seed) { return KnapsackProblem::random(15 + i % 10, 0.5, seed); },
        csv_out
    );
    
    // SAT - All 10 solvers
    run_problem_tests<SATProblem, SATSolution, 
        SATDPLL, SATWalkSAT, SATBranchBound,
        SATSparseAMX, SATDenseAMX, SATEigenSparse, SATEigenDense, SATInteriorPoint,
        SATMonteCarlo, SATMonteCarloRW>(
        "SAT", n_instances,
        [](size_t i, unsigned seed) { return SATProblem::random(8 + i % 4, 15 + i % 10, 3, seed); },
        csv_out
    );
    
    // Graph Coloring - All 10 solvers
    run_problem_tests<GraphColoringProblem, GraphColoringSolution, 
        ColoringGreedy, ColoringDSATUR, ColoringBranchBound,
        GraphColoringSparseAMX, GraphColoringDenseAMX, GraphColoringEigenSparse, GraphColoringEigenDense, GraphColoringInteriorPoint,
        GraphColoringMonteCarlo, GraphColoringMonteCarloRW>(
        "GraphColoring", n_instances,
        [](size_t i, unsigned seed) { return GraphColoringProblem::random(10 + i % 5, 0.3, seed); },
        csv_out
    );
    
    // Vertex Cover - All 10 solvers
    run_problem_tests<VertexCoverProblem, VertexCoverSolution, 
        VertexCoverGreedy, VertexCover2Approx, VertexCoverBranchBound,
        VertexCoverSparseAMX, VertexCoverDenseAMX, VertexCoverEigenSparse, VertexCoverEigenDense, VertexCoverInteriorPoint,
        VertexCoverMonteCarlo, VertexCoverMonteCarloRW>(
        "VertexCover", n_instances,
        [](size_t i, unsigned seed) { return VertexCoverProblem::random(12 + i % 6, 0.3, seed); },
        csv_out
    );
    
    // Clique - All 10 solvers
    run_problem_tests<CliqueProblem, CliqueSolution, 
        CliqueGreedy, CliqueBronKerbosch, CliqueBranchBound,
        CliqueSparseAMX, CliqueDenseAMX, CliqueEigenSparse, CliqueEigenDense, CliqueInteriorPoint,
        CliqueMonteCarlo, CliqueMonteCarloRW>(
        "Clique", n_instances,
        [](size_t i, unsigned seed) { return CliqueProblem::random(12 + i % 4, 0.5, seed); },
        csv_out
    );
    
    // Hamiltonian Cycle - All 10 solvers
    run_problem_tests<HamiltonianProblem, HamiltonianSolution, 
        HamiltonianBacktrack, HamiltonianRotation, HamiltonianBranchBound,
        HamiltonianSparseAMX, HamiltonianDenseAMX, HamiltonianEigenSparse, HamiltonianEigenDense, HamiltonianInteriorPoint,
        HamiltonianMonteCarlo, HamiltonianMonteCarloRW>(
        "HamiltonianCycle", n_instances,
        [](size_t i, unsigned seed) { return HamiltonianProblem::random(8 + i % 4, 0.4, seed); },
        csv_out
    );
    
    // Set Cover - All 10 solvers
    run_problem_tests<SetCoverProblem, SetCoverSolution, 
        SetCoverGreedy, SetCoverFrequency, SetCoverBranchBound,
        SetCoverSparseAMX, SetCoverDenseAMX, SetCoverEigenSparse, SetCoverEigenDense, SetCoverInteriorPoint,
        SetCoverMonteCarlo, SetCoverMonteCarloRW>(
        "SetCover", n_instances,
        [](size_t i, unsigned seed) { return SetCoverProblem::random(15 + i % 10, 10 + i % 5, seed); },
        csv_out
    );
    
    // Subset Sum - All 10 solvers
    run_problem_tests<SubsetSumProblem, SubsetSumSolution, 
        SubsetSumGreedy, SubsetSumMeetMiddle, SubsetSumBranchBound,
        SubsetSumSparseAMX, SubsetSumDenseAMX, SubsetSumEigenSparse, SubsetSumEigenDense, SubsetSumInteriorPoint,
        SubsetSumMonteCarlo, SubsetSumMonteCarloRW>(
        "SubsetSum", n_instances,
        [](size_t i, unsigned seed) { return SubsetSumProblem::random(15 + i % 10, seed); },
        csv_out
    );
    
    // Steiner Tree - All 10 solvers
    run_problem_tests<SteinerTreeProblem, SteinerTreeSolution, 
        SteinerMST, SteinerShortestPath, SteinerBranchBound,
        SteinerSparseAMX, SteinerDenseAMX, SteinerEigenSparse, SteinerEigenDense, SteinerInteriorPoint,
        SteinerMonteCarlo, SteinerMonteCarloRW>(
        "SteinerTree", n_instances,
        [](size_t i, unsigned seed) { return SteinerTreeProblem::random(12 + i % 6, 4 + i % 3, seed); },
        csv_out
    );

    // Server Optimization - All 3 basic solvers + AMX IPM
    run_problem_tests<ServerProblem, ServerSolution,
        ServerGreedy, ServerSparseAMX, AMX_IPM_Solver>(
        "Server", n_instances,
        [](size_t i, unsigned seed) { return ServerProblem::random(10 + i % 5, 20 + i % 10, seed); },
        csv_out
    );
    
    csv_out.close();
    
    std::cout << "\n========================================\n";
    std::cout << "Results written to: " << output_file << std::endl;
    std::cout << "Total problems: 10\n";
    std::cout << "Instances per problem: " << n_instances << "\n";
    std::cout << "Total tests: " << (10 * n_instances * 10 + n_instances) << " (11 for TSP, 10 for others)\n";
    
    return 0;
}
