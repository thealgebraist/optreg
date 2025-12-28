#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <random>
#include <cmath>

using namespace optsolve;

void save_instance(std::ofstream& instance_file, int id, const TSPProblem& problem) {
    for (size_t i = 0; i < problem.n_cities; ++i) {
        instance_file << id << "," << i << "," << problem.coords[i].x << "," << problem.coords[i].y << "\n";
    }
}

void save_solution(std::ofstream& solution_file, int id, const TSPSolution& solution) {
    for (size_t i = 0; i < solution.tour.size(); ++i) {
        solution_file << id << "," << i << "," << solution.tour[i] << "\n";
    }
}

int main() {
    std::ofstream instances_out("optreg/build/tsp_instances_expanded.csv");
    std::ofstream solutions_out("optreg/build/tsp_solutions_expanded.csv");
    
    instances_out << "instance_id,city_id,x,y\n";
    solutions_out << "instance_id,tour_pos,city_id\n";

    TSPBranchBound solver;
    std::mt19937 rng(43);
    std::uniform_int_distribution<size_t> n_dist(4, 15);
    std::uniform_int_distribution<int> grid_dist(0, 511);

    std::cout << "Generating 32000 ultra-high-confidence random TSP instances ($n < 16, 512 \\times 512$ grid) and solving optimally...\n";

    for (int i = 0; i < 32000; ++i) {
        size_t n = n_dist(rng);
        
        TSPProblem problem;
        problem.n_cities = n;
        problem.coords.resize(n);
        problem.distances.assign(n, std::vector<double>(n, 0.0));
        
        for (size_t j = 0; j < n; ++j) {
            problem.coords[j] = {static_cast<double>(grid_dist(rng)), static_cast<double>(grid_dist(rng))};
        }
        
        for (size_t j = 0; j < n; ++j) {
            for (size_t k = j + 1; k < n; ++k) {
                double d = std::sqrt(std::pow(problem.coords[j].x - problem.coords[k].x, 2) +
                                   std::pow(problem.coords[j].y - problem.coords[k].y, 2));
                problem.distances[j][k] = problem.distances[k][j] = d;
            }
        }
        
        save_instance(instances_out, i, problem);
        
        auto result = solver.solve(problem);
        if (result.success) {
            save_solution(solutions_out, i, result.solution);
        }
        
        if ((i + 1) % 1000 == 0) {
            std::cout << "Solved " << (i + 1) << " instances...\n";
        }
    }
    instances_out.close();
    solutions_out.close();

    std::cout << "Analysis data generation complete (2048 instances).\n";
    return 0;
}
