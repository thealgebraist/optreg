#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <random>
#include <cmath>

using namespace optsolve;

void save_instance(std::ofstream& out, int id, const TSPProblem& p) {
    for (size_t i = 0; i < p.n_cities; ++i) {
        out << id << "," << i << "," << p.coords[i].x << "," << p.coords[i].y << "\n";
    }
}

void save_solution(std::ofstream& out, int id, const std::vector<size_t>& tour) {
    for (size_t city : tour) {
        out << id << "," << city << "\n";
    }
}

int main() {
    std::ofstream inst_out("optreg/build/tsp_comp_instances.csv");
    std::ofstream opt_out("optreg/build/tsp_comp_solutions_opt.csv");
    std::ofstream boltz_out("optreg/build/tsp_comp_solutions_boltz.csv");

    inst_out << "instance_id,city_id,x,y\n";
    opt_out << "instance_id,city_id\n";
    boltz_out << "instance_id,city_id\n";

    TSPBranchBound opt_solver;
    TSPBoltzmannHeuristic boltz_solver;

    std::mt19937 rng(1234);
    std::uniform_int_distribution<size_t> n_dist(8, 15);

    std::cout << "Collecting comparative data for 1024 instances (Opt vs Boltzmann)...\n";

    for (int i = 0; i < 1024; ++i) {
        size_t n = n_dist(rng);
        auto p = TSPProblem::random(n, i + 6000);

        save_instance(inst_out, i, p);

        auto opt_res = opt_solver.solve(p);
        if (opt_res.success) {
            save_solution(opt_out, i, opt_res.solution.tour);
        }

        auto boltz_res = boltz_solver.solve(p);
        if (boltz_res.success) {
            save_solution(boltz_out, i, boltz_res.solution.tour);
        }

        if ((i + 1) % 100 == 0) {
            std::cout << "Processed " << (i + 1) << " instances...\n";
        }
    }

    std::cout << "Data collection complete.\n";
    return 0;
}
