#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <chrono>
#include <iomanip>

using namespace optsolve;

class TSPMultiRestart2Opt : public Solver<TSPProblem, TSPSolution> {
public:
    TSPMultiRestart2Opt(size_t restarts) : restarts_(restarts) {}
    std::string name() const override { return "TSP_MultiRestart2Opt_" + std::to_string(restarts_); }

protected:
    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        double best_dist = std::numeric_limits<double>::infinity();
        std::vector<size_t> best_tour;
        std::mt19937 rng(42);

        for (size_t i = 0; i < restarts_; ++i) {
            TSPSolution current_sol;
            std::vector<size_t> tour(n);
            std::iota(tour.begin(), tour.end(), 0);
            std::shuffle(tour.begin(), tour.end(), rng);
            
            double dist = 0;
            for (size_t k = 0; k < n; ++k) dist += problem.distances[tour[k]][tour[(k+1)%n]];
            current_sol.tour = tour;
            current_sol.total_distance = dist;

            // Simple 2-Opt
            bool improved = true;
            while (improved) {
                improved = false;
                for (size_t a = 1; a < n - 1; ++a) {
                    for (size_t b = a + 1; b < n; ++b) {
                        size_t p1 = current_sol.tour[a-1];
                        size_t p2 = current_sol.tour[a];
                        size_t p3 = current_sol.tour[b];
                        size_t p4 = current_sol.tour[(b+1)%n];

                        double d_old = problem.distances[p1][p2] + problem.distances[p3][p4];
                        double d_new = problem.distances[p1][p3] + problem.distances[p2][p4];

                        if (d_new < d_old - 1e-6) {
                            std::reverse(current_sol.tour.begin() + a, current_sol.tour.begin() + b + 1);
                            current_sol.total_distance += (d_new - d_old);
                            improved = true;
                        }
                    }
                }
            }

            if (current_sol.total_distance < best_dist) {
                best_dist = current_sol.total_distance;
                best_tour = current_sol.tour;
            }
            if ((i + 1) % 100 == 0 && n > 500) {
                std::cout << "  Restart " << (i + 1) << " / " << restarts_ << " complete...\n";
            }
        }

        solution.tour = best_tour;
        solution.total_distance = best_dist;
        metrics.objective_value = best_dist;
        return true;
    }

private:
    size_t restarts_;
};

int main() {
    std::cout << "=== Large-Scale TSP Heuristic Comparison ===\n\n";

    // Scenario 1: Exact vs Heuristic (N=25)
    {
        size_t n = 25;
        std::cout << "Scenario 1: Exact vs Heuristic (N=" << n << ")\n";
        auto p = TSPProblem::random(n, 777);
        
        TSPBranchBound exact;
        TSPTopologicalBoltzmann topo_boltz;

        std::cout << "Solving optimally..." << std::endl;
        auto start_opt = std::chrono::high_resolution_clock::now();
        auto res_opt = exact.solve(p);
        auto end_opt = std::chrono::high_resolution_clock::now();
        double opt_dist = res_opt.solution.total_distance;

        std::cout << "Running Topological Boltzmann..." << std::endl;
        auto start_topo = std::chrono::high_resolution_clock::now();
        auto res_topo = topo_boltz.solve(p);
        auto end_topo = std::chrono::high_resolution_clock::now();
        double topo_dist = res_topo.solution.total_distance;

        double gap = (topo_dist / opt_dist - 1.0) * 100.0;

        std::cout << std::fixed << std::setprecision(4);
        std::cout << "  Optimal:   " << opt_dist << " (" << std::chrono::duration_cast<std::chrono::milliseconds>(end_opt - start_opt).count() << "ms)\n";
        std::cout << "  Heuristic: " << topo_dist << " (" << std::chrono::duration_cast<std::chrono::microseconds>(end_topo - start_topo).count() << "us)\n";
        std::cout << "  True Gap:  " << gap << "%\n\n";
    }

    // Scenario 2: Pseudo-Optimal vs Heuristic (N=1024)
    {
        size_t n = 1024;
        std::cout << "Scenario 2: Pseudo-Optimal vs Heuristic (N=" << n << ")\n";
        // Explicitly generate in 512x512
        TSPProblem p;
        p.n_cities = n;
        p.coords.resize(n);
        p.distances.resize(n, std::vector<double>(n, 0.0));
        std::mt19937 rng(888);
        std::uniform_real_distribution<double> dist_gen(0.0, 512.0);
        for (size_t i = 0; i < n; ++i) p.coords[i] = {dist_gen(rng), dist_gen(rng)};
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                double d = std::sqrt(std::pow(p.coords[i].x - p.coords[j].x, 2) + std::pow(p.coords[i].y - p.coords[j].y, 2));
                p.distances[i][j] = p.distances[j][i] = d;
            }
        }

        TSPMultiRestart2Opt pseudo_opt(1000);
        TSPTopologicalBoltzmann topo_boltz;

        std::cout << "Running 1000-Restart 2-Opt (Baseline)..." << std::endl;
        auto start_pseudo = std::chrono::high_resolution_clock::now();
        auto res_pseudo = pseudo_opt.solve(p);
        auto end_pseudo = std::chrono::high_resolution_clock::now();
        double pseudo_dist = res_pseudo.solution.total_distance;

        std::cout << "Running Topological Boltzmann..." << std::endl;
        auto start_topo = std::chrono::high_resolution_clock::now();
        auto res_topo = topo_boltz.solve(p);
        auto end_topo = std::chrono::high_resolution_clock::now();
        double topo_dist = res_topo.solution.total_distance;

        double pseudo_gap = (topo_dist / pseudo_dist - 1.0) * 100.0;

        std::cout << std::fixed << std::setprecision(4);
        std::cout << "  Multi-2Opt: " << pseudo_dist << " (" << std::chrono::duration_cast<std::chrono::seconds>(end_pseudo - start_pseudo).count() << "s)\n";
        std::cout << "  Heuristic:  " << topo_dist << " (" << std::chrono::duration_cast<std::chrono::milliseconds>(end_topo - start_topo).count() << "ms)\n";
        std::cout << "  Pseudo-Gap: " << pseudo_gap << "%\n";
        if (topo_dist < pseudo_dist) {
            std::cout << "  *** HEURISTIC BEAT 1000-RESTART 2-OPT! ***\n";
        }
    }

    return 0;
}
