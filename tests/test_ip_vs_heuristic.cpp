#include <iostream>
#include <vector>
#include <string>
#include <chrono>
#include <random>
#include <thread>
#include <iomanip>
#include <sqlite3.h>

#include "server_solvers_bnb.hpp"
#include "server_solvers_amx.hpp"
#include "server_solvers.hpp" // For ServerGreedy

using namespace optsolve;

// Adapter for Dense AMX
class DenseAMXRelaxation : public RelaxationEngine {
    AMX_IPM_Solver solver;
public:
    RelaxationResult solve_relaxation(const ServerProblem& p, const std::vector<int>& assign) override {
        auto internal_res = solver.solve_relaxation(p, assign);
        RelaxationResult out;
        out.lower_bound = internal_res.lower_bound;
        out.fractional_solution = internal_res.fractional_solution;
        out.feasible = internal_res.feasible;
        return out;
    }
};

// SQLite Helper
sqlite3* db;

void init_db() {
    int rc = sqlite3_open("bnb_comparison.db", &db);
    if (rc) { std::cerr << "DB Error\n"; exit(1); }
    
    // Drop table if exists to start fresh? Or append? User said "rerun", usually implies fresh set.
    // Let's keep data but maybe add session id?
    // For simplicity, I'll just create if not exists.
    
    const char* sql = "CREATE TABLE IF NOT EXISTS comparison (" \
                      "id INTEGER PRIMARY KEY AUTOINCREMENT, " \
                      "run_idx INTEGER, " \
                      "problem_size INTEGER, " \
                      "opt_cost REAL, " \
                      "heuristic_cost REAL, " \
                      "gap_percent REAL, " \
                      "opt_time_ms REAL, " \
                      "heuristic_time_ms REAL, " \
                      "opt_nodes INTEGER);";
    sqlite3_exec(db, sql, 0, 0, 0);
}

void log_comparison(int run_idx, int size, double opt_cost, double heur_cost, double opt_time, double heur_time, int nodes) {
    char sql[512];
    double gap = (opt_cost > 1e-6) ? (heur_cost - opt_cost) / opt_cost * 100.0 : 0.0;
    
    snprintf(sql, sizeof(sql), 
             "INSERT INTO comparison (run_idx, problem_size, opt_cost, heuristic_cost, gap_percent, opt_time_ms, heuristic_time_ms, opt_nodes) "
             "VALUES (%d, %d, %f, %f, %f, %f, %f, %d);",
             run_idx, size, opt_cost, heur_cost, gap, opt_time, heur_time, nodes);
             
    sqlite3_exec(db, sql, 0, 0, 0);
}

int main() {
    init_db();
    
    std::cout << "Starting 1024-Run Comparison (Optimal IP vs Heuristic)...\n";
    
    std::mt19937 rng(54321); // Different seed
    std::uniform_real_distribution<float> dist_pos(0.0f, 500.0f);
    
    // Final Config: Small Feasible Instances
    // N=10, S=10 (100 vars). SLA=1000 (Assignments easy).
    // Focus on Cost optimization difference.
    int n_groups = 10;
    int n_servers = 10;
    
    ServerBnB<DenseAMXRelaxation> opt_solver("DenseAMX");
    ServerGreedy heur_solver;
    
    double total_opt_time = 0;
    double total_gap = 0;
    int valid_runs = 0;
    int infeasible_runs = 0;

    for (int i = 0; i < 1024; ++i) {
        // Generate
        ServerProblem problem;
        problem.sla_limit = 1000.0;
        problem.z_score = 1.0;
        problem.u_target = 0.0;
        
        for(int s=0; s<n_servers; ++s) problem.servers.push_back({(size_t)s, dist_pos(rng), dist_pos(rng), 400.0f, (float)(10 + s)});
        for(int g=0; g<n_groups; ++g) problem.groups.push_back({(size_t)g, dist_pos(rng), dist_pos(rng), 10.0f});
        
        // 1. Heuristic
        auto t1 = std::chrono::high_resolution_clock::now();
        auto h_res = heur_solver.solve(problem);
        auto t2 = std::chrono::high_resolution_clock::now();
        double h_time = std::chrono::duration<double>(t2-t1).count() * 1000.0;
        
        double h_cost = h_res.success ? h_res.solution.total_cost : -1.0;
        
        // 2. Optimal (BnB)
        auto t3 = std::chrono::high_resolution_clock::now();
        auto o_res = opt_solver.solve(problem);
        auto t4 = std::chrono::high_resolution_clock::now();
        double o_time = std::chrono::duration<double>(t4-t3).count() * 1000.0;
        
        // Log regardless of success to debug throughput
        double o_cost = o_res.success ? o_res.solution.total_cost : -1.0;
        log_comparison(i, n_groups * n_servers, o_cost, h_cost, o_time, h_time, opt_solver.nodes_visited);
        
        if (o_res.success && h_res.success) {
            double gap = (o_cost > 1e-6) ? (h_cost - o_cost) / o_cost * 100.0 : 0.0;
            total_opt_time += o_time;
            total_gap += gap;
            valid_runs++;
        } else {
            infeasible_runs++;
        }
        
        if (i % 50 == 0 || i == 1023) {
             std::cout << "Run " << i << "/1024 | Opt: " << std::fixed << std::setprecision(1) << o_time << "ms"
                       << " | Val: " << valid_runs << " Inf: " << infeasible_runs << "\n" << std::flush;
        }
    }
    
    std::cout << "\n--- Completed 1024 Runs ---\n";
    std::cout << "Avg Opt Time: " << (total_opt_time / valid_runs) << " ms\n";
    std::cout << "Avg Gap:      " << (total_gap / valid_runs) << " %\n";
    
    sqlite3_close(db);
    return 0;
}
