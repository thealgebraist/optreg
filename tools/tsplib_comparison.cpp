#include "tsp_solvers.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <cmath>
#include <iomanip>
#include <map>
#include <algorithm>

using namespace optsolve;

// TSPLIB Distance Functions
double nint(double x) { return (double)((int)(x + 0.5)); }

double euc_2d(const TSPProblem::Point& p1, const TSPProblem::Point& p2) {
    double dx = p1.x - p2.x;
    double dy = p1.y - p2.y;
    return nint(std::sqrt(dx*dx + dy*dy));
}

double att_dist(const TSPProblem::Point& p1, const TSPProblem::Point& p2) {
    double dx = p1.x - p2.x;
    double dy = p1.y - p2.y;
    double rij = std::sqrt((dx*dx + dy*dy) / 10.0);
    double tij = nint(rij);
    return (tij < rij) ? (double)((int)tij + 1) : (double)((int)tij);
}

double geo_dist(const TSPProblem::Point& p1, const TSPProblem::Point& p2) {
    auto to_rad = [](double degree) {
        double deg = (double)((int)degree);
        double min = degree - deg;
        return M_PI * (deg + 5.0 * min / 3.0) / 180.0;
    };
    double rrr = 6378.388;
    double q1 = std::cos(to_rad(p1.y) - to_rad(p2.y));
    double q2 = std::cos(to_rad(p1.x) - to_rad(p2.x));
    double q3 = std::cos(to_rad(p1.x) + to_rad(p2.x));
    return (double)((int)(rrr * std::acos(0.5 * ((1.0 + q1) * q2 - (1.0 - q1) * q3)) + 1.0));
}

struct TSPLIBInstance {
    std::string name;
    int dimension = 0;
    std::string edge_weight_type;
    std::string edge_weight_format;
    TSPProblem problem;
};

TSPLIBInstance load_tsplib(const std::string& path) {
    std::cout << "Loading " << path << "..." << std::endl;
    std::ifstream f(path);
    if (!f.is_open()) { std::cerr << "Failed to open " << path << std::endl; return {}; }
    std::string line;
    TSPLIBInstance inst;
    bool in_coord = false;
    bool in_explicit = false;
    
    while (std::getline(f, line)) {
        if (line.empty()) continue;
        if (line.find("NAME") != std::string::npos && line.find(":") != std::string::npos) inst.name = line.substr(line.find(":") + 1);
        else if (line.find("DIMENSION") != std::string::npos && line.find(":") != std::string::npos) inst.dimension = std::stoi(line.substr(line.find(":") + 1));
        else if (line.find("EDGE_WEIGHT_TYPE") != std::string::npos && line.find(":") != std::string::npos) inst.edge_weight_type = line.substr(line.find(":") + 1);
        else if (line.find("EDGE_WEIGHT_FORMAT") != std::string::npos && line.find(":") != std::string::npos) inst.edge_weight_format = line.substr(line.find(":") + 1);
        else if (line.find("NODE_COORD_SECTION") != std::string::npos || line.find("DISPLAY_DATA_SECTION") != std::string::npos) {
            in_coord = true;
            in_explicit = false;
            inst.problem.n_cities = inst.dimension;
            if (inst.problem.coords.empty()) inst.problem.coords.resize(inst.dimension);
        } else if (line.find("EDGE_WEIGHT_SECTION") != std::string::npos) {
            in_explicit = true;
            in_coord = false;
            inst.problem.n_cities = inst.dimension;
            inst.problem.distances.assign(inst.dimension, std::vector<double>(inst.dimension, 0));
        } else if (in_coord) {
            if (line.find("EOF") != std::string::npos) break;
            std::stringstream ss(line);
            int id; double x, y;
            if (!(ss >> id >> x >> y)) continue;
            if (id > 0 && id <= inst.dimension) inst.problem.coords[id-1] = {x, y};
        } else if (in_explicit) {
            if (line.find("EOF") != std::string::npos) { in_explicit = false; continue; }
            if (line.find("DISPLAY_DATA_SECTION") != std::string::npos) { in_explicit = false; in_coord = true; continue; }
            
            std::stringstream ss(line);
            double val;
            static int r = 0, c = 0;
            static std::string current_format = "";
            if (current_format != inst.edge_weight_format) { r = 0; c = 0; current_format = inst.edge_weight_format; }
            
            while (ss >> val) {
                if (inst.edge_weight_format.find("FULL_MATRIX") != std::string::npos) {
                    if (r < inst.dimension && c < inst.dimension) {
                        inst.problem.distances[r][c] = val;
                        c++; if (c == inst.dimension) { r++; c = 0; }
                    }
                } else if (inst.edge_weight_format.find("LOWER_DIAG_ROW") != std::string::npos) {
                    if (r < inst.dimension && c <= r) {
                        inst.problem.distances[r][c] = inst.problem.distances[c][r] = val;
                        c++; if (c > r) { r++; c = 0; }
                    }
                } else if (inst.edge_weight_format.find("UPPER_ROW") != std::string::npos) {
                    if (r < inst.dimension - 1) {
                        if (c == 0) c = r + 1;
                        inst.problem.distances[r][c] = inst.problem.distances[c][r] = val;
                        c++; if (c == inst.dimension) { r++; c = r + 1; }
                    }
                }
            }
        }
    }
    
    // Compute distances for coord-based weighted types
    if (inst.problem.distances.empty()) inst.problem.distances.assign(inst.dimension, std::vector<double>(inst.dimension, 0));
    if (!inst.problem.coords.empty()) {
        for (int i = 0; i < inst.dimension; ++i) {
            for (int j = 0; j < inst.dimension; ++j) {
                if (i == j) continue;
                if (inst.problem.distances[i][j] != 0) continue; // Keep explicit if exists
                
                if (inst.edge_weight_type.find("EUC_2D") != std::string::npos)
                    inst.problem.distances[i][j] = euc_2d(inst.problem.coords[i], inst.problem.coords[j]);
                else if (inst.edge_weight_type.find("GEO") != std::string::npos)
                    inst.problem.distances[i][j] = geo_dist(inst.problem.coords[i], inst.problem.coords[j]);
                else if (inst.edge_weight_type.find("ATT") != std::string::npos)
                    inst.problem.distances[i][j] = att_dist(inst.problem.coords[i], inst.problem.coords[j]);
                else
                    inst.problem.distances[i][j] = std::sqrt(std::pow(inst.problem.coords[i].x - inst.problem.coords[j].x, 2) +
                                                           std::pow(inst.problem.coords[i].y - inst.problem.coords[j].y, 2));
            }
        }
    }
    return inst;
}

int main() {
    std::map<std::string, double> optimal_values;
    std::ifstream sol_f("optreg/data/tsplib/solutions");
    std::string line;
    while (std::getline(sol_f, line)) {
        size_t colon = line.find(":");
        if (colon != std::string::npos) {
            std::string name = line.substr(0, colon);
            name.erase(0, name.find_first_not_of(" \t\r\n"));
            name.erase(name.find_last_not_of(" \t\r\n") + 1);
            std::stringstream ss(line.substr(colon + 1));
            double val; ss >> val;
            optimal_values[name] = val;
        }
    }

    std::vector<std::string> tsplib_files = {
        "burma14", "ulysses16", "ulysses22", "fri26", "bayg29", "bays29", "att48", "berlin52",
        "eil51", "st70", "pr76", "rat99", "kroA100", "rd100", "eil101", "lin105"
    };
    std::vector<std::shared_ptr<Solver<TSPProblem, TSPSolution>>> heuristics = {
        std::make_shared<TSPNearestNeighbor>(),
        std::make_shared<TSP2Opt>(),
        std::make_shared<TSPPatternHeuristic>(),
        std::make_shared<TSPGeometricHeuristic>(),
        std::make_shared<TSPBoltzmannHeuristic>()
    };

    std::cout << "\n=== TSPLIB Comparison ===\n";
    std::cout << std::left << std::setw(12) << "Instance" << " | " << std::setw(20) << "Solver" << " | " << std::setw(10) << "Result" << " | " << std::setw(10) << "Optimal" << " | " << "Gap %" << "\n";
    std::cout << std::string(75, '-') << "\n";

    for (const auto& name_raw : tsplib_files) {
        auto inst = load_tsplib("optreg/data/tsplib/" + name_raw + ".tsp");
        double opt = optimal_values[name_raw];
        if (opt == 0) {
            std::cout << "Warning: No optimal value for " << name_raw << "\n";
            continue;
        }
        
        for (auto& h : heuristics) {
            if ((h->name() == "TSP_Geometric" || h->name() == "TSP_Boltzmann") && inst.problem.coords.empty()) {
                // TSP_Boltzmann also doesn't really work without coords if it needs d_avg from all edges?
                // Actually it DOES work if it uses distances, let's keep it if distances are present.
            }
            if (h->name() == "TSP_Geometric" && inst.problem.coords.empty()) {
                 std::cout << std::left << std::setw(12) << name_raw << " | " << std::setw(20) << h->name() << " | " 
                          << std::setw(10) << "N/A" << " | " << std::setw(10) << opt << " | " << "Skipped\n";
                 continue;
            }

            auto res = h->solve(inst.problem);
            double gap = (res.solution.total_distance / opt - 1.0) * 100.0;
            std::cout << std::left << std::setw(12) << name_raw << " | " << std::setw(20) << h->name() << " | " 
                      << std::setw(10) << std::fixed << std::setprecision(0) << res.solution.total_distance << " | " 
                      << std::setw(10) << opt << " | " << std::setprecision(2) << gap << "%\n";
        }
        std::cout << std::string(75, '-') << "\n";
    }

    std::cout << "\n=== Random Instances Comparison (n < 16, N=512) ===\n";
    TSPBranchBound exact;
    std::mt19937 rng(42);
    std::uniform_int_distribution<size_t> n_dist(8, 15);
    std::map<std::string, double> avg_gaps;
    for (int i = 0; i < 512; ++i) {
        size_t n = n_dist(rng);
        auto p = TSPProblem::random(n, i + 5000);
        auto opt_res = exact.solve(p);
        double opt = opt_res.solution.total_distance;
        for (auto& h : heuristics) {
            auto res = h->solve(p);
            avg_gaps[h->name()] += (res.solution.total_distance / opt - 1.0) * 100.0;
        }
        if ((i + 1) % 100 == 0) std::cout << "Benchmarked " << (i + 1) << " instances...\n";
    }
    for (auto const& [name, total_gap] : avg_gaps) {
        std::cout << std::left << std::setw(25) << name << " | Avg Gap: " << std::fixed << std::setprecision(3) << total_gap / 512.0 << "%\n";
    }
    return 0;
}
