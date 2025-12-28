#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <algorithm>
#include <numeric>
#include <limits>
#include <cmath>
#include <queue>

namespace optsolve {

// ============================================================================
// TSP Heuristic 1: Nearest Neighbor
// ============================================================================
class TSPNearestNeighbor : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "TSP_NearestNeighbor"; }
    
protected:
    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        std::vector<bool> visited(n, false);
        solution.tour.clear();
        solution.tour.reserve(n);
        
        // Start from city 0
        size_t current = 0;
        solution.tour.push_back(current);
        visited[current] = true;
        
        for (size_t step = 1; step < n; ++step) {
            double min_dist = std::numeric_limits<double>::infinity();
            size_t nearest = 0;
            
            for (size_t next = 0; next < n; ++next) {
                if (!visited[next] && problem.distances[current][next] < min_dist) {
                    min_dist = problem.distances[current][next];
                    nearest = next;
                }
            }
            
            visited[nearest] = true;
            solution.tour.push_back(nearest);
            current = nearest;
        }
        
        // Calculate total distance
        solution.total_distance = 0;
        for (size_t i = 0; i < n; ++i) {
            size_t from = solution.tour[i];
            size_t to = solution.tour[(i + 1) % n];
            solution.total_distance += problem.distances[from][to];
        }
        
        metrics.iterations = n;
        metrics.objective_value = solution.total_distance;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// TSP Heuristic 2: 2-Opt Improvement
// ============================================================================
class TSP2Opt : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "TSP_2Opt"; }
    
protected:
    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        
        // Start with nearest neighbor solution
        TSPNearestNeighbor nn;
        auto nn_result = nn.solve(problem);
        solution = nn_result.solution;
        
        bool improved = true;
        size_t iterations = 0;
        const size_t max_iter = 1000;
        
        while (improved && iterations < max_iter) {
            improved = false;
            
            for (size_t i = 1; i < n - 1; ++i) {
                for (size_t j = i + 1; j < n; ++j) {
                    double delta = calculate_2opt_delta(problem, solution.tour, i, j);
                    
                    if (delta < -1e-6) {
                        // Apply 2-opt swap
                        std::reverse(solution.tour.begin() + i, solution.tour.begin() + j + 1);
                        solution.total_distance += delta;
                        improved = true;
                    }
                }
            }
            
            iterations++;
        }
        
        metrics.iterations = iterations;
        metrics.objective_value = solution.total_distance;
        metrics.is_optimal = false;
        
        return true;
    }
    
private:
    double calculate_2opt_delta(const TSPProblem& problem, 
                                const std::vector<size_t>& tour, 
                                size_t i, size_t j) {
        size_t n = tour.size();
        
        // Current edges: (i-1, i) and (j, j+1)
        // New edges: (i-1, j) and (i, j+1)
        size_t a = tour[i - 1];
        size_t b = tour[i];
        size_t c = tour[j];
        size_t d = tour[(j + 1) % n];
        
        double old_dist = problem.distances[a][b] + problem.distances[c][d];
        double new_dist = problem.distances[a][c] + problem.distances[b][d];
        
        return new_dist - old_dist;
    }
};

// ============================================================================
// TSP Branch and Bound
// ============================================================================
class TSPBranchBound : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "TSP_BranchBound"; }
    
protected:
    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        if (n == 0) return true;
        if (n == 1) {
            solution.tour = {0};
            solution.total_distance = 0;
            metrics.is_optimal = true;
            return true;
        }
        
        // Get initial upper bound using 2-opt
        TSP2Opt solver_2opt;
        auto opt_result = solver_2opt.solve(problem);
        solution = opt_result.solution;
        
        double best_dist = solution.total_distance;
        std::vector<size_t> best_tour = solution.tour;
        std::vector<size_t> current_tour = {0};
        std::vector<bool> visited(n, false);
        visited[0] = true;
        
        size_t nodes_visited = 0;
        branch_and_bound_recurse(problem, current_tour, visited, 0, best_tour, best_dist, nodes_visited);
        
        solution.tour = best_tour;
        solution.total_distance = best_dist;
        
        metrics.iterations = nodes_visited;
        metrics.objective_value = best_dist;
        metrics.is_optimal = true;
        
        return true;
    }
    
private:
    double calculate_mst_weight(const TSPProblem& problem, const std::vector<bool>& visited) {
        size_t n = problem.n_cities;
        std::vector<size_t> unvisited;
        for (size_t i = 0; i < n; ++i) if (!visited[i]) unvisited.push_back(i);
        
        if (unvisited.empty()) return 0;
        
        // Prim's algorithm for MST on unvisited cities
        double mst_weight = 0;
        std::vector<double> min_edge(unvisited.size(), std::numeric_limits<double>::infinity());
        std::vector<bool> in_mst(unvisited.size(), false);
        min_edge[0] = 0;
        
        for (size_t i = 0; i < unvisited.size(); ++i) {
            int u = -1;
            for (size_t v = 0; v < unvisited.size(); ++v) {
                if (!in_mst[v] && (u == -1 || min_edge[v] < min_edge[u])) u = v;
            }
            
            if (min_edge[u] == std::numeric_limits<double>::infinity()) return std::numeric_limits<double>::infinity();
            
            in_mst[u] = true;
            mst_weight += min_edge[u];
            
            for (size_t v = 0; v < unvisited.size(); ++v) {
                if (!in_mst[v]) {
                    double d = problem.distances[unvisited[u]][unvisited[v]];
                    if (d < min_edge[v]) min_edge[v] = d;
                }
            }
        }
        return mst_weight;
    }

    void branch_and_bound_recurse(const TSPProblem& problem,
                                  std::vector<size_t>& current_tour,
                                  std::vector<bool>& visited,
                                  double current_dist,
                                  std::vector<size_t>& best_tour,
                                  double& best_dist,
                                  size_t& nodes_visited) {
        nodes_visited++;
        size_t n = problem.n_cities;
        
        if (current_tour.size() == n) {
            double total = current_dist + problem.distances[current_tour.back()][0];
            if (total < best_dist) {
                best_dist = total;
                best_tour = current_tour;
            }
            return;
        }
        
        // 1-tree Lower Bound:
        // LB = current_dist + MST(unvisited) + min_edge(last_visited -> unvisited) + min_edge(unvisited -> 0)
        double mst = calculate_mst_weight(problem, visited);
        if (mst == std::numeric_limits<double>::infinity()) return;
        
        double min_to_unvisited = std::numeric_limits<double>::infinity();
        double min_from_unvisited = std::numeric_limits<double>::infinity();
        
        size_t last = current_tour.back();
        for (size_t i = 0; i < n; ++i) {
            if (!visited[i]) {
                min_to_unvisited = std::min(min_to_unvisited, problem.distances[last][i]);
                min_from_unvisited = std::min(min_from_unvisited, problem.distances[i][0]);
            }
        }
        
        double lb = current_dist + mst + min_to_unvisited + min_from_unvisited;
        if (lb >= best_dist - 1e-6) return;
        
        // Heuristic branching: try closest unvisited cities first
        std::vector<std::pair<double, size_t>> candidates;
        for (size_t next = 0; next < n; ++next) {
            if (!visited[next]) {
                candidates.push_back({problem.distances[last][next], next});
            }
        }
        std::sort(candidates.begin(), candidates.end());
        
        for (const auto& cand : candidates) {
            size_t next = cand.second;
            double d = cand.first;
            
            if (current_dist + d >= best_dist) continue;
            
            current_tour.push_back(next);
            visited[next] = true;
            
            branch_and_bound_recurse(problem, current_tour, visited, current_dist + d, 
                                    best_tour, best_dist, nodes_visited);
            
            current_tour.pop_back();
            visited[next] = false;
        }
    }
};

// ============================================================================
// TSP Pattern-Based Heuristic
// ============================================================================
class TSPGeometricHeuristic : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "TSP_Geometric"; }

    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        if (n < 3) {
            TSPNearestNeighbor fallback;
            auto res = fallback.solve(problem);
            solution = res.solution;
            return res.success;
        }

        // 1. Geometric Greedy Construction
        // Target angle: 118 degrees.
        // Score = Distance + alpha * |Target_Angle - Angle|
        std::vector<size_t> tour;
        std::vector<bool> visited(n, false);
        
        // Start with city 0 and its nearest neighbor
        tour.push_back(0);
        visited[0] = true;
        
        size_t first_nn = 0;
        double min_d = std::numeric_limits<double>::infinity();
        for (size_t i = 1; i < n; ++i) {
            if (problem.distances[0][i] < min_d) {
                min_d = problem.distances[0][i];
                first_nn = i;
            }
        }
        tour.push_back(first_nn);
        visited[first_nn] = true;

        while (tour.size() < n) {
            size_t prev = tour[tour.size() - 2];
            size_t curr = tour.back();
            
            size_t best_next = -1;
            double best_score = std::numeric_limits<double>::infinity();
            
            for (size_t next = 0; next < n; ++next) {
                if (!visited[next]) {
                    double d = problem.distances[curr][next];
                    double angle = calculate_angle(problem.coords[prev], problem.coords[curr], problem.coords[next]);
                    
                    // Geometric Score: Penalize deviation from 118 degrees
                    // We also normalize distance by global average to keep units comparable
                    double angle_penalty = std::abs(118.0 - angle) * (d / 20.0); // Simple heuristic weighting
                    double score = d + angle_penalty;
                    
                    if (score < best_score) {
                        best_score = score;
                        best_next = next;
                    }
                }
            }
            tour.push_back(best_next);
            visited[best_next] = true;
        }

        solution.tour = tour;
        calculate_total_distance(problem, solution);

        // 2. Geometric 2-Opt Refinement
        // Prioritize swapping edges that form sharp angles
        bool improved = true;
        int max_iter = 1000;
        while (improved && max_iter-- > 0) {
            improved = false;
            for (size_t i = 0; i < n - 2; ++i) {
                for (size_t j = i + 2; j < n; ++j) {
                    if (i == 0 && j == n - 1) continue;

                    double d_old = problem.distances[solution.tour[i]][solution.tour[i+1]] + 
                                  problem.distances[solution.tour[j]][solution.tour[(j+1)%n]];
                    double d_new = problem.distances[solution.tour[i]][solution.tour[j]] + 
                                  problem.distances[solution.tour[i+1]][solution.tour[(j+1)%n]];

                    // Calculate "Geometric Quality" (avg deviation from 118 degrees at the 4 affected nodes)
                    // This is a bit complex for a fast heuristic, so we'll use a bias:
                    // If distance is roughly equal, prefer the one with blunter angles.
                    if (d_new < d_old - 1e-6) {
                        std::reverse(solution.tour.begin() + i + 1, solution.tour.begin() + j + 1);
                        improved = true;
                    }
                }
            }
        }

        calculate_total_distance(problem, solution);
        metrics.objective_value = solution.total_distance;
        return true;
    }

private:
    double calculate_angle(const TSPProblem::Point& a, const TSPProblem::Point& b, const TSPProblem::Point& c) {
        double ux = a.x - b.x;
        double uy = a.y - b.y;
        double vx = c.x - b.x;
        double vy = c.y - b.y;
        double dot = ux * vx + uy * vy;
        double mag_u = std::sqrt(ux * ux + uy * uy);
        double mag_v = std::sqrt(vx * vx + vy * vy);
        if (mag_u < 1e-9 || mag_v < 1e-9) return 180.0;
        double cos_theta = dot / (mag_u * mag_v);
        cos_theta = std::max(-1.0, std::min(1.0, cos_theta));
        return std::acos(cos_theta) * 180.0 / M_PI;
    }

    void calculate_total_distance(const TSPProblem& problem, TSPSolution& solution) {
        solution.total_distance = 0;
        for (size_t i = 0; i < solution.tour.size(); ++i) {
            solution.total_distance += problem.distances[solution.tour[i]][solution.tour[(i + 1) % solution.tour.size()]];
        }
    }
};

class TSPPatternHeuristic : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "TSP_PatternHeuristic"; }
    
protected:
    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        if (n < 2) return true;
        
        // 1. Precompute global average distance and KNN (K=8 as per analysis)
        double total_d = 0;
        size_t count = 0;
        std::vector<std::vector<size_t>> knn(n);
        for (size_t i = 0; i < n; ++i) {
            std::vector<std::pair<double, size_t>> candidates;
            for (size_t j = 0; j < n; ++j) {
                if (i == j) continue;
                double d = problem.distances[i][j];
                total_d += d;
                count++;
                candidates.push_back({d, j});
            }
            std::sort(candidates.begin(), candidates.end());
            size_t k = std::min(n - 1, (size_t)8);
            for (size_t j = 0; j < k; ++j) knn[i].push_back(candidates[j].second);
        }
        double avg_d = total_d / count;
        double prune_threshold = avg_d * 1.5;
        
        // 2. Pattern-Aware Construction (KNN first)
        std::vector<bool> visited(n, false);
        solution.tour.clear();
        solution.tour.reserve(n);
        
        size_t current = 0;
        solution.tour.push_back(current);
        visited[current] = true;
        
        for (size_t step = 1; step < n; ++step) {
            size_t nearest = n;
            double min_d = std::numeric_limits<double>::infinity();
            
            // Try KNN first
            for (size_t neighbor : knn[current]) {
                if (!visited[neighbor]) {
                    nearest = neighbor;
                    min_d = problem.distances[current][neighbor];
                    break;
                }
            }
            
            // Fallback to global nearest if all KNN visited or if nearest is too long
            if (nearest == n) {
                for (size_t i = 0; i < n; ++i) {
                    if (!visited[i] && problem.distances[current][i] < min_d) {
                        min_d = problem.distances[current][i];
                        nearest = i;
                    }
                }
            }
            
            visited[nearest] = true;
            solution.tour.push_back(nearest);
            current = nearest;
        }
        
        // Calculate initial distance
        solution.total_distance = 0;
        for (size_t i = 0; i < n; ++i) {
            solution.total_distance += problem.distances[solution.tour[i]][solution.tour[(i + 1) % n]];
        }
        
        // 3. Pattern-Aware Refinement (Restricted 2-Opt)
        bool improved = true;
        size_t iterations = 0;
        while (improved && iterations < 100) {
            improved = false;
            for (size_t i = 1; i < n - 1; ++i) {
                for (size_t j = i + 1; j < n; ++j) {
                    // Only consider swaps that replace "long" edges or use KNN connections
                    size_t a = solution.tour[i-1], b = solution.tour[i];
                    size_t c = solution.tour[j], d = solution.tour[(j+1)%n];
                    
                    // Pattern: Long edges should be replaced
                    bool needs_improvement = (problem.distances[a][b] > avg_d || problem.distances[c][d] > avg_d);
                    
                    if (needs_improvement) {
                        double old_dist = problem.distances[a][b] + problem.distances[c][d];
                        double new_dist = problem.distances[a][c] + problem.distances[b][d];
                        
                        if (new_dist < old_dist - 1e-6) {
                            std::reverse(solution.tour.begin() + i, solution.tour.begin() + j + 1);
                            solution.total_distance += (new_dist - old_dist);
                            improved = true;
                        }
                    }
                }
            }
            iterations++;
        }
        
        metrics.iterations = iterations;
        metrics.objective_value = solution.total_distance;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// TSP Boltzmann-Guided Heuristic
// ============================================================================
class TSPBoltzmannHeuristic : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "TSP_Boltzmann"; }

protected:
    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        if (n < 2) {
            TSPNearestNeighbor fallback;
            auto res = fallback.solve(problem);
            solution = res.solution;
            return res.success;
        }

        // 1. Calculate problem-wide metrics for normalization
        double total_dist = 0;
        size_t edge_count = 0;
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                total_dist += problem.distances[i][j];
                edge_count++;
            }
        }
        double avg_dist = total_dist / edge_count;

        // 2. Boltzmann-Sampled Construction
        // We run multiple trials and keep the best
        size_t n_trials = std::min((size_t)32, 1024 / n + 1);
        double best_total = std::numeric_limits<double>::infinity();
        std::vector<size_t> best_tour;
        
        std::mt19937 rng(1337);
        
        for (size_t trial = 0; trial < n_trials; ++trial) {
            std::vector<size_t> current_tour;
            std::vector<bool> visited(n, false);
            current_tour.reserve(n);
            
            size_t current = trial % n; // Diverse starting points
            current_tour.push_back(current);
            visited[current] = true;
            
            while (current_tour.size() < n) {
                std::vector<std::pair<double, size_t>> candidates;
                for (size_t next = 0; next < n; ++next) {
                    if (!visited[next]) {
                        double d = problem.distances[current][next];
                        double norm_d = d / avg_dist;
                        // Prob = 1.17 * exp(-2.15 * norm_d)
                        double prob = std::exp(-2.15 * norm_d);
                        candidates.push_back({prob, next});
                    }
                }
                
                // Sample from candidates
                double sum_prob = 0;
                for (auto& c : candidates) sum_prob += c.first;
                
                std::uniform_real_distribution<double> dist(0, sum_prob);
                double r = dist(rng);
                double accum = 0;
                size_t selected = candidates.back().second;
                for (auto& c : candidates) {
                    accum += c.first;
                    if (r <= accum) {
                        selected = c.second;
                        break;
                    }
                }
                
                visited[selected] = true;
                current_tour.push_back(selected);
                current = selected;
            }
            
            double dist = 0;
            for (size_t i = 0; i < n; ++i) {
                dist += problem.distances[current_tour[i]][current_tour[(i + 1) % n]];
            }
            
            if (dist < best_total) {
                best_total = dist;
                best_tour = current_tour;
            }
        }
        
        solution.tour = best_tour;
        solution.total_distance = best_total;

        // 3. Boltzmann-Biased 2-Opt Refinement
        bool improved = true;
        size_t iter = 0;
        while (improved && iter < 1000) {
            improved = false;
            for (size_t i = 1; i < n - 1; ++i) {
                for (size_t j = i + 1; j < n; ++j) {
                    size_t a = solution.tour[i-1];
                    size_t b = solution.tour[i];
                    size_t c = solution.tour[j];
                    size_t d = solution.tour[(j+1)%n];
                    
                    double d_old = problem.distances[a][b] + problem.distances[c][d];
                    double d_new = problem.distances[a][c] + problem.distances[b][d];
                    
                    if (d_new < d_old - 1e-6) {
                        // Apply swap
                        std::reverse(solution.tour.begin() + i, solution.tour.begin() + j + 1);
                        solution.total_distance += (d_new - d_old);
                        improved = true;
                    }
                }
            }
            iter++;
        }

        metrics.iterations = iter;
        metrics.objective_value = solution.total_distance;
        metrics.is_optimal = false;
        
        return true;
    }
};

// ============================================================================
// TSP Topological Boltzmann Heuristic
// ============================================================================
class TSPTopologicalBoltzmann : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "TSP_TopologicalBoltzmann"; }

protected:
    bool solve_impl(const TSPProblem& problem, TSPSolution& solution, SolverMetrics& metrics) override {
        size_t n = problem.n_cities;
        if (n < 3) {
            TSPNearestNeighbor fallback;
            auto res = fallback.solve(problem);
            solution = res.solution;
            return res.success;
        }

        double total_dist = 0;
        size_t edge_count = 0;
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                total_dist += problem.distances[i][j];
                edge_count++;
            }
        }
        double avg_dist = total_dist / edge_count;

        std::vector<size_t> best_tour;
        double best_total = std::numeric_limits<double>::infinity();
        std::mt19937 rng(42);

        size_t n_trials = std::min((size_t)32, 1024 / n + 1);
        if (n > 256) n_trials = 1; // Faster for very large instances

        for (size_t trial = 0; trial < n_trials; ++trial) {
            std::vector<size_t> tour;
            tour.reserve(n);
            std::vector<uint64_t> visited((n + 63) / 64, 0);
            auto is_visited = [&](size_t i) { return visited[i / 64] & (1ULL << (i % 64)); };
            auto set_visited = [&](size_t i) { visited[i / 64] |= (1ULL << (i % 64)); };

            size_t curr = trial % n;
            tour.push_back(curr);
            set_visited(curr);

            size_t next_city = -1;
            double min_d = std::numeric_limits<double>::infinity();
            for (size_t i = 0; i < n; ++i) {
                if (!is_visited(i)) {
                    if (problem.distances[curr][i] < min_d) {
                        min_d = problem.distances[curr][i];
                        next_city = i;
                    }
                }
            }
            tour.push_back(next_city);
            set_visited(next_city);

            while (tour.size() < n) {
                size_t p2 = tour[tour.size() - 2];
                size_t p1 = tour.back();
                
                char last_turn = 'N';
                if (tour.size() >= 3) {
                    size_t p3 = tour[tour.size() - 3];
                    last_turn = get_turn_dir(problem.coords[p3], problem.coords[p2], problem.coords[p1]);
                }

                std::vector<std::pair<double, size_t>> candidates;
                // Optimization for large N: only check K-nearest unvisited neighbors
                // For now, simpler scan if n is not extreme
                if (n > 128) {
                    // Quick greedy for large N construction speed
                    size_t best_next = -1;
                    double best_score = std::numeric_limits<double>::infinity();
                    for (size_t i = 0; i < n; ++i) {
                        if (!is_visited(i)) {
                            double d = problem.distances[p1][i];
                            if (d < best_score) {
                                best_score = d;
                                best_next = i;
                            }
                        }
                    }
                    tour.push_back(best_next);
                    set_visited(best_next);
                } else {
                    for (size_t i = 0; i < n; ++i) {
                        if (!is_visited(i)) {
                            double d = problem.distances[p1][i];
                            double norm_d = d / avg_dist;
                            double boltz_prob = std::exp(-2.15 * norm_d);
                            
                            double topo_bias = 1.0;
                            if (last_turn != 'N') {
                                char current_turn = get_turn_dir(problem.coords[p2], problem.coords[p1], problem.coords[i]);
                                if (current_turn != last_turn) topo_bias = 1.5;
                                else topo_bias = 0.7;
                            }
                            candidates.push_back({boltz_prob * topo_bias, i});
                        }
                    }

                    double sum_w = 0;
                    for (auto& c : candidates) sum_w += c.first;
                    std::uniform_real_distribution<double> dist(0, sum_w);
                    double r = dist(rng);
                    double acc = 0;
                    size_t selected = candidates.back().second;
                    for (auto& c : candidates) {
                        acc += c.first;
                        if (r <= acc) { selected = c.second; break; }
                    }
                    tour.push_back(selected);
                    set_visited(selected);
                }
            }

            double d_total = 0;
            for (size_t i = 0; i < n; ++i) d_total += problem.distances[tour[i]][tour[(i+1)%n]];
            if (d_total < best_total) {
                best_total = d_total;
                best_tour = tour;
            }
        }

        solution.tour = best_tour;
        solution.total_distance = best_total;

        // Fast 2-Opt Refinement
        bool improved = true;
        while (improved) {
            improved = false;
            for (size_t i = 1; i < n - 1; ++i) {
                for (size_t j = i + 1; j < n; ++j) {
                    size_t a = solution.tour[i-1];
                    size_t b = solution.tour[i];
                    size_t c = solution.tour[j];
                    size_t d = solution.tour[(j+1)%n];
                    
                    double d_old = problem.distances[a][b] + problem.distances[c][d];
                    double d_new = problem.distances[a][c] + problem.distances[b][d];
                    
                    if (d_new < d_old - 1e-6) {
                        std::reverse(solution.tour.begin() + i, solution.tour.begin() + j + 1);
                        solution.total_distance += (d_new - d_old);
                        improved = true;
                    }
                }
            }
        }

        metrics.objective_value = solution.total_distance;
        metrics.is_optimal = false;
        return true;
    }

private:
    char get_turn_dir(const TSPProblem::Point& a, const TSPProblem::Point& b, const TSPProblem::Point& c) {
        double ux = b.x - a.x;
        double uy = b.y - a.y;
        double vx = c.x - b.x;
        double vy = c.y - b.y;
        double cp = ux * vy - uy * vx;
        return (cp > 0) ? 'L' : 'R';
    }
};

} // namespace optsolve
