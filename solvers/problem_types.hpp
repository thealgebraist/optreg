#pragma once
#include <vector>
#include <random>
#include <set>
#include <algorithm>
#include <cmath>

namespace optsolve {

// ============================================================================
// TSP (Traveling Salesperson Problem)
// ============================================================================
struct TSPProblem {
    struct Point { double x, y; };
    size_t n_cities;
    std::vector<Point> coords;
    std::vector<std::vector<double>> distances; // n x n distance matrix
    
    static TSPProblem random(size_t n, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::uniform_real_distribution<double> dist_gen(0.0, 100.0);
        
        TSPProblem p;
        p.n_cities = n;
        p.coords.resize(n);
        p.distances.resize(n, std::vector<double>(n, 0.0));
        
        for (size_t i = 0; i < n; ++i) {
            p.coords[i] = {dist_gen(rng), dist_gen(rng)};
        }
        
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                double d = std::sqrt(std::pow(p.coords[i].x - p.coords[j].x, 2) +
                                   std::pow(p.coords[i].y - p.coords[j].y, 2));
                p.distances[i][j] = d;
                p.distances[j][i] = d;
            }
        }
        return p;
    }
};

struct TSPSolution {
    std::vector<size_t> tour; // Sequence of city indices
    double total_distance;
    
    bool is_valid(const TSPProblem& problem) const {
        if (tour.size() != problem.n_cities) return false;
        std::set<size_t> visited(tour.begin(), tour.end());
        return visited.size() == problem.n_cities;
    }
};

// ============================================================================
// Knapsack Problem
// ============================================================================
struct KnapsackProblem {
    size_t n_items;
    std::vector<double> values;
    std::vector<double> weights;
    double capacity;
    
    static KnapsackProblem random(size_t n, double cap_ratio = 0.5, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::uniform_real_distribution<double> val_dist(1.0, 100.0);
        std::uniform_real_distribution<double> wgt_dist(1.0, 50.0);
        
        KnapsackProblem p;
        p.n_items = n;
        p.values.resize(n);
        p.weights.resize(n);
        
        double total_weight = 0;
        for (size_t i = 0; i < n; ++i) {
            p.values[i] = val_dist(rng);
            p.weights[i] = wgt_dist(rng);
            total_weight += p.weights[i];
        }
        p.capacity = total_weight * cap_ratio;
        return p;
    }
};

struct KnapsackSolution {
    std::vector<bool> selected; // selected[i] = true if item i is in knapsack
    double total_value;
    double total_weight;
    
    bool is_valid(const KnapsackProblem& problem) const {
        if (selected.size() != problem.n_items) return false;
        return total_weight <= problem.capacity + 1e-6;
    }
};

// ============================================================================
// Boolean SAT
// ============================================================================
struct SATProblem {
    size_t n_vars;
    size_t n_clauses;
    std::vector<std::vector<int>> clauses; // clauses[i] = list of literals (positive = var, negative = ~var)
    
    static SATProblem random(size_t n_vars, size_t n_clauses, size_t clause_size = 3, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::uniform_int_distribution<int> var_dist(1, n_vars);
        std::bernoulli_distribution sign_dist(0.5);
        
        SATProblem p;
        p.n_vars = n_vars;
        p.n_clauses = n_clauses;
        p.clauses.resize(n_clauses);
        
        for (size_t i = 0; i < n_clauses; ++i) {
            std::set<size_t> used;
            for (size_t j = 0; j < clause_size && used.size() < clause_size; ++j) {
                size_t var = var_dist(rng);
                if (used.count(var)) continue;
                used.insert(var);
                int lit = sign_dist(rng) ? var : -static_cast<int>(var);
                p.clauses[i].push_back(lit);
            }
        }
        return p;
    }
};

struct SATSolution {
    std::vector<bool> assignment; // assignment[i] = value of variable i+1
    size_t satisfied_clauses;
    
    bool is_valid(const SATProblem& problem) const {
        return assignment.size() == problem.n_vars;
    }
};

// ============================================================================
// Graph Coloring
// ============================================================================
struct GraphColoringProblem {
    size_t n_vertices;
    std::vector<std::pair<size_t, size_t>> edges;
    
    static GraphColoringProblem random(size_t n, double edge_prob = 0.3, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::bernoulli_distribution dist(edge_prob);
        
        GraphColoringProblem p;
        p.n_vertices = n;
        
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                if (dist(rng)) {
                    p.edges.emplace_back(i, j);
                }
            }
        }
        return p;
    }
};

struct GraphColoringSolution {
    std::vector<size_t> colors; // colors[i] = color of vertex i
    size_t num_colors;
    
    bool is_valid(const GraphColoringProblem& problem) const {
        if (colors.size() != problem.n_vertices) return false;
        for (const auto& [u, v] : problem.edges) {
            if (colors[u] == colors[v]) return false;
        }
        return true;
    }
};

// ============================================================================
// Vertex Cover
// ============================================================================
struct VertexCoverProblem {
    size_t n_vertices;
    std::vector<std::pair<size_t, size_t>> edges;
    
    static VertexCoverProblem random(size_t n, double edge_prob = 0.3, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::bernoulli_distribution dist(edge_prob);
        
        VertexCoverProblem p;
        p.n_vertices = n;
        
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                if (dist(rng)) {
                    p.edges.emplace_back(i, j);
                }
            }
        }
        return p;
    }
};

struct VertexCoverSolution {
    std::vector<bool> in_cover; // in_cover[i] = true if vertex i is in cover
    size_t cover_size;
    
    bool is_valid(const VertexCoverProblem& problem) const {
        if (in_cover.size() != problem.n_vertices) return false;
        for (const auto& [u, v] : problem.edges) {
            if (!in_cover[u] && !in_cover[v]) return false;
        }
        return true;
    }
};

// ============================================================================
// Clique Problem
// ============================================================================
struct CliqueProblem {
    size_t n_vertices;
    std::vector<std::pair<size_t, size_t>> edges;
    
    static CliqueProblem random(size_t n, double edge_prob = 0.5, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::bernoulli_distribution dist(edge_prob);
        
        CliqueProblem p;
        p.n_vertices = n;
        
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                if (dist(rng)) {
                    p.edges.emplace_back(i, j);
                }
            }
        }
        return p;
    }
};

struct CliqueSolution {
    std::vector<size_t> vertices; // Vertices in the clique
    size_t clique_size;
    
    bool is_valid(const CliqueProblem& problem) const {
        std::set<std::pair<size_t, size_t>> edge_set;
        for (const auto& [u, v] : problem.edges) {
            edge_set.emplace(std::min(u, v), std::max(u, v));
        }
        
        for (size_t i = 0; i < vertices.size(); ++i) {
            for (size_t j = i + 1; j < vertices.size(); ++j) {
                size_t u = vertices[i], v = vertices[j];
                if (!edge_set.count({std::min(u, v), std::max(u, v)})) {
                    return false;
                }
            }
        }
        return true;
    }
};

// ============================================================================
// Hamiltonian Cycle
// ============================================================================
struct HamiltonianProblem {
    size_t n_vertices;
    std::vector<std::pair<size_t, size_t>> edges;
    
    static HamiltonianProblem random(size_t n, double edge_prob = 0.4, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::bernoulli_distribution dist(edge_prob);
        
        HamiltonianProblem p;
        p.n_vertices = n;
        
        // Ensure Hamiltonian cycle exists by creating a cycle first
        for (size_t i = 0; i < n; ++i) {
            p.edges.emplace_back(i, (i + 1) % n);
        }
        
        // Add random edges
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 2; j < n; ++j) {
                if ((i == 0 && j == n - 1)) continue; // Skip if would duplicate cycle edge
                if (dist(rng)) {
                    p.edges.emplace_back(i, j);
                }
            }
        }
        return p;
    }
};

struct HamiltonianSolution {
    std::vector<size_t> cycle;
    bool exists;
    
    bool is_valid(const HamiltonianProblem& problem) const {
        if (!exists) return true; // No cycle found is valid answer
        if (cycle.size() != problem.n_vertices) return false;
        
        std::set<std::pair<size_t, size_t>> edge_set;
        for (const auto& [u, v] : problem.edges) {
            edge_set.emplace(std::min(u, v), std::max(u, v));
        }
        
        for (size_t i = 0; i < cycle.size(); ++i) {
            size_t u = cycle[i];
            size_t v = cycle[(i + 1) % cycle.size()];
            if (!edge_set.count({std::min(u, v), std::max(u, v)})) {
                return false;
            }
        }
        return true;
    }
};

// ============================================================================
// Set Cover
// ============================================================================
struct SetCoverProblem {
    size_t n_elements;
    size_t n_sets;
    std::vector<std::vector<size_t>> sets; // sets[i] = elements in set i
    
    static SetCoverProblem random(size_t n_elem, size_t n_sets, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::bernoulli_distribution dist(0.3);
        
        SetCoverProblem p;
        p.n_elements = n_elem;
        p.n_sets = n_sets;
        p.sets.resize(n_sets);
        
        // Ensure all elements are covered
        for (size_t e = 0; e < n_elem; ++e) {
            std::uniform_int_distribution<size_t> set_dist(0, n_sets - 1);
            size_t s = set_dist(rng);
            p.sets[s].push_back(e);
        }
        
        // Add random coverage
        for (size_t s = 0; s < n_sets; ++s) {
            for (size_t e = 0; e < n_elem; ++e) {
                if (dist(rng)) {
                    p.sets[s].push_back(e);
                }
            }
        }
        return p;
    }
};

struct SetCoverSolution {
    std::vector<bool> selected_sets;
    size_t num_sets_used;
    
    bool is_valid(const SetCoverProblem& problem) const {
        if (selected_sets.size() != problem.n_sets) return false;
        
        std::set<size_t> covered;
        for (size_t i = 0; i < problem.n_sets; ++i) {
            if (selected_sets[i]) {
                for (size_t e : problem.sets[i]) {
                    covered.insert(e);
                }
            }
        }
        return covered.size() == problem.n_elements;
    }
};

// ============================================================================
// Subset Sum
// ============================================================================
struct SubsetSumProblem {
    std::vector<int> numbers;
    int target;
    
    static SubsetSumProblem random(size_t n, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::uniform_int_distribution<int> dist(1, 100);
        
        SubsetSumProblem p;
        p.numbers.resize(n);
        
        int sum = 0;
        for (size_t i = 0; i < n; ++i) {
            p.numbers[i] = dist(rng);
            sum += p.numbers[i];
        }
        
        // Target is roughly half the total sum
        std::uniform_int_distribution<int> target_dist(sum / 3, 2 * sum / 3);
        p.target = target_dist(rng);
        
        return p;
    }
};

struct SubsetSumSolution {
    std::vector<bool> selected;
    int sum;
    bool exists;
    
    bool is_valid(const SubsetSumProblem& problem) const {
        if (!exists) return true; // No solution found is valid
        if (selected.size() != problem.numbers.size()) return false;
        
        int computed_sum = 0;
        for (size_t i = 0; i < selected.size(); ++i) {
            if (selected[i]) {
                computed_sum += problem.numbers[i];
            }
        }
        return computed_sum == problem.target;
    }
};

// ============================================================================
// Steiner Tree
// ============================================================================
struct SteinerTreeProblem {
    size_t n_vertices;
    std::vector<std::tuple<size_t, size_t, double>> edges; // (u, v, weight)
    std::vector<size_t> terminals; // Required vertices
    
    static SteinerTreeProblem random(size_t n, size_t n_terminals, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::uniform_real_distribution<double> weight_dist(1.0, 10.0);
        std::bernoulli_distribution edge_dist(0.4);
        
        SteinerTreeProblem p;
        p.n_vertices = n;
        
        // Create edges
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = i + 1; j < n; ++j) {
                if (edge_dist(rng)) {
                    p.edges.emplace_back(i, j, weight_dist(rng));
                }
            }
        }
        
        // Select terminals
        std::vector<size_t> vertices(n);
        std::iota(vertices.begin(), vertices.end(), 0);
        std::shuffle(vertices.begin(), vertices.end(), rng);
        p.terminals.assign(vertices.begin(), vertices.begin() + std::min(n_terminals, n));
        
        return p;
    }
};

struct SteinerTreeSolution {
    std::vector<std::tuple<size_t, size_t, double>> tree_edges;
    double total_weight;
    
    bool is_valid(const SteinerTreeProblem& problem) const {
        // Build adjacency list from solution
        std::vector<std::vector<size_t>> adj(problem.n_vertices);
        for (const auto& [u, v, w] : tree_edges) {
            adj[u].push_back(v);
            adj[v].push_back(u);
        }
        
        // Check if all terminals are connected via DFS from first terminal
        if (problem.terminals.empty()) return true;
        
        std::vector<bool> visited(problem.n_vertices, false);
        std::vector<size_t> stack = {problem.terminals[0]};
        visited[problem.terminals[0]] = true;
        
        while (!stack.empty()) {
            size_t v = stack.back();
            stack.pop_back();
            for (size_t u : adj[v]) {
                if (!visited[u]) {
                    visited[u] = true;
                    stack.push_back(u);
                }
            }
        }
        
        for (size_t t : problem.terminals) {
            if (!visited[t]) return false;
        }
        
        return true;
    }
};

// ============================================================================
// Server Optimization
// ============================================================================
struct ServerProblem {
    struct Server { size_t id; double cost; double capacity; double x, y; };
    struct UserGroup { size_t id; double demand; double x, y; };
    
    std::vector<Server> servers;
    std::vector<UserGroup> groups;
    double u_target;
    double sla_limit;
    double z_score;
    
    static ServerProblem random(size_t n_servers, size_t n_groups, unsigned seed = 42) {
        std::mt19937 rng(seed);
        std::uniform_real_distribution<double> pos_dist(0, 100);
        std::uniform_real_distribution<double> cost_dist(100, 500);
        std::uniform_real_distribution<double> cap_dist(500, 2000);
        std::uniform_real_distribution<double> demand_dist(100, 500);
        
        ServerProblem p;
        p.u_target = 0.5;
        p.sla_limit = 10.0;
        p.z_score = 1.645;
        
        for (size_t i = 0; i < n_servers; ++i) {
            p.servers.push_back({i, cost_dist(rng), cap_dist(rng), pos_dist(rng), pos_dist(rng)});
        }
        for (size_t i = 0; i < n_groups; ++i) {
            p.groups.push_back({i, demand_dist(rng), pos_dist(rng), pos_dist(rng)});
        }
        return p;
    }
};

struct ServerSolution {
    std::vector<size_t> server_assignment; // server_assignment[group_id] = server_id
    std::vector<bool> active_servers;      // active_servers[server_id] = true if active
    double total_cost;
    
    bool is_valid(const ServerProblem& problem) const {
        if (server_assignment.size() != problem.groups.size()) return false;
        if (active_servers.size() != problem.servers.size()) return false;
        
        std::vector<double> load(problem.servers.size(), 0.0);
        for (size_t g = 0; g < problem.groups.size(); ++g) {
            size_t s = server_assignment[g];
            if (s >= problem.servers.size()) return false;
            if (!active_servers[s]) return false;
            
            // SLA check
            double dx = problem.groups[g].x - problem.servers[s].x;
            double dy = problem.groups[g].y - problem.servers[s].y;
            double dist = std::sqrt(dx*dx + dy*dy);
            double mu = dist * 0.1;
            double sigma = mu * 0.1;
            if (mu + problem.z_score * sigma > problem.sla_limit + 1e-6) return false;
            
            load[s] += problem.groups[g].demand;
        }
        
        for (size_t s = 0; s < problem.servers.size(); ++s) {
            if (active_servers[s]) {
                if (load[s] > problem.servers[s].capacity + 1e-6) return false;
                if (load[s] < problem.u_target * problem.servers[s].capacity - 1e-6) return false;
            } else {
                if (load[s] > 1e-6) return false;
            }
        }
        return true;
    }
};

} // namespace optsolve
