#include "tsp_solver.h"
#include <iostream>
#include <numeric>
#include <algorithm>

namespace optreg {

double compute_ap_lower_bound(const TSPInstance& instance, std::vector<double>& pi, std::vector<double>& sigma) {
    int n = instance.dimension;
    pi.assign(n, 1e18);
    sigma.assign(n, 1e18);
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            if (i == j) continue;
            pi[i] = std::min(pi[i], instance.adj[i][j]);
        }
    }
    for (int j = 0; j < n; ++j) {
        for (int i = 0; i < n; ++i) {
            if (i == j) continue;
            sigma[j] = std::min(sigma[j], instance.adj[i][j] - pi[i]);
        }
    }
    double lb = 0;
    for (int i = 0; i < n; ++i) lb += pi[i];
    for (int j = 0; j < n; ++j) lb += sigma[j];
    return lb;
}

LPProblem TSPSolver::formulate_ip(const TSPInstance& instance) {
    int n = instance.dimension;
    if (n < 2) return {};

    // Preprocessing
    std::vector<double> pi, sigma;
    double lb_ap = compute_ap_lower_bound(instance, pi, sigma);
    double heuristic_ub = 0;
    std::vector<bool> visited(n, false);
    int curr = 0; visited[0] = true;
    for (int step = 1; step < n; ++step) {
        int next = -1; double min_d = 1e18;
        for (int j = 0; j < n; ++j) {
            if (!visited[j] && instance.adj[curr][j] < min_d) { min_d = instance.adj[curr][j]; next = j; }
        }
        if (next == -1) break;
        visited[next] = true; heuristic_ub += min_d; curr = next;
    }
    heuristic_ub += instance.adj[curr][0];

    // Variables: x[i*n + j], u[i], slacks for MTZ constraints, slacks for upper bounds
    int n_edges = n * n;
    int n_u = n - 1;
    int n_mtz = (n - 1) * (n - 2);
    int n_upper_slacks = n_edges + n_u; // One slack per bounded variable
    int total_vars = n_edges + n_u + n_mtz + n_upper_slacks;

    LPProblem prob;
    prob.c = Vector::Zero(total_vars);
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            prob.c(i * n + j) = instance.adj[i][j];
        }
    }
    
    std::vector<Eigen::Triplet<double>> triplets;
    std::vector<double> b_values;
    int constraint_idx = 0;
    int slack_idx = n_edges + n_u;

    // 1. Outgoing degree constraints (all n nodes)
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) triplets.push_back({constraint_idx, i * n + j, 1.0});
        b_values.push_back(1.0);
        constraint_idx++;
    }

    // 2. Incoming degree constraints (n-1 nodes, skip last to remove linear dependence)
    for (int j = 0; j < n - 1; ++j) {
        for (int i = 0; i < n; ++i) triplets.push_back({constraint_idx, i * n + j, 1.0});
        b_values.push_back(1.0);
        constraint_idx++;
    }

    // 3. MTZ subtour elimination: u_i - u_j + n*x_ij <= n-1
    // For i, j in {1, ..., n-1}, i != j
    for (int i = 1; i < n; ++i) {
        for (int j = 1; j < n; ++j) {
            if (i == j) continue;
            int u_i_idx = n_edges + (i - 1);
            int u_j_idx = n_edges + (j - 1);
            int x_ij_idx = i * n + j;
            
            triplets.push_back({constraint_idx, u_i_idx, 1.0});
            triplets.push_back({constraint_idx, u_j_idx, -1.0});
            triplets.push_back({constraint_idx, x_ij_idx, (double)n});
            triplets.push_back({constraint_idx, slack_idx, 1.0});
            
            b_values.push_back((double)(n - 1));
            constraint_idx++;
            slack_idx++;
        }
    }

    // 4. Upper bound constraints: x_ij + slack = 1.0 (or 0 for self-loops)
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            triplets.push_back({constraint_idx, i * n + j, 1.0});
            triplets.push_back({constraint_idx, slack_idx++, 1.0});
            b_values.push_back((i == j) ? 0.0 : 1.0);
            constraint_idx++;
        }
    }
    
    // 5. Upper bound constraints for u: u_i + slack = (n-1)
    for (int i = 0; i < n_u; ++i) {
        triplets.push_back({constraint_idx, n_edges + i, 1.0});
        triplets.push_back({constraint_idx, slack_idx++, 1.0});
        b_values.push_back((double)(n - 1));
        constraint_idx++;
    }

    prob.A.resize(constraint_idx, total_vars);
    prob.A.setFromTriplets(triplets.begin(), triplets.end());
    prob.b.resize(constraint_idx);
    for (int i = 0; i < constraint_idx; ++i) prob.b(i) = b_values[i];

    // Allocate and initialize bound vectors
    prob.lower_bound.resize(total_vars);
    prob.upper_bound.resize(total_vars);
    
    for (int i = 0; i < total_vars; ++i) {
        prob.lower_bound(i) = 0.0;
        prob.upper_bound(i) = 1e15;
    }
    
    // u variables have lower bound of 1
    for (int i = 0; i < n_u; ++i) {
        prob.lower_bound(n_edges + i) = 1.0;
    }

    return prob;
}

std::vector<int> TSPSolver::extract_tour(const Vector& x, int n) {
    std::vector<int> tour;
    if (x.size() < n * n) return tour;
    int curr = 0; std::vector<bool> visited(n, false);
    for (int step = 0; step < n; ++step) {
        tour.push_back(curr); visited[curr] = true;
        int next_node = -1; double max_val = 0.5;
        for (int j = 0; j < n; ++j) {
            if (!visited[j] && x(curr * n + j) > max_val) { max_val = x(curr * n + j); next_node = j; }
        }
        if (next_node == -1) break;
        curr = next_node;
    }
    return tour;
}

} // namespace optreg
