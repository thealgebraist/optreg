#pragma once
#include "solver_base.hpp"
#include "problem_types.hpp"
#include <vector>
#include <complex>
#include <cmath>
#include <algorithm>
#include <random>
#include <iostream>

namespace optsolve {

// ============================================================================
// 1. TSP: Fourier Contour Solver (Active Contour / Snake in Fourier Domain)
// ============================================================================
// Idea: Represent path as z(t) = sum c_k * exp(i k t).
// Minimize Energy: Length + Distance to Cities.
// DE: dc_k/dt = - Gradient(Energy).
// This is effectively smoothing the path in frequency domain.

class FourierContourSolver : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "Fourier_ActiveContour"; }
    
    // Config
    int num_coeffs = 20; // Number of Fourier descriptors
    double alpha = 0.05; // Length penalty
    double beta = 1.0;  // Attraction penalty (City potential)
    double step_size = 0.1;
    int iterations = 1000;
    
protected:
    using Complex = std::complex<double>;
    
    Complex eval_fourier(const std::vector<Complex>& coeffs, double t) {
        Complex z(0,0);
        int K = (int)coeffs.size();
        for(int k=0; k<K; ++k) {
             // Index mapping: 0 -> 0, 1 -> 1, 2 -> -1, 3 -> 2, 4 -> -2...
             // Simplified: just 0..K-1 frequency? Or standard -M..M?
             // Let's use simple positive/negative pairs for closed loop.
             // c[0] is center. c[1] is fundamental +1. c[2] is -1.
             // k_freq needed.
             int freq = 0;
             if (k == 0) freq = 0;
             else if (k % 2 == 1) freq = (k+1)/2;
             else freq = -(k/2);
             
             double angle = freq * t * 2 * M_PI;
             z += coeffs[k] * std::polar(1.0, angle);
        }
        return z;
    }

    bool solve_impl(const TSPProblem& p, TSPSolution& val, SolverMetrics& m) override {
        size_t N = p.coords.size();
        if (N < 3) {
            val.tour.resize(N); std::iota(val.tour.begin(), val.tour.end(), 0);
            return true;
        }
        
        // 1. Initialize Fourier Coefficients (Circle around centroid)
        double cx=0, cy=0;
        for(auto& loc : p.coords) { cx+=loc.x; cy+=loc.y; }
        cx/=N; cy/=N;
        
        // Find radius
        double r=0;
        for(auto& loc : p.coords) r = std::max(r, std::sqrt(std::pow(loc.x-cx,2)+std::pow(loc.y-cy,2)));
        
        int K = std::min((int)N, num_coeffs);
        std::vector<Complex> coeffs(K, Complex(0,0));
        
        coeffs[0] = Complex(cx, cy); // DC component
        if (K > 1) {
            coeffs[1] = Complex(r*0.5, 0); // Fundamental (Radius)
        }
        
        // 2. Gradient Descent Evolution
        // E = alpha * Integral |z'(t)|^2 dt + beta * sum_cities dist(city, contour)
        // Actually, "Snake" usually has internal energy (smoothness) and external (image forces).
        // Here external force is attraction to nearest point on contour for each city.
        
        // Simplified Discrete Time Steps (M points on contour)
        int M = N * 2; 
        std::vector<double> T(M);
        for(int i=0; i<M; ++i) T[i] = (double)i/M;
        
        for(int iter=0; iter<iterations; ++iter) {
            m.iterations++;
            // Reconstruct points
            std::vector<Complex> z(M);
            for(int i=0; i<M; ++i) z[i] = eval_fourier(coeffs, T[i]);
            
            // Calculate Forces
            // 1. Internal Force (Shrink/Smooth) -> affects higher freqs more
            // In Fourier domain, deriv of c_k is -k^2 * c_k roughly for smoothness
            // Gradient of Length ~ k^2 c_k
            
            std::vector<Complex> grad(K, Complex(0,0));
            
            // 2. External Force (Attraction)
            // For each city, find closest point on Z, pull that point towards city
            // Force on Z[i] += sum_cities (City - Z[closest])
            // This is "Balloon" force or inverse.
            // Let's model: Every city pulls the closest point on the contour towards it.
            
            std::vector<Complex> force_z(M, Complex(0,0));
            
            std::vector<bool> city_covered(N, false);
            
            for(size_t c=0; c<N; ++c) {
                Complex city(p.coords[c].x, p.coords[c].y);
                
                // Find closest point on contour
                int best_i = -1;
                double min_d = 1e9;
                for(int i=0; i<M; ++i) {
                    double d = std::abs(z[i] - city);
                    if(d < min_d) { min_d=d; best_i=i; }
                }
                
                // Add pull force
                if(best_i != -1) {
                    force_z[best_i] += (city - z[best_i]); 
                }
            }
            
            // Convert Spatial Force to Fourier Gradient
            // Gradient c_k = sum_i force_z[i] * exp(-j w t_i) (Inverse FT roughly)
            for(int k=0; k<K; ++k) {
                int freq = 0;
                if (k == 0) freq = 0;
                else if (k % 2 == 1) freq = (k+1)/2;
                else freq = -(k/2);
                
                Complex dE_dCk_ext(0,0);
                for(int i=0; i<M; ++i) {
                    double angle = -freq * T[i] * 2 * M_PI;
                    dE_dCk_ext += force_z[i] * std::polar(1.0, angle);
                }
                dE_dCk_ext /= (double)M;
                
                // Internal Energy Gradient (Elasticity)
                // L ~ sum k^2 |c_k|^2
                Complex dE_dCk_int = coeffs[k] * (double)(freq * freq);
                
                // Update
                Complex step = beta * dE_dCk_ext - alpha * dE_dCk_int;
                coeffs[k] += step * step_size;
            }
            
            // Annealing
            alpha *= 0.999; // Less smoothing over time
        }
        
        // 3. Discretize to Tour
        // Assign each city to position in tour based on projection parameter t
        std::vector<std::pair<double, size_t>> city_pos;
        for(size_t c=0; c<N; ++c) {
             Complex city(p.coords[c].x, p.coords[c].y);
             // Find t with min dist
             // Simple search
             double best_t = 0;
             double min_d = 1e9;
             for(int i=0; i<M; ++i) {
                  double d = std::abs(eval_fourier(coeffs, (double)i/M) - city);
                  if (d < min_d) { min_d=d; best_t = (double)i/M; }
             }
             city_pos.push_back({best_t, c});
        }
        std::sort(city_pos.begin(), city_pos.end());
        
        val.tour.clear();
        for(auto& pair : city_pos) val.tour.push_back(pair.second);
        
        // Calculate length
        double len = 0;
        for(size_t i=0; i<N; ++i) {
            size_t u = val.tour[i];
            size_t v = val.tour[(i+1)%N];
            len += std::hypot(p.coords[u].x - p.coords[v].x, p.coords[u].y - p.coords[v].y);
        }
        val.total_distance = len;
        m.objective_value = len;
        
        return true;
    }
};

// ============================================================================
// 2. Coloring: Kuramoto Phase Solver (ODE / Reaction-Diffusion)
// ============================================================================
// Model: Nodes are oscillators with phase theta_i.
// Interaction: Repulsive coupling for connected nodes (Anti-synchronization).
// dtheta_i/dt = - sum_j A_ij * sin(theta_i - theta_j)
// Stable states maximize phase differences (which corresponds to coloring).

class KuramotoPhaseSolver : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Kuramoto_ODE"; }
    
    // Config
    double dt = 0.1;
    int steps = 500;
    
protected:
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        size_t N = p.n_vertices;
        std::vector<double> theta(N);
        std::vector<std::vector<size_t>> adj(N);
        for(auto& e:p.edges) { adj[e.first].push_back(e.second); adj[e.second].push_back(e.first); }
        
        // Init Random Phases 0..2PI
        std::mt19937 rng(42);
        std::uniform_real_distribution<> dist(0, 2*M_PI);
        for(size_t i=0; i<N; ++i) theta[i] = dist(rng);
        
        // Integration (Euler)
        for(int t=0; t<steps; ++t) {
            m.iterations++;
            std::vector<double> dtheta(N, 0.0);
            
            // Calculate derivatives
            for(size_t i=0; i<N; ++i) {
                for(size_t j : adj[i]) {
                    // Interaction: Repulsive force sin(theta_j - theta_i) ??
                    // Kuramoto standard: sin(theta_j - theta_i) tries to sync.
                    // We want ANTI-sync. So negative coupling.
                    // dtheta_i = - K * sin(theta_j - theta_i) = K * sin(theta_i - theta_j)
                    // Let K = 1.
                    dtheta[i] += std::sin(theta[i] - theta[j]); 
                }
            }
            
            // Update
            double max_change = 0;
            for(size_t i=0; i<N; ++i) {
                theta[i] += dtheta[i] * dt;
                max_change = std::max(max_change, std::abs(dtheta[i]*dt));
            }
            if(max_change < 1e-4) break; // Converged
        }
        
        // Discretize Phases to Colors
        // Bin phases into clusters? Or k-means on circle?
        // Simple heuristic: k=4 to start?
        // Let's iterate K=2...N until valid
        
        // Normalize phases to 0..1
        std::vector<double> normalized(N);
        for(size_t i=0; i<N; ++i) {
            double ph = std::fmod(theta[i], 2*M_PI);
            if(ph < 0) ph += 2*M_PI;
            normalized[i] = ph / (2*M_PI);
        }
        
        // Try increasing K
        for(size_t k=2; k<=N; ++k) {
             val.num_colors = k;
             val.colors.assign(N, 0);
             bool valid = true;
             
             // Assign by binning
             for(size_t i=0; i<N; ++i) {
                 val.colors[i] = (size_t)(normalized[i] * k) % k;
             }
             
             // Check conflicts
             // If conflicts, simple greedy fixup?
             // Since heuristic, just count conflicts.
             // If this solver allows invalid solutions, we return approximate.
             // But SolverBase usually implies valid.
             // Let's do a Greedy Fixup pass.
             
             ColoringGreedy g;
             // We can use the phase vector as the *ordering* for Greedy!
             // Sort by phase, then run greedy.
             // This uses the DE solution as a "Spectral Ordering".
             
             std::vector<std::pair<double, size_t>> order(N);
             for(size_t i=0; i<N; ++i) order[i] = {normalized[i], i};
             std::sort(order.begin(), order.end());
             
             std::vector<size_t> p_indices(N);
             for(size_t i=0; i<N; ++i) p_indices[i] = order[i].second;
             
             // Manual Greedy with this order
             std::vector<size_t> colors(N, 9999);
             size_t max_c = 0;
             for(size_t u : p_indices) {
                 // pick lowest free
                 std::vector<bool> used_c(N, false);
                 for(size_t v : adj[u]) {
                     if(colors[v] != 9999) used_c[colors[v]] = true;
                 }
                 size_t c = 0;
                 while(used_c[c]) c++;
                 colors[u] = c;
                 max_c = std::max(max_c, c);
             }
             
             val.colors = colors;
             val.num_colors = max_c + 1;
             m.objective_value = val.num_colors;
             return true; 
        }
        return false;
    }
};

// ============================================================================
// 3. TSP: Physarum Solver (Slime Mold Network Design)
// ============================================================================
// Model: Edges have conductivity D_ij.
// Flux Q_ij flows based on pressure difference (p_i - p_j).
// Adaptation: dD_ij/dt = |Q_ij| - D_ij.
// For TSP: We want a single loop. Standard Physarum finds shortest paths.
// We use a "Reinforcement Phase" where we simulate flow between all pairs (or adjacent in tour)
// and decay unused edges. This effectively sparsifies the graph to the "skeleton".
// Then we run a heuristic (e.g. NN) on the high-conductivity backbone.

class PhysarumTSPSolver : public Solver<TSPProblem, TSPSolution> {
public:
    std::string name() const override { return "Physarum_Network"; }
    
    int iterations = 100;
    double dt = 1.0;
    double initial_conductivity = 0.5;
    
    // Simplified Physarum Logic (Flux-based Tube Adaptation)
    // Full Kirchoff solution is O(N^3). We use a simplified local flow simulation.
    // "Agent-based Slime Mold":
    // Agents move probabilistically proportional to D_ij.
    // Trail D_ij increases when agent passes. D_ij decays over time.
    // This is computationally cheaper and similar to Ant Colony but with "Fluid" metaphor.
    
    bool solve_impl(const TSPProblem& p, TSPSolution& val, SolverMetrics& m) override {
        size_t N = p.coords.size();
        if (N < 3) return false;
        
        // Conductivity Matrix
        std::vector<std::vector<double>> D(N, std::vector<double>(N));
        // Init with inverse distance (Proximity)
        for(size_t i=0; i<N; ++i) {
            for(size_t j=0; j<N; ++j) {
                if (i!=j) D[i][j] = 1.0 / (p.distances[i][j] + 1.0);
            }
        }
        
        // Simulation: Random Walkers (representing Flow) reinforcing tubes
        // For TSP, we want to visit ALL nodes.
        // Let's spawn agents at all nodes, they move to neighbors, deposit slime.
        // Edges decay.
        // Constraint: We want a TOUR.
        // Variation: "Physarum Solver for TSP" (Aono et al.) uses complex inhibitor logic.
        // We will implemented a "Guided Flow" where flux is driven by "Unvisited" pressure?
        // Let's stick to the Classic "Agent Transport" model (like Ant Colony but continuous update):
        // dD/dt = Flux - Decay * D
        
        std::mt19937 rng(42);
        std::vector<size_t> agents(N); // 1 agent per city
        std::iota(agents.begin(), agents.end(), 0);
        
        for(int t=0; t<iterations; ++t) {
            m.iterations++;
            std::vector<std::vector<double>> flux(N, std::vector<double>(N, 0.0));
            
            // Move Agents
            for(size_t& curr : agents) {
                // Pick neighbor prob proportional to D
                double sum_d = 0;
                for(size_t j=0; j<N; ++j) if(curr!=j) sum_d += D[curr][j];
                
                std::uniform_real_distribution<> dist(0, sum_d);
                double r = dist(rng);
                double acc = 0;
                size_t next = curr;
                for(size_t j=0; j<N; ++j) {
                    if(curr!=j) {
                        acc += D[curr][j];
                        if(r <= acc) { next = j; break; }
                    }
                }
                
                // Record Flux (bi-directional)
                flux[curr][next] += 1.0;
                flux[next][curr] += 1.0;
                curr = next;
            }
            
            // Update Conductivity
            for(size_t i=0; i<N; ++i) {
                for(size_t j=0; j<N; ++j) {
                     // dD = Flux - Decay
                     // Here: D = D + (Flux - D) * dt
                     double change = (flux[i][j] - D[i][j]);
                     D[i][j] += change * dt * 0.1; 
                     if(D[i][j] < 1e-5) D[i][j] = 1e-5; // Non-zero floor
                }
            }
        }
        
        // Extract Tour from High-Conductivity Backbone
        // Prims/Greedy on D matrix (Max Conductivity = Min Distance)
        std::vector<bool> visited(N, false);
        val.tour.clear();
        size_t curr = 0;
        visited[curr] = true;
        val.tour.push_back(curr);
        
        for(size_t i=0; i<N-1; ++i) {
            double max_D = -1.0;
            size_t best_next = 0;
            for(size_t j=0; j<N; ++j) {
                if(!visited[j]) {
                    if(D[curr][j] > max_D) { max_D = D[curr][j]; best_next = j; }
                }
            }
            curr = best_next;
            visited[curr] = true;
            val.tour.push_back(curr);
        }
        
        // Distance
        double len = 0;
        for(size_t i=0; i<N; ++i) {
            size_t u = val.tour[i];
            size_t v = val.tour[(i+1)%N];
            len += p.distances[u][v];
        }
        val.total_distance = len;
        m.objective_value = len;
        return true;
    }
};

// ============================================================================
// 4. Coloring: Physarum Coloring (Competitive Nutrient Flow)
// ============================================================================
// Model: Each Color is a "Nutrient Type".
// Nodes have capacity for nutrients.
// Edges transmit inhibition? or Shared Resource?
// Let's model it as "Competitive Species". Species K wants to occupy Node I.
// Growth of K at Node I is inhibited by presence of K at Neighbors.
// dX_i,k / dt = X_i,k * ( 1 - X_i,k - sum_j A_ij * X_j,k )
// This is Lotka-Volterra competition.
// If X_i,k > 0, then Species K occupies Node I.
// Inhibition term sum_j A_ij * X_j,k ensures neighbors don't have same species.

class PhysarumColoringSolver : public Solver<GraphColoringProblem, GraphColoringSolution> {
public:
    std::string name() const override { return "Physarum_Competitive"; }
    
    int max_colors = 20; // Pool size
    int w_iterations = 200;
    double dt = 0.1;
    
    bool solve_impl(const GraphColoringProblem& p, GraphColoringSolution& val, SolverMetrics& m) override {
        size_t N = p.n_vertices;
        size_t K = p.n_vertices; // Start with N potential colors
        if(K > 64) K = 64; // Limit for performance
        
        // X[i][k] = biomass of color k at node i
        // Init with random noise
        std::vector<std::vector<double>> X(N, std::vector<double>(K));
        std::mt19937 rng(42);
        std::uniform_real_distribution<> noise(0.01, 0.1);
        for(size_t i=0; i<N; ++i) 
             for(size_t k=0; k<K; ++k) X[i][k] = noise(rng);
             
        std::vector<std::vector<size_t>> adj(N);
        for(auto& e:p.edges) { adj[e.first].push_back(e.second); adj[e.second].push_back(e.first); }
        
        // Evolution
        for(int t=0; t<w_iterations; ++t) {
             m.iterations++;
             std::vector<std::vector<double>> dX(N, std::vector<double>(K));
             
             for(size_t i=0; i<N; ++i) {
                 double local_sum = 0; 
                 // Sum of all species at node i (We want exactly 1 species to win, so they compete locally too?)
                 // Yes, soft exclusion locally: sum_k X_i,k <= 1
                 // Term: (1 - sum_all_k X_i,k)
                 
                 for(size_t k=0; k<K; ++k) local_sum += X[i][k];
                 
                 for(size_t k=0; k<K; ++k) {
                     double neighbor_inhibition = 0;
                     for(size_t j : adj[i]) neighbor_inhibition += X[j][k];
                     
                     // Growth = X * (GrowthRate - LocalCompetition - NeighborInhibition)
                     // GrowthRate = 1.0 (Intrinsic)
                     // LocalCompetition = sum of other colors (forces 1 color per node)
                     // NeighborInhibition = alpha * sum of SAME color neighbors (forces valid coloring)
                     
                     double growth = 1.0 - local_sum - 2.0 * neighbor_inhibition; 
                     dX[i][k] = X[i][k] * growth; 
                 }
             }
             
             // Update
             for(size_t i=0; i<N; ++i) {
                 for(size_t k=0; k<K; ++k) {
                     X[i][k] += dX[i][k] * dt;
                     if(X[i][k] < 0.001) X[i][k] = 0.001; // Floor
                     if(X[i][k] > 1.0) X[i][k] = 1.0; // Cap
                 }
             }
        }
        
        // Extract Colors (Dominant Species)
        val.colors.assign(N, 0);
        size_t used_k = 0;
        
        for(size_t i=0; i<N; ++i) {
             size_t best_k = 0;
             double max_val = -1;
             for(size_t k=0; k<K; ++k) {
                 if(X[i][k] > max_val) { max_val = X[i][k]; best_k = k; }
             }
             val.colors[i] = best_k;
             if(best_k >= used_k) used_k = best_k;
        }
        
        // Validate & Fix (Greedy cleanup)
        // Similar to Kuramoto, the dynamics might not be perfectly valid due to local minima.
        // We do a conflict check.
        val.num_colors = 0;
        for(size_t i=0; i<N; ++i) {
            bool conflict = false;
            for(size_t j : adj[i]) if(val.colors[i] == val.colors[j]) conflict = true;
            if (conflict) {
                // Pick mex
                std::vector<bool> used_c(K+1, false);
                for(size_t n : adj[i]) used_c[val.colors[n]] = true;
                size_t c = 0; while(used_c[c]) c++;
                val.colors[i] = c;
            }
            if(val.colors[i] >= val.num_colors) val.num_colors = val.colors[i] + 1;
        }
        
        m.objective_value = val.num_colors;
        return true;
    }
};

}
