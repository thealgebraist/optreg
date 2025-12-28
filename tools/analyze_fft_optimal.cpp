#include <iostream>
#include <vector>
#include <complex>
#include <cmath>
#include <algorithm>
#include <fstream>
#include <iomanip>
#include <numeric>

#include "problem_types.hpp"
#include "solver_base.hpp"
#include "tsp_solvers.hpp"
#include "coloring_solvers.hpp"

// Accelerate / LAPACK for Eigenvalues
#ifdef ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#else
// Mock or simple solver if unavailable, but we assume environment has it.
// For N=20 we can implement simple Jacobi.
#endif

using namespace optsolve;

// Simple Jacobi Eigenvalue Algorithm (reused from test_metaheuristics)
std::pair<std::vector<double>, std::vector<std::vector<double>>> compute_eigen(const std::vector<std::vector<double>>& A) {
    int n = A.size();
    std::vector<std::vector<double>> V(n, std::vector<double>(n, 0.0));
    for(int i=0; i<n; ++i) V[i][i] = 1.0;
    std::vector<std::vector<double>> D = A;
    
    int max_iter = 100; // Sufficient for small N
    for(int iter=0; iter<max_iter; ++iter) {
        double max_off = 0;
        int p=0, q=0;
        for(int i=0; i<n; ++i) {
            for(int j=i+1; j<n; ++j) {
                if(std::abs(D[i][j]) > max_off) { max_off = std::abs(D[i][j]); p=i; q=j; }
            }
        }
        if(max_off < 1e-9) break;
        
        double phi = 0.5 * std::atan2(2*D[p][q], D[q][q] - D[p][p]);
        double c = std::cos(phi);
        double s = std::sin(phi);
        
        // Rotate D
        // (This is O(N) per rotation, total O(N^3) roughly)
        // Simplified update for D_pp, D_qq, D_pq
        // Full update for rows/cols p, q
        // ... (Omitting full implementation for brevity, assuming generic Jacobi works)
        // Actually, let's implement the full update for correctness.
        
        std::vector<double> d_p_row(n), d_q_row(n);
        for(int k=0; k<n; ++k) { d_p_row[k] = D[p][k]; d_q_row[k] = D[q][k]; }
        
        D[p][p] = c*c*d_p_row[p] + s*s*d_q_row[q] + 2*c*s*d_p_row[q];
        D[q][q] = s*s*d_p_row[p] + c*c*d_q_row[q] - 2*c*s*d_p_row[q];
        D[p][q] = 0;
        D[q][p] = 0;
        
        for(int k=0; k<n; ++k) {
            if(k!=p && k!=q) {
                D[p][k] = c*d_p_row[k] + s*d_q_row[k];
                D[k][p] = D[p][k];
                D[q][k] = -s*d_p_row[k] + c*d_q_row[k];
                D[k][q] = D[q][k];
            }
        }
        
        // Update V
        // V_new = V * R
        for(int k=0; k<n; ++k) {
            double v_kp = V[k][p];
            double v_kq = V[k][q];
            V[k][p] = c*v_kp + s*v_kq;
            V[k][q] = -s*v_kp + c*v_kq;
        }
    }
    
    std::vector<double> evals(n);
    for(int i=0; i<n; ++i) evals[i] = D[i][i];
    return {evals, V};
}

// FFT (Simple O(N^2) DFT)
std::vector<std::complex<double>> compute_dft(const std::vector<std::complex<double>>& x) {
    size_t N = x.size();
    std::vector<std::complex<double>> X(N);
    const std::complex<double> J(0, 1);
    for(size_t k=0; k<N; ++k) {
        for(size_t n=0; n<N; ++n) {
            double angle = -2.0 * M_PI * k * n / N;
            X[k] += x[n] * std::exp(J * angle);
        }
        X[k] /= (double)N; // Scale? Usually 1/N for inverse, or unitary. Keep raw or 1/N. 
        // Let's normalize by N to get "Average Radius" logic.
    }
    return X;
}

int main() {
    std::ofstream csv("fft_analysis.csv");
    csv << "problem,id,cost,fft_c1,fft_c2,fft_c3,fft_c4,spec_lambda2,spec_gap\n";
    
    // 1. TSP Optimal FFT Analysis
    // N=20 allows fast Branch & Bound
    std::cout << "Analyzing TSP Optimal Tours (N=20)...\n";
    TSPBranchBound tsp_bnb;
    
    for(int i=0; i<128; ++i) {
        TSPProblem p = TSPProblem::random(20, i);
        auto sol = tsp_bnb.solve(p);
        
        // Construct Tour Signal z[n]
        std::vector<std::complex<double>> z(p.n_cities);
        for(size_t n=0; n<p.n_cities; ++n) {
            size_t city_idx = sol.solution.tour[n];
            z[n] = std::complex<double>(p.coords[city_idx].x, p.coords[city_idx].y);
        }
        
        // Compute DFT
        auto Z = compute_dft(z);
        
        // Extract features (Magnitudes of low frequencies)
        // Z[0] is centroid (DC). Z[1] is +1 freq (Fundamental). Z[N-1] is -1 freq.
        // We care about magnitude |Z[k]| + |Z[N-k]| (Energy at freq k).
        
        double mag_c1 = std::abs(Z[1]) + std::abs(Z[p.n_cities-1]);
        double mag_c2 = std::abs(Z[2]) + std::abs(Z[p.n_cities-2]);
        double mag_c3 = std::abs(Z[3]) + std::abs(Z[p.n_cities-3]);
        double mag_c4 = std::abs(Z[4]) + std::abs(Z[p.n_cities-4]);
        
        csv << "TSP," << i << "," << sol.solution.total_distance << ","
            << mag_c1 << "," << mag_c2 << "," << mag_c3 << "," << mag_c4 << ",0,0\n";
    }
    
    // 2. Coloring Optimal Spectral Analysis
    // N=20
    std::cout << "Analyzing Coloring Optimal Solutions (N=20) (using DSatur proxy)...\n";
    ColoringDSATUR col_bnb;
    
    for(int i=0; i<128; ++i) {
        GraphColoringProblem p = GraphColoringProblem::random(20, 0.3, i+1000);
        auto sol = col_bnb.solve(p);
        
        // Compute Eigenvalues of Adjacency Matrix
        std::vector<std::vector<double>> A(p.n_vertices, std::vector<double>(p.n_vertices, 0.0));
        for(auto& e : p.edges) {
            A[e.first][e.second] = 1.0;
            A[e.second][e.first] = 1.0;
        }
        
        auto [evals, evecs] = compute_eigen(A);
        std::sort(evals.begin(), evals.end());
        
        // Features
        double lambda2 = evals[1]; // 2nd smallest? For Adj matrix, usually largest are important.
        // For Laplacian, lambda2 is Fiedler.
        // For Adj, largest is max_ev.
        // Let's log largest and gap.
        double max_ev = evals.back();
        double gap = evals.back() - evals[evals.size()-2];
        
        // Also "Signal Smoothness"
        // GFT of color signal c[v]?
        // Signal f[v] = color[v].
        // f_hat = U^T f.
        // High frequency content = sum (f_hat_k)^2 for large lambda_k.
        
        // Let's compute "Rayleigh Quotient" R(f) = f^T L f / f^T f  -> Smoothness.
        // For coloring, we want f^T A f to be minimized? (Neighbors have diff colors -> f_i != f_j)
        // If independent set, f^T A f = 0.
        // Here f is integer color... maybe indicator vectors?
        // Let's just log eigenvalues for now as requested.
        
        csv << "Coloring," << i << "," << sol.solution.num_colors << ",0,0,0,0,"
            << lambda2 << "," << gap << "\n";
    }
    
    csv.close();
    std::cout << "Done.\n";
    return 0;
}
