#include <iostream>
#include <vector>
#include <chrono>
#include <random>
#include <fstream>
#include <iomanip>
#include <numeric>
#include <bitset>
#include <Accelerate/Accelerate.h>

#include "problem_types.hpp"
#include "solver_base.hpp"
#include "coloring_solvers.hpp"
#include "metaheuristics.hpp"
#include "bit_solvers.hpp"
#include "learned_heuristics.hpp"

// Re-define Optimal locally for speed/simplicity or include
// Using the AMX one from before
class OptimalSolver : public optsolve::Solver<optsolve::GraphColoringProblem, optsolve::GraphColoringSolution> {
public:
    std::string name() const override { return "Optimal_BnB"; }
protected:
    struct Node {
        std::vector<size_t> colors;
        int level;
        size_t max_color_used;
        double lb;
        bool operator>(const Node& o) const { return lb > o.lb; }
    };
    bool solve_impl(const optsolve::GraphColoringProblem& p, optsolve::GraphColoringSolution& val, optsolve::SolverMetrics& m) override {
        // Simple timeout-limited BnB
        size_t n = p.n_vertices;
        std::vector<std::vector<bool>> adj(n, std::vector<bool>(n,false));
        for(auto& e:p.edges) { adj[e.first][e.second]=adj[e.second][e.first]=true; }
        
        std::priority_queue<Node, std::vector<Node>, std::greater<Node>> pq;
        Node root; root.colors.assign(n,0); root.level=0; root.max_color_used=0; root.lb=1;
        pq.push(root);
        
        size_t best_k = n+1;
        std::vector<size_t> best_sol(n,0);
        
        auto start = std::chrono::steady_clock::now();
        m.iterations=0;
        
        while(!pq.empty()) {
            if(m.iterations++ > 10000) {
                 if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count() > 0.1) break; // Fast timeout for 1024 instances
            }
            Node curr = pq.top(); pq.pop();
            
            if(curr.lb >= best_k) continue;
            if(curr.level == n) {
                if(curr.max_color_used < best_k) { best_k = curr.max_color_used; best_sol = curr.colors; }
                continue;
            }
            
            std::vector<bool> used(curr.max_color_used + 2, false);
            for(size_t u=0; u<curr.level; ++u) if(adj[curr.level][u]) used[curr.colors[u]]=true;
            
            for(size_t c=1; c<=curr.max_color_used+1; ++c) {
                if(c>=best_k) break;
                if(!used[c]) {
                    Node child=curr;
                    child.colors[curr.level]=c;
                    child.level++;
                    child.max_color_used=std::max(child.max_color_used, c);
                    child.lb = child.max_color_used;
                    pq.push(child);
                }
            }
        }
        val.colors=best_sol;
        val.num_colors=best_k > n ? n : best_k; 
        m.objective_value=val.num_colors;
        return true;
    }
};

// Spectral Analysis (Extended)
struct SpectralFeatures {
    double max_eigenvalue;
    double min_eigenvalue;
    double spectral_gap;
    double energy;
    double fiedler_val; // 2nd smallest EV
    double fiedler_ipr; // Inverse Participation Ratio
    double cut_size;    // Fiedler cut size
    double algebraic_connectivity;
};

SpectralFeatures compute_spectral(const optsolve::GraphColoringProblem& p) {
    int n = (int)p.n_vertices;
    
    // 1. Build Laplacian L = D - A
    std::vector<double> L(n*n, 0.0);
    std::vector<int> degrees(n, 0);
    
    for(auto& e : p.edges) {
        degrees[e.first]++;
        degrees[e.second]++;
        L[e.first*n + e.second] = -1.0;
        L[e.second*n + e.first] = -1.0;
    }
    for(int i=0; i<n; ++i) L[i*n + i] = (double)degrees[i];
    
    // 2. Cyclic Jacobi Eigenvalue (on L)
    std::vector<double> V(n*n, 0.0); // Eigenvectors (identity init)
    for(int i=0; i<n; ++i) V[i*n + i] = 1.0;
    
    std::vector<double> d(n); 
    for(int i=0; i<n; ++i) d[i] = L[i*n + i];
    
    std::vector<double> b(n), z(n);
    for(int i=0; i<n; ++i) { b[i]=d[i]; z[i]=0.0; }
    
    int max_iter = 50;
    for(int iter=0; iter<max_iter; ++iter) {
        double sm = 0.0;
        for(int i=0; i<n-1; ++i) {
            for(int j=i+1; j<n; ++j) {
                sm += std::abs(L[i*n + j]);
            }
        }
        if (sm == 0.0) break;
        
        double tresh = (iter < 4) ? 0.2 * sm / (n*n) : 0.0;
        
        for(int i=0; i<n-1; ++i) {
            for(int j=i+1; j<n; ++j) {
                double g = 100.0 * std::abs(L[i*n + j]);
                if (iter > 4 && (std::abs(d[i]) + g == std::abs(d[i])) 
                             && (std::abs(d[j]) + g == std::abs(d[j]))) {
                     L[i*n + j] = 0.0;
                } else if (std::abs(L[i*n + j]) > tresh) {
                    double h = d[j] - d[i];
                    double t;
                    if (std::abs(h) + g == std::abs(h)) {
                        t = (L[i*n + j]) / h;
                    } else {
                        double theta = 0.5 * h / (L[i*n + j]);
                        t = 1.0 / (std::abs(theta) + std::sqrt(1.0 + theta*theta));
                        if (theta < 0.0) t = -t;
                    }
                    
                    double c = 1.0 / std::sqrt(1 + t*t);
                    double s = t * c;
                    double tau = s / (1.0 + c);
                    
                    h = t * L[i*n + j];
                    z[i] -= h;
                    z[j] += h;
                    d[i] -= h;
                    d[j] += h;
                    L[i*n + j] = 0.0;
                    
                    // Rotate Eigenvectors V (Right Multiply)
                    // V column k is k-th eigenvector
                    for(int k=0; k<n; ++k) {
                        g = V[k*n + i]; h = V[k*n + j];
                        V[k*n + i] = g - s*(h + g*tau);
                        V[k*n + j] = h + s*(g - h*tau);
                    }
                    
                    // Rotate Matrix L
                    for(int k=0; k<i; ++k) {
                        g = L[k*n + i]; h = L[k*n + j];
                        L[k*n + i] = g - s*(h + g*tau);
                        L[k*n + j] = h + s*(g - h*tau);
                    }
                    for(int k=i+1; k<j; ++k) {
                        g = L[i*n + k]; h = L[k*n + j];
                        L[i*n + k] = g - s*(h + g*tau);
                        L[k*n + j] = h + s*(g - h*tau);
                    }
                    for(int k=j+1; k<n; ++k) {
                        g = L[i*n + k]; h = L[j*n + k];
                        L[i*n + k] = g - s*(h + g*tau);
                        L[j*n + k] = h + s*(g - h*tau);
                    }
                }
            }
        }
        for(int i=0; i<n; ++i) {
            b[i] += z[i];
            d[i] = b[i];
            z[i] = 0.0;
        }
    }
    
    // Sort eigenvalues and corresponding eigenvectors
    std::vector<std::pair<double, int>> eigen_pairs(n);
    for(int i=0; i<n; ++i) eigen_pairs[i] = {d[i], i};
    std::sort(eigen_pairs.begin(), eigen_pairs.end());
    
    double max_ev = eigen_pairs[n-1].first;
    double min_ev = eigen_pairs[0].first; // Should be ~0 for Laplacian
    double alg_conn = eigen_pairs[1].first; // 2nd smallest (Fiedler Value)
    double gap = max_ev - min_ev; // Not typical gap, but range
    double energy = 0; // Laplacian energy
    double avg_d = 0; // Average degree = 2m/n
    double sum_deg = 0;
    for(int i=0; i<n; ++i) sum_deg += (double)degrees[i];
    avg_d = sum_deg / n; 
    
    // Laplacian Energy: sum |lambda_i - 2m/n|
    for(auto p : eigen_pairs) energy += std::abs(p.first - avg_d);

    // Fiedler Vector Analysis
    int fiedler_idx = eigen_pairs[1].second;
    double fiedler_ipr_num = 0;
    double fiedler_ipr_den = 0;
    std::vector<double> fiedler_vec(n);
    
    for(int i=0; i<n; ++i) {
        double val = V[i*n + fiedler_idx];
        fiedler_vec[i] = val;
        fiedler_ipr_num += val*val*val*val;
        fiedler_ipr_den += val*val;
    }
    double ipr = fiedler_ipr_num / (fiedler_ipr_den * fiedler_ipr_den);
    
    // Cut Size based on Fiedler Sign
    double cut_size = 0;
    for(auto& e : p.edges) {
        bool s1 = fiedler_vec[e.first] > 0;
        bool s2 = fiedler_vec[e.second] > 0;
        if (s1 != s2) cut_size++;
    }

    return {max_ev, min_ev, gap, energy, alg_conn, ipr, cut_size, alg_conn};
}

using namespace optsolve;

int main() {
    std::cout << "Starting Advanced Metaheuristics Benchmark...\n";
    std::ofstream csv("meta_results_v2.csv");
    csv << "id,n,p,max_ev,alg_conn,ipr,cut_size,"
        << "Greedy,Tabu,RW,GLS,"
        << "BitGreedy,BitTabu,BitRW,BitGLS,"
        << "Optional,DSatur,Learned\n";
        
    // Solvers
    ColoringGreedy s1;
    ColoringTabu s2;
    ColoringRandomWalk s3;
    ColoringGLS s4;
    
    BitsetGreedy b1;
    BitsetTabu b2;
    BitsetRandomWalk b3;
    BitsetGLS b4;
    
    OptimalSolver opt;
    ColoringDSATUR dsat;
    LearnedColoringSolver learn;
    
    for(int i=0; i<1024; ++i) {
        int n = 30 + (i % 34); // 30..64
        double p = 0.1 + (0.5 * (i % 10) / 10.0);
        
        GraphColoringProblem prob = GraphColoringProblem::random(n, p, i);
        
        // Spectral
        SpectralFeatures spec = compute_spectral(prob);
        
        // Solve
        double r1 = s1.solve(prob).metrics.objective_value;
        double r2 = s2.solve(prob).metrics.objective_value;
        double r3 = s3.solve(prob).metrics.objective_value;
        double r4 = s4.solve(prob).metrics.objective_value;
        
        double rb1 = b1.solve(prob).metrics.objective_value;
        double rb2 = b2.solve(prob).metrics.objective_value;
        double rb3 = b3.solve(prob).metrics.objective_value;
        double rb4 = b4.solve(prob).metrics.objective_value;
        
        double ropt = opt.solve(prob).metrics.objective_value;
        double rdsat = dsat.solve(prob).metrics.objective_value;
        double rlearn = learn.solve(prob).metrics.objective_value;
        
        csv << i << "," << n << "," << p << ","
            << spec.max_eigenvalue << "," << spec.algebraic_connectivity << "," << spec.fiedler_ipr << "," << spec.cut_size << ","
            << r1 << "," << r2 << "," << r3 << "," << r4 << ","
            << rb1 << "," << rb2 << "," << rb3 << "," << rb4 << ","
            << ropt << "," << rdsat << "," << rlearn << "\n";
            
        if(i%50==0) std::cout << "Processed " << i << " (Cut: " << spec.cut_size << ")\n";
    }
    
    csv.close();
    std::cout << "Done.\n";
    return 0;
}
