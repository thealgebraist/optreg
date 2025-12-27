#include <iostream>
#include <vector>
#include <random>
#include <Eigen/Sparse>
#include <Eigen/Dense>
#include "../include/accelerate_solver.h"

using namespace optreg;

// Generate a random Sparse Symmetric Positive Definite Matrix
void generate_spd(int n, double density, Eigen::SparseMatrix<double>& A, Eigen::VectorXd& b) {
    A.resize(n, n);
    std::vector<Eigen::Triplet<double>> triplets;
    
    std::mt19937 gen(42);
    std::uniform_real_distribution<double> dist(-1.0, 1.0);
    
    // Create random symmetric pattern
    for(int i=0; i<n; ++i) {
        // Diagonal dominance
        triplets.push_back({i, i, n + 2.0}); 
        
        for(int j=i+1; j<n; ++j) {
            if (dist(gen) < density) {
                double v = dist(gen);
                triplets.push_back({i, j, v});
                triplets.push_back({j, i, v});
            }
        }
    }
    
    A.setFromTriplets(triplets.begin(), triplets.end());
    A.makeCompressed();
    
    b.resize(n);
    for(int i=0; i<n; ++i) b(i) = dist(gen);
}

int main() {
    std::cout << "Reproducing AMX Crash..." << std::endl;
    
    AccelerateSparseSolver solver;
    
    // 1. Small test (Sanity)
    {
        std::cout << "Test 1: Small (n=10)" << std::endl;
        Eigen::SparseMatrix<double> A;
        Eigen::VectorXd b, x;
        generate_spd(10, 0.5, A, b);
        if(!solver.solve(A, b, x)) {
            std::cerr << "Solve failed on small matrix." << std::endl;
        }
    }
    
    // 2. Loop with growing sizes
    for(int i=1; i<=10; ++i) { // Reduced loop for speed
        int n = i * 10;
        std::cout << "Test 2: Loop Iter " << i << " (n=" << n << ")" << std::endl;
        Eigen::SparseMatrix<double> A;
        Eigen::VectorXd b, x;
        generate_spd(n, 0.05, A, b);
        
        if(!solver.solve(A, b, x)) {
            std::cerr << "Solve failed at n=" << n << std::endl;
        }
    }
    
    // 3. Non-PD Matrix (Negative Diagonal)
    {
        std::cout << "Test 3: Non-PD Matrix" << std::endl;
        Eigen::SparseMatrix<double> A(10, 10);
        A.insert(0, 0) = -1.0; // Negative!
        for(int i=1; i<10; ++i) A.insert(i, i) = 1.0;
        A.makeCompressed();
        
        Eigen::VectorXd b(10), x;
        b.setOnes();
        
        // This should fail gracefully, NOT crash
        if(solver.solve(A, b, x)) {
             std::cerr << "WARNING: Solve succeeded on Indefinite matrix?" << std::endl;
        } else {
             std::cout << "Correctly failed on Non-PD matrix." << std::endl;
        }
    }
    
    // 4. Mismatched Dimensions (A is 10x10, b is 5)
    {
        std::cout << "Test 4: Mismatched Dimensions" << std::endl;
        Eigen::SparseMatrix<double> A;
        Eigen::VectorXd b_dummy, x;
        generate_spd(10, 0.5, A, b_dummy);
        
        Eigen::VectorXd b_small(5);
        b_small.setOnes();
        
        // This causes out-of-bounds read in SparseSolve inside the wrapper
        // The wrapper assumes b has size n.
        std::cout << "Triggering mismatch..." << std::endl;
        solver.solve(A, b_small, x); 
        std::cout << "Survived mismatch (might be luck)." << std::endl;
    }

    std::cout << "Finished without crash." << std::endl;
    return 0;
}
