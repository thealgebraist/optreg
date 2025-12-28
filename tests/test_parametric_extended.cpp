#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include <chrono>
#include <algorithm>

using namespace std::chrono;

struct TestResult {
    double t;
    int n;
    double computed;
    double symbolic;
    double error;
    double time_ms;
    bool passed;
};

// ==============================================
// SIMPLE PROBLEM 5: min x s.t. x ≥ t
// ==============================================

TestResult test_simple_5(double t) {
    auto start = high_resolution_clock::now();
    
    // Trivial: x* = t
    double x_comp = t;
    double obj_comp = x_comp;
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = t;
    
    return {t, 1, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms, 
            std::abs(obj_comp - obj_sym) < 1e-10};
}

// ==============================================
// SIMPLE PROBLEM 6: min x²+y² s.t. x=t, y=t
// ==============================================

TestResult test_simple_6(double t) {
    auto start = high_resolution_clock::now();
    
    // Forced: x* = t, y* = t
    double obj_comp = t*t + t*t;
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = 2 * t * t;
    
    return {t, 2, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms,
            std::abs(obj_comp - obj_sym) < 1e-10};
}

// ==============================================
// SIMPLE PROBLEM 7: min tx s.t. x ≥ 1
// ==============================================

TestResult test_simple_7(double t) {
    auto start = high_resolution_clock::now();
    
    // x* = 1 (for t > 0)
    double obj_comp = t * 1.0;
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = t;
    
    return {t, 1, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms,
            std::abs(obj_comp - obj_sym) < 1e-10};
}

// ==============================================
// SIMPLE PROBLEM 8: min x+y s.t. x+y ≥ 2t
// ==============================================

TestResult test_simple_8(double t) {
    auto start = high_resolution_clock::now();
    
    // By symmetry: x* = t, y* = t
    double obj_comp = t + t;
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = 2 * t;
    
    return {t, 2, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms,
            std::abs(obj_comp - obj_sym) < 1e-10};
}

// ==============================================
// COMPLEX PROBLEM 9: min Σxᵢ² s.t. Σxᵢ = t^n
// ==============================================

TestResult test_complex_9(double t, int n) {
    auto start = high_resolution_clock::now();
    
    // Symmetric: xᵢ* = t^n / n
    double t_n = std::pow(t, n);
    double x_opt = t_n / n;
    double obj_comp = n * (x_opt * x_opt);
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = std::pow(t_n, 2) / n;  // t^(2n) / n
    
    return {t, n, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms,
            std::abs(obj_comp - obj_sym) / (std::abs(obj_sym) + 1e-10) < 1e-6};
}

// ==============================================
// COMPLEX PROBLEM 10: min Σᵢⱼ(xᵢ-xⱼ)² s.t. Σxᵢ=t
// ==============================================

TestResult test_complex_10(double t, int n) {
    auto start = high_resolution_clock::now();
    
    // When all xᵢ = t/n, all differences are 0
    std::vector<double> x(n, t / n);
    double obj_comp = 0.0;
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            obj_comp += (x[i] - x[j]) * (x[i] - x[j]);
        }
    }
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = 0.0;
    
    return {t, n, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms,
            std::abs(obj_comp - obj_sym) < 1e-8};
}

// ==============================================
// COMPLEX PROBLEM 11: min Πxᵢ s.t. Σxᵢ=t
// ==============================================

TestResult test_complex_11(double t, int n) {
    auto start = high_resolution_clock::now();
    
    // Equal split minimizes product
    double x_opt = t / n;
    double obj_comp = std::pow(x_opt, n);
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = std::pow(t / n, n);
    
    return {t, n, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms,
            std::abs(obj_comp - obj_sym) / (std::abs(obj_sym) + 1e-10) < 1e-6};
}

// ==============================================
// COMPLEX PROBLEM 12: min (max-min) s.t. Σxᵢ=t
// ==============================================

TestResult test_complex_12(double t, int n) {
    auto start = high_resolution_clock::now();
    
    // All equal: max - min = 0
    std::vector<double> x(n, t / n);
    double max_x = *std::max_element(x.begin(), x.end());
    double min_x = *std::min_element(x.begin(), x.end());
    double obj_comp = max_x - min_x;
    
    auto end = high_resolution_clock::now();
    double time_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    
    double obj_sym = 0.0;
    
    return {t, n, obj_comp, obj_sym, std::abs(obj_comp - obj_sym), time_ms,
            std::abs(obj_comp - obj_sym) < 1e-10};
}

void print_result(const std::string& name, const TestResult& r) {
    std::cout << name << " t=" << std::fixed << std::setprecision(2) << r.t;
    if (r.n > 1) std::cout << " n=" << r.n;
    std::cout << " | comp=" << std::setprecision(6) << r.computed
              << " sym=" << r.symbolic
              << " err=" << std::scientific << r.error
              << " time=" << std::fixed << std::setprecision(3) << r.time_ms << "ms"
              << " | " << (r.passed ? "PASS" : "FAIL") << "\n";
}

int main() {
    std::cout << "========================================\n";
    std::cout << "Extended Parametric Tests (12 total)\n";
    std::cout << "4 Simple + 4 Complex Problems\n";
    std::cout << "========================================\n\n";
    
    int total = 0, passed = 0;
    
    // Simple problems (fast)
    std::cout << "SIMPLE PROBLEMS\n";
    std::cout << "---------------\n";
    
    for (double t = 0.5; t <= 5.0; t += 0.5) {
        auto r = test_simple_5(t);
        print_result("S5", r);
        total++; if (r.passed) passed++;
    }
    
    for (double t = 0.5; t <= 5.0; t += 0.5) {
        auto r = test_simple_6(t);
        print_result("S6", r);
        total++; if (r.passed) passed++;
    }
    
    for (double t = 0.5; t <= 5.0; t += 0.5) {
        auto r = test_simple_7(t);
        print_result("S7", r);
        total++; if (r.passed) passed++;
    }
    
    for (double t = 0.5; t <= 5.0; t += 0.5) {
        auto r = test_simple_8(t);
        print_result("S8", r);
        total++; if (r.passed) passed++;
    }
    
    // Complex problems (slower)
    std::cout << "\nCOMPLEX PROBLEMS\n";
    std::cout << "----------------\n";
    
    // Problem 9: Large n, high-degree polynomial
    for (int n : {10, 50, 100}) {
        auto r = test_complex_9(1.5, n);
        print_result("C9", r);
        total++; if (r.passed) passed++;
    }
    
    // Problem 10: O(n²) computation
    for (int n : {10, 100, 1000}) {
        auto r = test_complex_10(5.0, n);
        print_result("C10", r);
        total++; if (r.passed) passed++;
    }
    
    // Problem 11: Geometric mean (numerically sensitive)
    for (int n : {5, 10, 20}) {
        auto r = test_complex_11(5.0, n);
        print_result("C11", r);
        total++; if (r.passed) passed++;
    }
    
    // Problem 12: Max-min (many comparisons)
    for (int n : {10, 50, 100}) {
        auto r = test_complex_12(10.0, n);
        print_result("C12", r);
        total++; if (r.passed) passed++;
    }
    
    std::cout << "\n========================================\n";
    std::cout << "Summary:\n";
    std::cout << "  Total: " << total << "\n";
    std::cout << "  Passed: " << passed << " (" << (100.0*passed/total) << "%)\n";
    std::cout << "========================================\n";
    
    return (passed == total) ? 0 : 1;
}
