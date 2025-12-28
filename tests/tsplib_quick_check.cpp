#include <iostream>
#include <filesystem>
#include <fstream>
#include "tsplib_parser.h"

namespace fs = std::filesystem;
using namespace optreg;

int main() {
    TSPLIBParser parser;
    
    int total = 0, ok = 0, failed = 0;
    
    std::cout << "TSPLIB Parser Status:\n\n";
    
    for (const auto& entry : fs::directory_iterator("data/tsplib")) {
        if (entry.path().extension() == ".tsp") {
            total++;
            try {
                auto inst = parser.parse(entry.path().string());
                if (inst.dimension > 0 && !inst.adj.empty()) {
                    ok++;
                    if (ok <= 5) {
                        std::cout << "✓ " << entry.path().filename().string() 
                                  << " (n=" << inst.dimension << ")\n";
                    }
                } else {
                    failed++;
                }
            } catch (...) {
                failed++;
            }
        }
    }
    
    std::cout << "\n========================================\n";
    std::cout << "Summary:\n";
    std::cout << "  Total files: " << total << "\n";
    std::cout << "  Parsed OK: " << ok << " (" << (100.0*ok/total) << "%)\n";
    std::cout << "  Failed: " << failed << " (" << (100.0*failed/total) << "%)\n";
    std::cout << "========================================\n";
    
    return 0;
}
