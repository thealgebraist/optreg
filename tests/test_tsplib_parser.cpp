#include <iostream>
#include <fstream>
#include <sstream>
#include "tsplib_lr1_parser.h"

using namespace tsplib;

std::string read_file(const std::string& filename) {
    std::ifstream file(filename);
    std::stringstream buffer;
    buffer << file.rdbuf();
    return buffer.str();
}

int main() {
    std::cout << "Testing LR(1) TSPLIB Parser\n" << std::endl;
    
    std::vector<std::string> test_files = {
        "data/tsplib/burma14.tsp",
        "data/tsplib/gr17.tsp",
        "data/tsplib/ulysses16.tsp"
    };
    
    for (const auto& filename : test_files) {
        try {
            std::cout << "Parsing: " << filename << std::endl;
            
            std::string content = read_file(filename);
            TSPLIBParser parser(content);
            auto inst = parser.parse();
            
            std::cout << "  Name: " << inst.name << std::endl;
            std::cout << "  Type: " << inst.type << std::endl;
            std::cout << "  Dimension: " << inst.dimension << std::endl;
            std::cout << "  Edge Weight Type: " << inst.edge_weight_type << std::endl;
            std::cout << "  Format: " << inst.edge_weight_format << std::endl;
            std::cout << "  Matrix valid: " << (inst.adj_matrix.size() == (size_t)inst.dimension ? "YES" : "NO") << std::endl;
            std::cout << std::endl;
            
        } catch (const std::exception& e) {
            std::cout << "  ERROR: " << e.what() << std::endl << std::endl;
        }
    }
    
    return 0;
}
