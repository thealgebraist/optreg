#include <iostream>
#include <filesystem>
#include <vector>
#include <algorithm>
#include "tsplib_parser.h"

using namespace optreg;
namespace fs = std::filesystem;

int main() {
    std::cout << "Testing TSPLIB Parser on All Files\n" << std::endl;
    
    TSPLIBParser parser;
    std::vector<std::string> files;
    
    for (const auto& entry : fs::directory_iterator("data/tsplib")) {
        if (entry.path().extension() == ".tsp") {
            files.push_back(entry.path().string());
        }
    }
    std::sort(files.begin(), files.end());
    
    std::cout << "Found " << files.size() << " files\n" << std::endl;
    std::cout << "File                        N   Type          Status" << std::endl;
    std::cout << "--------------------------- --- ------------- ------" << std::endl;
    
    int success = 0, failed = 0;
    
    for (const auto& file : files) {
        try {
            auto inst = parser.parse(file);
            
            std::string status = "OK";
            if (inst.dimension == 0) status = "NO_DIM";
            else if (inst.adj.empty()) status = "NO_ADJ";
            else success++;
            
            printf("%-27s %3d %-13s %s\n",
                   fs::path(file).filename().string().substr(0, 27).c_str(),
                   inst.dimension,
                   inst.edge_weight_type.substr(0, 13).c_str(),
                   status.c_str());
                   
        } catch (const std::exception& e) {
            printf("%-27s  ?  %-13s ERROR: %s\n",
                   fs::path(file).filename().string().substr(0, 27).c_str(),
                   "?",
                   std::string(e.what()).substr(0, 30).c_str());
            failed++;
        }
    }
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Results:" << std::endl;
    std::cout << "  Total files: " << files.size() << std::endl;
    std::cout << "  Parsed OK:   " << success << std::endl;
    std::cout << "  Failed:      " << failed << std::endl;
    std::cout << "  Success rate: " << (files.size() > 0 ? 100*success/(int)files.size() : 0) << "%" << std::endl;
    std::cout << "========================================" << std::endl;
    
    return failed > 0 ? 1 : 0;
}
