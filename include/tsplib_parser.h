#pragma once
#include <string>
#include <vector>
#include <unordered_map>

namespace optreg {

struct TSPInstance {
    std::string name;
    std::string type;
    int dimension = 0;
    std::string edge_weight_type;
    std::vector<std::pair<double, double>> coords;
    std::vector<std::vector<double>> adj; // Distance matrix
};

class TSPLIBParser {
public:
    static TSPInstance parse(const std::string& filepath);
    static TSPInstance from_string(const std::string& content);
};

} // namespace optreg
