#include "tsplib_parser.h"
#include <fstream>
#include <sstream>
#include <cmath>
#include <iostream>

namespace optreg {

static double euc_2d(double x1, double y1, double x2, double y2) {
    double dx = x1 - x2;
    double dy = y1 - y2;
    return std::round(std::sqrt(dx*dx + dy*dy));
}

TSPInstance TSPLIBParser::parse(const std::string& filepath) {
    std::ifstream file(filepath);
    if (!file.is_open()) return {};
    
    std::stringstream ss;
    ss << file.rdbuf();
    return from_string(ss.str());
}

TSPInstance TSPLIBParser::from_string(const std::string& content) {
    TSPInstance instance;
    std::stringstream ss(content);
    std::string line;
    bool in_node_coord = false;

    while (std::getline(ss, line)) {
        if (line.empty() || line.find("EOF") != std::string::npos) break;

        if (in_node_coord) {
            std::stringstream ls(line);
            int id;
            double x, y;
            if (ls >> id >> x >> y) {
                instance.coords.push_back({x, y});
            }
            continue;
        }

        size_t colon = line.find(':');
        if (colon != std::string::npos) {
            std::string key = line.substr(0, colon);
            std::string val = line.substr(colon + 1);
            // Trim
            key.erase(0, key.find_first_not_of(" \t\n\r"));
            key.erase(key.find_last_not_of(" \t\n\r") + 1);
            val.erase(0, val.find_first_not_of(" \t\n\r"));
            val.erase(val.find_last_not_of(" \t\n\r") + 1);

            if (key == "NAME") instance.name = val;
            else if (key == "TYPE") instance.type = val;
            else if (key == "DIMENSION") instance.dimension = std::stoi(val);
            else if (key == "EDGE_WEIGHT_TYPE") instance.edge_weight_type = val;
        } else if (line.find("NODE_COORD_SECTION") != std::string::npos) {
            in_node_coord = true;
        }
    }

    // Compute adjacency matrix for EUC_2D
    if (instance.edge_weight_type == "EUC_2D" && (int)instance.coords.size() == instance.dimension) {
        instance.adj.resize(instance.dimension, std::vector<double>(instance.dimension));
        for (int i = 0; i < instance.dimension; ++i) {
            for (int j = 0; j < instance.dimension; ++j) {
                if (i == j) instance.adj[i][j] = 0;
                else instance.adj[i][j] = euc_2d(instance.coords[i].first, instance.coords[i].second,
                                                instance.coords[j].first, instance.coords[j].second);
            }
        }
    }

    return instance;
}

} // namespace optreg
