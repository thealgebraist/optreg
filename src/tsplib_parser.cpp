#include "tsplib_parser.h"
#include <fstream>
#include <sstream>
#include <cmath>
#include <iostream>

namespace optreg {

// Distance functions for different types
static double euc_2d(double x1, double y1, double x2, double y2) {
    double dx = x1 - x2;
    double dy = y1 - y2;
    return std::round(std::sqrt(dx*dx + dy*dy));
}

static double ceil_2d(double x1, double y1, double x2, double y2) {
    double dx = x1 - x2;
    double dy = y1 - y2;
    return std::ceil(std::sqrt(dx*dx + dy*dy));
}

static double att(double x1, double y1, double x2, double y2) {
    double dx = x1 - x2;
    double dy = y1 - y2;
    double r = std::sqrt((dx*dx + dy*dy) / 10.0);
    int t = (int)std::round(r);
    if (t < r) return t + 1;
    return t;
}

static double geo(double lat1, double lon1, double lat2, double lon2) {
    const double PI = 3.141592653589793;
    const double RRR = 6378.388;  // Earth radius in km
    
    // Convert to radians
    double deg_lat1 = (int)lat1;
    double min_lat1 = lat1 - deg_lat1;
    double rad_lat1 = PI * (deg_lat1 + 5.0 * min_lat1 / 3.0) / 180.0;
    
    double deg_lon1 = (int)lon1;
    double min_lon1 = lon1 - deg_lon1;
    double rad_lon1 = PI * (deg_lon1 + 5.0 * min_lon1 / 3.0) / 180.0;
    
    double deg_lat2 = (int)lat2;
    double min_lat2 = lat2 - deg_lat2;
    double rad_lat2 = PI * (deg_lat2 + 5.0 * min_lat2 / 3.0) / 180.0;
    
    double deg_lon2 = (int)lon2;
    double min_lon2 = lon2 - deg_lon2;
    double rad_lon2 = PI * (deg_lon2 + 5.0 * min_lon2 / 3.0) / 180.0;
    
    double q1 = std::cos(rad_lon1 - rad_lon2);
    double q2 = std::cos(rad_lat1 - rad_lat2);
    double q3 = std::cos(rad_lat1 + rad_lat2);
    
    return (int)(RRR * std::acos(0.5 * ((1.0 + q1) * q2 - (1.0 - q1) * q3)) + 1.0);
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
    bool in_edge_weight = false;
    std::string edge_weight_format;
    std::vector<double> edge_weights;

    while (std::getline(ss, line)) {
        if (line.empty() || line.find("EOF") != std::string::npos) break;

        if (in_edge_weight) {
            // Parse edge weight data
            std::stringstream ls(line);
            double val;
            while (ls >> val) {
                edge_weights.push_back(val);
            }
            continue;
        }

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
            // Trim whitespace
            key.erase(0, key.find_first_not_of(" \t\n\r"));
            key.erase(key.find_last_not_of(" \t\n\r") + 1);
            val.erase(0, val.find_first_not_of(" \t\n\r"));
            val.erase(val.find_last_not_of(" \t\n\r") + 1);

            if (key == "NAME") instance.name = val;
            else if (key == "TYPE") instance.type = val;
            else if (key == "DIMENSION" && !val.empty()) instance.dimension = std::stoi(val);
            else if (key == "EDGE_WEIGHT_TYPE") instance.edge_weight_type = val;
            else if (key == "EDGE_WEIGHT_FORMAT") edge_weight_format = val;
        } else if (line.find("NODE_COORD_SECTION") != std::string::npos) {
            in_node_coord = true;
        } else if (line.find("EDGE_WEIGHT_SECTION") != std::string::npos) {
            in_edge_weight = true;
        }
    }

    // Build adjacency matrix based on type
    if (instance.dimension <= 0) return instance;
    
    instance.adj.resize(instance.dimension, std::vector<double>(instance.dimension, 0));

    if (instance.edge_weight_type == "EUC_2D" && (int)instance.coords.size() == instance.dimension) {
        for (int i = 0; i < instance.dimension; ++i) {
            for (int j = 0; j < instance.dimension; ++j) {
                if (i == j) instance.adj[i][j] = 0;
                else instance.adj[i][j] = euc_2d(instance.coords[i].first, instance.coords[i].second,
                                                instance.coords[j].first, instance.coords[j].second);
            }
        }
    }
    else if (instance.edge_weight_type == "CEIL_2D" && (int)instance.coords.size() == instance.dimension) {
        for (int i = 0; i < instance.dimension; ++i) {
            for (int j = 0; j < instance.dimension; ++j) {
                if (i == j) instance.adj[i][j] = 0;
                else instance.adj[i][j] = ceil_2d(instance.coords[i].first, instance.coords[i].second,
                                                 instance.coords[j].first, instance.coords[j].second);
            }
        }
    }
    else if (instance.edge_weight_type == "ATT" && (int)instance.coords.size() == instance.dimension) {
        for (int i = 0; i < instance.dimension; ++i) {
            for (int j = 0; j < instance.dimension; ++j) {
                if (i == j) instance.adj[i][j] = 0;
                else instance.adj[i][j] = att(instance.coords[i].first, instance.coords[i].second,
                                             instance.coords[j].first, instance.coords[j].second);
            }
        }
    }
    else if (instance.edge_weight_type == "GEO" && (int)instance.coords.size() == instance.dimension) {
        for (int i = 0; i < instance.dimension; ++i) {
            for (int j = 0; j < instance.dimension; ++j) {
                if (i == j) instance.adj[i][j] = 0;
                else instance.adj[i][j] = geo(instance.coords[i].first, instance.coords[i].second,
                                             instance.coords[j].first, instance.coords[j].second);
            }
        }
    }
    else if (instance.edge_weight_type == "EXPLICIT" && !edge_weights.empty()) {
        // Handle different EXPLICIT formats
        if (edge_weight_format == "LOWER_DIAG_ROW" || edge_weight_format.empty()) {
            int idx = 0;
            for (int i = 0; i < instance.dimension; ++i) {
                for (int j = 0; j <= i; ++j) {
                    if (idx < (int)edge_weights.size()) {
                        instance.adj[i][j] = edge_weights[idx];
                        instance.adj[j][i] = edge_weights[idx];
                        idx++;
                    }
                }
            }
        }
        else if (edge_weight_format == "UPPER_ROW") {
            int idx = 0;
            for (int i = 0; i < instance.dimension - 1; ++i) {
                for (int j = i + 1; j < instance.dimension; ++j) {
                    if (idx < (int)edge_weights.size()) {
                        instance.adj[i][j] = edge_weights[idx];
                        instance.adj[j][i] = edge_weights[idx];
                        idx++;
                    }
                }
            }
        }
        else if (edge_weight_format == "FULL_MATRIX") {
            int idx = 0;
            for (int i = 0; i < instance.dimension; ++i) {
                for (int j = 0; j < instance.dimension; ++j) {
                    if (idx < (int)edge_weights.size()) {
                        instance.adj[i][j] = edge_weights[idx++];
                    }
                }
            }
        }
    }

    return instance;
}

} // namespace optreg
