#pragma once

#include "interference_graph.h"
#include "graph_coloring.h"
#include <sqlite3.h>
#include <string>
#include <optional>
#include <chrono>

namespace optreg {

// Cached solution entry
struct CachedSolution {
    std::string graph_hash;
    std::string graph_ast;        // String representation
    uint32_t num_variables;
    uint32_t num_registers;
    uint32_t num_edges;
    
    // Optimal solution
    uint32_t optimal_spills;
    uint32_t optimal_colors;
    int64_t optimal_time_us;
    
    // Heuristic baseline
    uint32_t heuristic_spills;
    uint32_t heuristic_colors;
    int64_t heuristic_time_us;
    
    double improvement_pct;  // (heuristic - optimal) / heuristic * 100
};

class SolutionCache {
public:
    SolutionCache(const std::string& db_path = "regalloc_cache.db");
    ~SolutionCache();
    
    // Initialize database schema
    bool init();
    
    // Compute hash of interference graph
    std::string compute_hash(const InterferenceGraph& graph);
    
    // Build AST string representation
    std::string graph_to_ast(const InterferenceGraph& graph);
    
    // Lookup solution by hash
    std::optional<CachedSolution> lookup(const std::string& hash);
    
    // Store new solution
    bool store(const CachedSolution& solution);
    
    // Stats
    struct CacheStats {
        uint64_t total_entries;
        uint64_t hits;
        uint64_t misses;
        double avg_optimal_time_ms;
        double avg_improvement_pct;
    };
    
    CacheStats get_stats();
    
private:
    sqlite3* db_;
    std::string db_path_;
    uint64_t session_hits_;
    uint64_t session_misses_;
    
    bool create_schema();
    bool prepare_statements();
    
    sqlite3_stmt* stmt_lookup_;
    sqlite3_stmt* stmt_insert_;
};

} // namespace optreg
