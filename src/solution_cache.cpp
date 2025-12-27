#include "solution_cache.h"
#include <sstream>
#include <iomanip>
#include <openssl/sha.h>

namespace optreg {

SolutionCache::SolutionCache(const std::string& db_path)
    : db_(nullptr), db_path_(db_path), session_hits_(0), session_misses_(0),
      stmt_lookup_(nullptr), stmt_insert_(nullptr) {}

SolutionCache::~SolutionCache() {
    if (stmt_lookup_) sqlite3_finalize(stmt_lookup_);
    if (stmt_insert_) sqlite3_finalize(stmt_insert_);
    if (db_) sqlite3_close(db_);
}

bool SolutionCache::init() {
    int rc = sqlite3_open(db_path_.c_str(), &db_);
    if (rc != SQLITE_OK) {
        return false;
    }
    
    if (!create_schema()) return false;
    if (!prepare_statements()) return false;
    
    return true;
}

bool SolutionCache::create_schema() {
    const char* schema = R"(
        CREATE TABLE IF NOT EXISTS solutions (
            graph_hash TEXT PRIMARY KEY,
            graph_ast TEXT NOT NULL,
            num_variables INTEGER NOT NULL,
            num_registers INTEGER NOT NULL,
            num_edges INTEGER NOT NULL,
            optimal_spills INTEGER NOT NULL,
            optimal_colors INTEGER NOT NULL,
            optimal_time_us INTEGER NOT NULL,
            heuristic_spills INTEGER NOT NULL,
            heuristic_colors INTEGER NOT NULL,
            heuristic_time_us INTEGER NOT NULL,
            improvement_pct REAL NOT NULL,
            timestamp INTEGER DEFAULT (strftime('%s', 'now'))
        );
        
        CREATE INDEX IF NOT EXISTS idx_num_vars ON solutions(num_variables);
        CREATE INDEX IF NOT EXISTS idx_timestamp ON solutions(timestamp);
    )";
    
    char* err_msg = nullptr;
    int rc = sqlite3_exec(db_, schema, nullptr, nullptr, &err_msg);
    
    if (rc != SQLITE_OK) {
        if (err_msg) {
            sqlite3_free(err_msg);
        }
        return false;
    }
    
    return true;
}

bool SolutionCache::prepare_statements() {
    // Lookup statement
    const char* lookup_sql = 
        "SELECT * FROM solutions WHERE graph_hash = ?";
    
    int rc = sqlite3_prepare_v2(db_, lookup_sql, -1, &stmt_lookup_, nullptr);
    if (rc != SQLITE_OK) return false;
    
    // Insert statement
    const char* insert_sql = R"(
        INSERT OR REPLACE INTO solutions 
        (graph_hash, graph_ast, num_variables, num_registers, num_edges,
         optimal_spills, optimal_colors, optimal_time_us,
         heuristic_spills, heuristic_colors, heuristic_time_us, improvement_pct)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    )";
    
    rc = sqlite3_prepare_v2(db_, insert_sql, -1, &stmt_insert_, nullptr);
    if (rc != SQLITE_OK) return false;
    
    return true;
}

std::string SolutionCache::compute_hash(const InterferenceGraph& graph) {
    std::ostringstream oss;
    
    // Build canonical representation
    oss << "V" << graph.num_variables << "E";
    
    // Add edges in sorted order
    std::vector<std::pair<uint32_t, uint32_t>> edges;
    for (const auto& [v, neighbors] : graph.edges) {
        for (uint32_t n : neighbors) {
            if (v < n) {  // avoid duplicates
                edges.push_back({v, n});
            }
        }
    }
    std::sort(edges.begin(), edges.end());
    
    for (const auto& [u, v] : edges) {
        oss << u << "-" << v << ",";
    }
    
    // SHA256 hash
    std::string str = oss.str();
    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256(reinterpret_cast<const unsigned char*>(str.c_str()), 
           str.length(), hash);
    
    // Convert to hex string
    std::ostringstream hash_str;
    for (int i = 0; i < SHA256_DIGEST_LENGTH; ++i) {
        hash_str << std::hex << std::setw(2) << std::setfill('0') 
                 << static_cast<int>(hash[i]);
    }
    
    return hash_str.str();
}

std::string SolutionCache::graph_to_ast(const InterferenceGraph& graph) {
    std::ostringstream oss;
    oss << "InterferenceGraph{\n";
    oss << "  variables: " << graph.num_variables << ",\n";
    oss << "  edges: [\n";
    
    for (const auto& [v, neighbors] : graph.edges) {
        oss << "    " << v << " -> {";
        bool first = true;
        for (uint32_t n : neighbors) {
            if (!first) oss << ", ";
            oss << n;
            first = false;
        }
        oss << "},\n";
    }
    
    oss << "  ]\n}";
    return oss.str();
}

std::optional<CachedSolution> SolutionCache::lookup(const std::string& hash) {
    sqlite3_reset(stmt_lookup_);
    sqlite3_bind_text(stmt_lookup_, 1, hash.c_str(), -1, SQLITE_STATIC);
    
    int rc = sqlite3_step(stmt_lookup_);
    if (rc == SQLITE_ROW) {
        session_hits_++;
        
        CachedSolution sol;
        sol.graph_hash = hash;
        sol.graph_ast = reinterpret_cast<const char*>(
            sqlite3_column_text(stmt_lookup_, 1));
        sol.num_variables = sqlite3_column_int(stmt_lookup_, 2);
        sol.num_registers = sqlite3_column_int(stmt_lookup_, 3);
        sol.num_edges = sqlite3_column_int(stmt_lookup_, 4);
        sol.optimal_spills = sqlite3_column_int(stmt_lookup_, 5);
        sol.optimal_colors = sqlite3_column_int(stmt_lookup_, 6);
        sol.optimal_time_us = sqlite3_column_int64(stmt_lookup_, 7);
        sol.heuristic_spills = sqlite3_column_int(stmt_lookup_, 8);
        sol.heuristic_colors = sqlite3_column_int(stmt_lookup_, 9);
        sol.heuristic_time_us = sqlite3_column_int64(stmt_lookup_, 10);
        sol.improvement_pct = sqlite3_column_double(stmt_lookup_, 11);
        
        return sol;
    }
    
    session_misses_++;
    return std::nullopt;
}

bool SolutionCache::store(const CachedSolution& solution) {
    sqlite3_reset(stmt_insert_);
    
    sqlite3_bind_text(stmt_insert_, 1, solution.graph_hash.c_str(), -1, SQLITE_STATIC);
    sqlite3_bind_text(stmt_insert_, 2, solution.graph_ast.c_str(), -1, SQLITE_STATIC);
    sqlite3_bind_int(stmt_insert_, 3, solution.num_variables);
    sqlite3_bind_int(stmt_insert_, 4, solution.num_registers);
    sqlite3_bind_int(stmt_insert_, 5, solution.num_edges);
    sqlite3_bind_int(stmt_insert_, 6, solution.optimal_spills);
    sqlite3_bind_int(stmt_insert_, 7, solution.optimal_colors);
    sqlite3_bind_int64(stmt_insert_, 8, solution.optimal_time_us);
    sqlite3_bind_int(stmt_insert_, 9, solution.heuristic_spills);
    sqlite3_bind_int(stmt_insert_, 10, solution.heuristic_colors);
    sqlite3_bind_int64(stmt_insert_, 11, solution.heuristic_time_us);
    sqlite3_bind_double(stmt_insert_, 12, solution.improvement_pct);
    
    int rc = sqlite3_step(stmt_insert_);
    return rc == SQLITE_DONE;
}

SolutionCache::CacheStats SolutionCache::get_stats() {
    CacheStats stats;
    stats.hits = session_hits_;
    stats.misses = session_misses_;
    
    const char* stats_sql = R"(
        SELECT 
            COUNT(*) as total,
            AVG(optimal_time_us) / 1000.0 as avg_time_ms,
            AVG(improvement_pct) as avg_improvement
        FROM solutions
    )";
    
    sqlite3_stmt* stmt;
    sqlite3_prepare_v2(db_, stats_sql, -1, &stmt, nullptr);
    
    if (sqlite3_step(stmt) == SQLITE_ROW) {
        stats.total_entries = sqlite3_column_int64(stmt, 0);
        stats.avg_optimal_time_ms = sqlite3_column_double(stmt, 1);
        stats.avg_improvement_pct = sqlite3_column_double(stmt, 2);
    }
    
    sqlite3_finalize(stmt);
    return stats;
}

} // namespace optreg
