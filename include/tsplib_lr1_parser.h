#pragma once
#include <string>
#include <vector>
#include <map>
#include <memory>
#include <stdexcept>

namespace tsplib {

// Token types for LR(1) parser
enum class TokenType {
    NAME, TYPE, COMMENT, DIMENSION, CAPACITY,
    EDGE_WEIGHT_TYPE, EDGE_WEIGHT_FORMAT,
    EDGE_DATA_FORMAT, NODE_COORD_TYPE,
    DISPLAY_DATA_TYPE,
    COLON, NUMBER, IDENTIFIER, STRING,
    EDGE_WEIGHT_SECTION, NODE_COORD_SECTION,
    DISPLAY_DATA_SECTION, DEPOT_SECTION,
    DEMAND_SECTION, FIXED_EDGES_SECTION,
    EOF_TOKEN, NEWLINE
};

struct Token {
    TokenType type;
    std::string value;
    int line;
    int col;
};

class TSPLIBLexer {
public:
    explicit TSPLIBLexer(const std::string& input);
    Token next_token();
    bool has_more() const { return pos_ < input_.size(); }
    
private:
    std::string input_;
    size_t pos_ = 0;
    int line_ = 1;
    int col_ = 1;
    
    void skip_whitespace();
    void skip_line();
    char peek() const;
    char advance();
    Token make_token(TokenType type, const std::string& value);
    Token read_number();
    Token read_identifier();
};

struct TSPLIBInstance {
    std::string name;
    std::string type;  // TSP, ATSP, etc.
    std::string comment;
    int dimension = 0;
    
    std::string edge_weight_type;   // EXPLICIT, EUC_2D, GEO, etc.
    std::string edge_weight_format; // FULL_MATRIX, UPPER_ROW, LOWER_DIAG_ROW, etc.
    
    // For EXPLICIT type
    std::vector<std::vector<double>> adj_matrix;
    
    // For EUC_2D, GEO, etc.
    std::vector<std::pair<double, double>> coords;
    
    bool is_valid() const { return dimension > 0; }
};

class TSPLIBParser {
public:
    explicit TSPLIBParser(const std::string& input);
    TSPLIBInstance parse();
    
private:
    TSPLIBLexer lexer_;
    Token current_;
    
    void advance();
    void expect(TokenType type);
    bool check(TokenType type) const;
    
    void parse_header();
    void parse_data_section();
    void parse_edge_weights();
    void parse_node_coords();
    
    TSPLIBInstance instance_;
};

} // namespace tsplib
