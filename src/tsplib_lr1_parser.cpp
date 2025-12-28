#include "tsplib_lr1_parser.h"
#include <sstream>
#include <cctype>
#include <cmath>
#include <iostream>

namespace tsplib {

// ============================================
// LEXER IMPLEMENTATION
// ============================================

TSPLIBLexer::TSPLIBLexer(const std::string& input) : input_(input) {}

void TSPLIBLexer::skip_whitespace() {
    while (pos_ < input_.size() && (input_[pos_] == ' ' || input_[pos_] == '\t')) {
        advance();
    }
}

void TSPLIBLexer::skip_line() {
    while (pos_ < input_.size() && input_[pos_] != '\n') {
        advance();
    }
}

char TSPLIBLexer::peek() const {
    return pos_ < input_.size() ? input_[pos_] : '\0';
}

char TSPLIBLexer::advance() {
    char c = peek();
    if (c == '\n') {
        line_++;
        col_ = 1;
    } else {
        col_++;
    }
    pos_++;
    return c;
}

Token TSPLIBLexer::make_token(TokenType type, const std::string& value) {
    return {type, value, line_, col_};
}

Token TSPLIBLexer::read_number() {
    std::string num;
    bool has_dot = false;
    
    if (peek() == '-' || peek() == '+') {
        num += advance();
    }
    
    while (std::isdigit(peek()) || (peek() == '.' && !has_dot)) {
        if (peek() == '.') has_dot = true;
        num += advance();
    }
    
    // Scientific notation
    if (peek() == 'e' || peek() == 'E') {
        num += advance();
        if (peek() == '-' || peek() == '+') {
            num += advance();
        }
        while (std::isdigit(peek())) {
            num += advance();
        }
    }
    
    return make_token(TokenType::NUMBER, num);
}

Token TSPLIBLexer::read_identifier() {
    std::string id;
    while (std::isalnum(peek()) || peek() == '_' || peek() == '-') {
        id += advance();
    }
    
    // Check for keywords
    static const std::map<std::string, TokenType> keywords = {
        {"NAME", TokenType::NAME},
        {"TYPE", TokenType::TYPE},
        {"COMMENT", TokenType::COMMENT},
        {"DIMENSION", TokenType::DIMENSION},
        {"CAPACITY", TokenType::CAPACITY},
        {"EDGE_WEIGHT_TYPE", TokenType::EDGE_WEIGHT_TYPE},
        {"EDGE_WEIGHT_FORMAT", TokenType::EDGE_WEIGHT_FORMAT},
        {"EDGE_DATA_FORMAT", TokenType::EDGE_DATA_FORMAT},
        {"NODE_COORD_TYPE", TokenType::NODE_COORD_TYPE},
        {"DISPLAY_DATA_TYPE", TokenType::DISPLAY_DATA_TYPE},
        {"EDGE_WEIGHT_SECTION", TokenType::EDGE_WEIGHT_SECTION},
        {"NODE_COORD_SECTION", TokenType::NODE_COORD_SECTION},
        {"DISPLAY_DATA_SECTION", TokenType::DISPLAY_DATA_SECTION},
        {"DEPOT_SECTION", TokenType::DEPOT_SECTION},
        {"DEMAND_SECTION", TokenType::DEMAND_SECTION},
        {"FIXED_EDGES_SECTION", TokenType::FIXED_EDGES_SECTION},
        {"EOF", TokenType::EOF_TOKEN}
    };
    
    auto it = keywords.find(id);
    if (it != keywords.end()) {
        return make_token(it->second, id);
    }
    
    return make_token(TokenType::IDENTIFIER, id);
}

Token TSPLIBLexer::next_token() {
    skip_whitespace();
    
    if (!has_more()) {
        return make_token(TokenType::EOF_TOKEN, "");
    }
    
    char c = peek();
    
    // Newline
    if (c == '\n' || c == '\r') {
        advance();
        if (c == '\r' && peek() == '\n') advance();
        return make_token(TokenType::NEWLINE, "\\n");
    }
    
    // Colon
    if (c == ':') {
        advance();
        skip_whitespace();
        // Read rest of line as string value
        std::string value;
        while (peek() != '\n' && peek() != '\r' && peek() != '\0') {
            value += advance();
        }
        // Trim trailing whitespace
        while (!value.empty() && (value.back() == ' ' || value.back() == '\t')) {
            value.pop_back();
        }
        return make_token(TokenType::STRING, value);
    }
    
    // Number
    if (std::isdigit(c) || c == '-' || c == '+' || c == '.') {
        if (c == '-' || c == '+' || c == '.') {
            // Check if next is digit
            if (pos_ + 1 < input_.size() && std::isdigit(input_[pos_ + 1])) {
                return read_number();
            }
        } else {
            return read_number();
        }
    }
    
    // Identifier/Keyword
    if (std::isalpha(c) || c == '_') {
        return read_identifier();
    }
    
    // Unknown character
    advance();
    return next_token();
}

// ============================================
// PARSER IMPLEMENTATION
// ============================================

TSPLIBParser::TSPLIBParser(const std::string& input) 
    : lexer_(input), current_(lexer_.next_token()) {}

void TSPLIBParser::advance() {
    current_ = lexer_.next_token();
    while (current_.type == TokenType::NEWLINE) {
        current_ = lexer_.next_token();
    }
}

void TSPLIBParser::expect(TokenType type) {
    if (current_.type != type) {
        throw std::runtime_error("Expected token type " + std::to_string(static_cast<int>(type)));
    }
    advance();
}

bool TSPLIBParser::check(TokenType type) const {
    return current_.type == type;
}

TSPLIBInstance TSPLIBParser::parse() {
    parse_header();
    parse_data_section();
    return instance_;
}

void TSPLIBParser::parse_header() {
    while (!check(TokenType::EOF_TOKEN)) {
        if (check(TokenType::NAME)) {
            advance();
            expect(TokenType::STRING);
            instance_.name = current_.value;
            advance();
        } else if (check(TokenType::TYPE)) {
            advance();
            expect(TokenType::STRING);
            instance_.type = current_.value;
            advance();
        } else if (check(TokenType::COMMENT)) {
            advance();
            expect(TokenType::STRING);
            instance_.comment = current_.value;
            advance();
        } else if (check(TokenType::DIMENSION)) {
            advance();
            expect(TokenType::STRING);
            instance_.dimension = std::stoi(current_.value);
            instance_.adj_matrix.resize(instance_.dimension, 
                std::vector<double>(instance_.dimension, 0));
            advance();
        } else if (check(TokenType::EDGE_WEIGHT_TYPE)) {
            advance();
            expect(TokenType::STRING);
            instance_.edge_weight_type = current_.value;
            advance();
        } else if (check(TokenType::EDGE_WEIGHT_FORMAT)) {
            advance();
            expect(TokenType::STRING);
            instance_.edge_weight_format = current_.value;
            advance();
        } else if (check(TokenType::EDGE_WEIGHT_SECTION) || 
                   check(TokenType::NODE_COORD_SECTION)) {
            break;
        } else {
            advance();
        }
    }
}

void TSPLIBParser::parse_data_section() {
    if (check(TokenType::EDGE_WEIGHT_SECTION)) {
        advance();
        parse_edge_weights();
    } else if (check(TokenType::NODE_COORD_SECTION)) {
        advance();
        parse_node_coords();
    }
}

void TSPLIBParser::parse_edge_weights() {
    int n = instance_.dimension;
    
    if (instance_.edge_weight_format == "LOWER_DIAG_ROW") {
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j <= i; ++j) {
                while (check(TokenType::NEWLINE)) advance();
                if (!check(TokenType::NUMBER)) break;
                double w = std::stod(current_.value);
                instance_.adj_matrix[i][j] = w;
                instance_.adj_matrix[j][i] = w;
                advance();
            }
        }
    } else if (instance_.edge_weight_format == "FULL_MATRIX") {
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                while (check(TokenType::NEWLINE)) advance();
                if (!check(TokenType::NUMBER)) break;
                instance_.adj_matrix[i][j] = std::stod(current_.value);
                advance();
            }
        }
    } else if (instance_.edge_weight_format == "UPPER_ROW") {
        for (int i = 0; i < n - 1; ++i) {
            for (int j = i + 1; j < n; ++j) {
                while (check(TokenType::NEWLINE)) advance();
                if (!check(TokenType::NUMBER)) break;
                double w = std::stod(current_.value);
                instance_.adj_matrix[i][j] = w;
                instance_.adj_matrix[j][i] = w;
                advance();
            }
        }
    }
}

void TSPLIBParser::parse_node_coords() {
    int n = instance_.dimension;
    instance_.coords.resize(n);
    
    for (int i = 0; i < n; ++i) {
        while (check(TokenType::NEWLINE)) advance();
        
        // Node index
        if (!check(TokenType::NUMBER)) break;
        advance();
        
        // X coordinate
        if (!check(TokenType::NUMBER)) break;
        double x = std::stod(current_.value);
        advance();
        
        // Y coordinate
        if (!check(TokenType::NUMBER)) break;
        double y = std::stod(current_.value);
        advance();
        
        instance_.coords[i] = {x, y};
    }
    
    // Compute Euclidean distances
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            double dx = instance_.coords[i].first - instance_.coords[j].first;
            double dy = instance_.coords[i].second - instance_.coords[j].second;
            instance_.adj_matrix[i][j] = std::round(std::sqrt(dx*dx + dy*dy));
        }
    }
}

} // namespace tsplib
