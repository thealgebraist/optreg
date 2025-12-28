#pragma once
#include "AST.hpp"
#include <cctype>
#include <sstream>

namespace browser_ast {

class CssParser {
public:
    static CssStylesheet parse(const std::string& css) {
        CssParser parser(css);
        return parser.parseStylesheet();
    }

private:
    const std::string& css;
    size_t pos = 0;
    
    CssParser(const std::string& css) : css(css) {}
    
    char peek() const {
        return pos < css.size() ? css[pos] : '\0';
    }
    
    char advance() {
        return pos < css.size() ? css[pos++] : '\0';
    }
    
    void skipWhitespace() {
        while (pos < css.size() && std::isspace(css[pos])) {
            pos++;
        }
    }
    
    void skipComments() {
        while (pos + 1 < css.size() && css[pos] == '/' && css[pos + 1] == '*') {
            pos += 2;
            while (pos + 1 < css.size() && !(css[pos] == '*' && css[pos + 1] == '/')) {
                pos++;
            }
            if (pos + 1 < css.size()) pos += 2;
        }
    }
    
    void skip() {
        while (true) {
            size_t oldPos = pos;
            skipWhitespace();
            skipComments();
            if (pos == oldPos) break;
        }
    }
    
    CssStylesheet parseStylesheet() {
        CssStylesheet sheet;
        
        while (pos < css.size()) {
            skip();
            if (pos >= css.size()) break;
            
            // Check for @import
            if (css.substr(pos, 7) == "@import") {
                pos += 7;
                skip();
                std::string url = parseString();
                sheet.imports.push_back(url);
                // Skip until semicolon
                while (peek() != ';' && peek() != '\0') advance();
                if (peek() == ';') advance();
                continue;
            }
            
            // Check for @media
            if (css.substr(pos, 6) == "@media") {
                auto mediaQuery = parseMediaQuery();
                sheet.media_queries.push_back(mediaQuery);
                continue;
            }
            
            // Parse regular rule
            auto rule = parseRule();
            if (!rule.selectors.empty()) {
                sheet.rules.push_back(rule);
            }
        }
        
        return sheet;
    }
    
    CssMediaQuery parseMediaQuery() {
        CssMediaQuery query;
        pos += 6;  // skip "@media"
        skip();
        
        // Parse media type and conditions (simplified)
        std::string condition;
        while (peek() != '{' && peek() != '\0') {
            condition += advance();
        }
        query.media_type = condition;
        
        if (peek() == '{') {
            advance();
            
            // Parse rules inside media query
            while (peek() != '}' && peek() != '\0') {
                skip();
                if (peek() == '}') break;
                auto rule = parseRule();
                if (!rule.selectors.empty()) {
                    query.rules.push_back(rule);
                }
            }
            
            if (peek() == '}') advance();
        }
        
        return query;
    }
    
    CssRule parseRule() {
        CssRule rule;
        
        // Parse selectors
        std::string selectorText;
        while (peek() != '{' && peek() != '\0') {
            selectorText += advance();
        }
        
        // Split by comma
        std::istringstream ss(selectorText);
        std::string selector;
        while (std::getline(ss, selector, ',')) {
            // Trim whitespace
            size_t start = selector.find_first_not_of(" \t\n\r");
            size_t end = selector.find_last_not_of(" \t\n\r");
            if (start != std::string::npos) {
                selector = selector.substr(start, end - start + 1);
                rule.selectors.push_back(selector);
            }
        }
        
        if (peek() == '{') {
            advance();
            
            // Parse declarations
            while (peek() != '}' && peek() != '\0') {
                skip();
                if (peek() == '}') break;
                
                auto decl = parseDeclaration();
                if (!decl.property.empty()) {
                    rule.declarations.push_back(decl);
                }
            }
            
            if (peek() == '}') advance();
        }
        
        return rule;
    }
    
    CssDeclaration parseDeclaration() {
        CssDeclaration decl;
        
        skip();
        
        // Parse property
        while (peek() != ':' && peek() != '}' && peek() != '\0') {
            decl.property += advance();
        }
        
        // Trim property
        size_t start = decl.property.find_first_not_of(" \t\n\r");
        size_t end = decl.property.find_last_not_of(" \t\n\r");
        if (start != std::string::npos) {
            decl.property = decl.property.substr(start, end - start + 1);
        }
        
        if (peek() == ':') {
            advance();
            skip();
            
            // Parse value
            while (peek() != ';' && peek() != '}' && peek() != '\0') {
                decl.value += advance();
            }
            
            // Check for !important
            size_t importantPos = decl.value.find("!important");
            if (importantPos != std::string::npos) {
                decl.important = true;
                decl.value = decl.value.substr(0, importantPos);
            }
            
            // Trim value
            start = decl.value.find_first_not_of(" \t\n\r");
            end = decl.value.find_last_not_of(" \t\n\r");
            if (start != std::string::npos) {
                decl.value = decl.value.substr(start, end - start + 1);
            }
            
            if (peek() == ';') advance();
        }
        
        return decl;
    }
    
    std::string parseString() {
        std::string result;
        skip();
        
        if (peek() == '"' || peek() == '\'') {
            char quote = advance();
            while (peek() != quote && peek() != '\0') {
                result += advance();
            }
            if (peek() == quote) advance();
        } else {
            while (!std::isspace(peek()) && peek() != ';' && peek() != '\0') {
                result += advance();
            }
        }
        
        return result;
    }
};

} // namespace browser_ast
