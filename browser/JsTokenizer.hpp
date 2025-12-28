#pragma once
#include "AST.hpp"
#include <cctype>
#include <unordered_set>

namespace browser_ast {

class JsTokenizer {
public:
    static JsTokenStream tokenize(const std::string& js, const std::string& source_url = "") {
        JsTokenizer tokenizer(js);
        auto tokens = tokenizer.tokenizeAll();
        return {tokens, source_url};
    }

private:
    const std::string& js;
    size_t pos = 0;
    size_t line = 1;
    size_t column = 1;
    
    static const std::unordered_set<std::string> keywords;
    
    JsTokenizer(const std::string& js) : js(js) {}
    
    char peek() const {
        return pos < js.size() ? js[pos] : '\0';
    }
    
    char advance() {
        char c = pos < js.size() ? js[pos++] : '\0';
        if (c == '\n') {
            line++;
            column = 1;
        } else {
            column++;
        }
        return c;
    }
    
    std::vector<JsToken> tokenizeAll() {
        std::vector<JsToken> tokens;
        
        while (pos < js.size()) {
            char c = peek();
            
            // Whitespace
            if (std::isspace(c)) {
                std::string ws;
                while (std::isspace(peek())) {
                    ws += advance();
                }
                tokens.push_back(JsToken(JsToken::Whitespace, ws, line, column));
                continue;
            }
            
            // Comments
            if (c == '/' && pos + 1 < js.size()) {
                if (js[pos + 1] == '/') {
                    std::string comment;
                    while (peek() != '\n' && peek() != '\0') {
                        comment += advance();
                    }
                    tokens.push_back(JsToken(JsToken::Comment, comment, line, column));
                    continue;
                }
                if (js[pos + 1] == '*') {
                    std::string comment;
                    comment += advance();  // '/'
                    comment += advance();  // '*'
                    while (!(peek() == '*' && pos + 1 < js.size() && js[pos + 1] == '/') && peek() != '\0') {
                        comment += advance();
                    }
                    if (peek() == '*') {
                        comment += advance();  // '*'
                        comment += advance();  // '/'
                    }
                    tokens.push_back(JsToken(JsToken::Comment, comment, line, column));
                    continue;
                }
            }
            
            // String literals
            if (c == '"' || c == '\'' || c == '`') {
                tokens.push_back(tokenizeString());
                continue;
            }
            
            // Numbers
            if (std::isdigit(c) || (c == '.' && pos + 1 < js.size() && std::isdigit(js[pos + 1]))) {
                tokens.push_back(tokenizeNumber());
                continue;
            }
            
            // Identifiers and keywords
            if (std::isalpha(c) || c == '_' || c == '$') {
                tokens.push_back(tokenizeIdentifier());
                continue;
            }
            
            // Operators and punctuation
            tokens.push_back(tokenizeOperatorOrPunctuation());
        }
        
        return tokens;
    }
    
    JsToken tokenizeString() {
        char quote = advance();
        std::string value;
        value += quote;
        
        while (peek() != quote && peek() != '\0') {
            if (peek() == '\\') {
                value += advance();  // backslash
                if (peek() != '\0') value += advance();  // escaped char
            } else {
                value += advance();
            }
        }
        
        if (peek() == quote) {
            value += advance();
        }
        
        return JsToken(JsToken::Literal, value, line, column);
    }
    
    JsToken tokenizeNumber() {
        std::string value;
        
        // Handle hex, octal, binary
        if (peek() == '0' && pos + 1 < js.size()) {
            char next = js[pos + 1];
            if (next == 'x' || next == 'X' || next == 'b' || next == 'B' || next == 'o' || next == 'O') {
                value += advance();  // '0'
                value += advance();  // 'x'/'b'/'o'
                while (std::isxdigit(peek()) || peek() == '_') {
                    value += advance();
                }
                return JsToken(JsToken::Literal, value, line, column);
            }
        }
        
        // Regular number
        while (std::isdigit(peek()) || peek() == '_') {
            value += advance();
        }
        
        // Decimal point
        if (peek() == '.' && pos + 1 < js.size() && std::isdigit(js[pos + 1])) {
            value += advance();
            while (std::isdigit(peek()) || peek() == '_') {
                value += advance();
            }
        }
        
        // Exponent
        if (peek() == 'e' || peek() == 'E') {
            value += advance();
            if (peek() == '+' || peek() == '-') {
                value += advance();
            }
            while (std::isdigit(peek()) || peek() == '_') {
                value += advance();
            }
        }
        
        return JsToken(JsToken::Literal, value, line, column);
    }
    
    JsToken tokenizeIdentifier() {
        std::string value;
        
        while (std::isalnum(peek()) || peek() == '_' || peek() == '$') {
            value += advance();
        }
        
        // Check if it's a keyword
        if (keywords.find(value) != keywords.end()) {
            return JsToken(JsToken::Keyword, value, line, column);
        }
        
        // Check for boolean/null literals
        if (value == "true" || value == "false" || value == "null" || value == "undefined") {
            return JsToken(JsToken::Literal, value, line, column);
        }
        
        return JsToken(JsToken::Identifier, value, line, column);
    }
    
    JsToken tokenizeOperatorOrPunctuation() {
        std::string value;
        char c = peek();
        
        // Multi-character operators
        static const std::vector<std::string> multiOps = {
            "===", "!==", ">>>", "<<=", ">>=", "**=", "&&=", "||=", "??=",
            "==", "!=", "<=", ">=", "<<", ">>", "&&", "||", "??", "++", "--",
            "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "=>", "**", "?."
        };
        
        for (const auto& op : multiOps) {
            if (js.substr(pos, op.size()) == op) {
                for (char ch : op) {
                    value += advance();
                }
                return JsToken(JsToken::Operator, value, line, column);
            }
        }
        
        // Single character
        value += advance();
        
        // Classify as operator or punctuation
        if (std::string("+-*/%<>=!&|^~?").find(c) != std::string::npos) {
            return JsToken(JsToken::Operator, value, line, column);
        } else {
            return JsToken(JsToken::Punctuation, value, line, column);
        }
    }
};

// JavaScript keywords
const std::unordered_set<std::string> JsTokenizer::keywords = {
    "break", "case", "catch", "class", "const", "continue", "debugger", "default",
    "delete", "do", "else", "export", "extends", "finally", "for", "function",
    "if", "import", "in", "instanceof", "let", "new", "return", "super",
    "switch", "this", "throw", "try", "typeof", "var", "void", "while",
    "with", "yield", "async", "await", "of", "static", "get", "set"
};

} // namespace browser_ast
