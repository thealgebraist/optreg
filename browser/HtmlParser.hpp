#pragma once
#include "AST.hpp"
#include <cctype>
#include <algorithm>

namespace browser_ast {

class HtmlParser {
public:
    static std::unique_ptr<HtmlNode> parse(const std::string& html) {
        HtmlParser parser(html);
        return parser.parseDocument();
    }

private:
    const std::string& html;
    size_t pos = 0;
    
    HtmlParser(const std::string& html) : html(html) {}
    
    char peek() const {
        return pos < html.size() ? html[pos] : '\0';
    }
    
    char advance() {
        return pos < html.size() ? html[pos++] : '\0';
    }
    
    void skipWhitespace() {
        while (pos < html.size() && std::isspace(html[pos])) {
            pos++;
        }
    }
    
    bool match(const std::string& str) {
        if (html.substr(pos, str.size()) == str) {
            pos += str.size();
            return true;
        }
        return false;
    }
    
    std::string parseUntil(char delimiter) {
        std::string result;
        while (peek() != delimiter && peek() != '\0') {
            result += advance();
        }
        return result;
    }
    
    std::unique_ptr<HtmlNode> parseDocument() {
        auto root = HtmlNode::makeElement("document");
        
        while (pos < html.size()) {
            skipWhitespace();
            if (pos >= html.size()) break;
            
            if (auto node = parseNode()) {
                root->children.push_back(std::move(node));
            }
        }
        
        return root;
    }
    
    std::unique_ptr<HtmlNode> parseNode() {
        skipWhitespace();
        
        if (peek() == '<') {
            advance();  // consume '<'
            
            // Check for special nodes
            if (match("!--")) {
                return parseComment();
            }
            if (match("!DOCTYPE") || match("!doctype")) {
                return parseDoctype();
            }
            if (peek() == '/') {
                // Closing tag - shouldn't be here in well-formed HTML
                // Skip it
                parseUntil('>');
                advance();  // consume '>'
                return nullptr;
            }
            
            return parseElement();
        } else {
            return parseText();
        }
    }
    
    std::unique_ptr<HtmlNode> parseComment() {
        std::string content;
        while (!(match("-->"))) {
            if (peek() == '\0') break;
            content += advance();
        }
        return HtmlNode::makeComment(content);
    }
    
    std::unique_ptr<HtmlNode> parseDoctype() {
        std::string doctype = parseUntil('>');
        advance();  // consume '>'
        return HtmlNode::makeDoctype(doctype);
    }
    
    std::unique_ptr<HtmlNode> parseElement() {
        // Parse tag name
        std::string tagName;
        while (peek() != '>' && peek() != '/' && !std::isspace(peek()) && peek() != '\0') {
            tagName += std::tolower(advance());
        }
        
        auto element = HtmlNode::makeElement(tagName);
        
        // Parse attributes
        skipWhitespace();
        while (peek() != '>' && peek() != '/' && peek() != '\0') {
            auto [key, value] = parseAttribute();
            if (!key.empty()) {
                element->attributes[key] = value;
            }
            skipWhitespace();
        }
        
        // Check for self-closing tag
        if (peek() == '/') {
            advance();  // consume '/'
            if (peek() == '>') advance();  // consume '>'
            return element;
        }
        
        if (peek() == '>') {
            advance();  // consume '>'
        }
        
        // Self-closing tags
        static const std::vector<std::string> voidElements = {
            "area", "base", "br", "col", "embed", "hr", "img", "input",
            "link", "meta", "param", "source", "track", "wbr"
        };
        
        if (std::find(voidElements.begin(), voidElements.end(), tagName) != voidElements.end()) {
            return element;
        }
        
        // Parse children
        while (pos < html.size()) {
            skipWhitespace();
            
            // Check for closing tag
            if (peek() == '<' && pos + 1 < html.size() && html[pos + 1] == '/') {
                advance();  // consume '<'
                advance();  // consume '/'
                std::string closingTag;
                while (peek() != '>' && peek() != '\0') {
                    closingTag += std::tolower(advance());
                }
                if (peek() == '>') advance();
                
                // Match closing tag (simplified - just check if it starts with our tag)
                if (closingTag.find(tagName) == 0) {
                    break;
                }
                continue;
            }
            
            if (auto child = parseNode()) {
                element->children.push_back(std::move(child));
            } else {
                break;
            }
        }
        
        return element;
    }
    
    std::pair<std::string, std::string> parseAttribute() {
        std::string key, value;
        
        // Parse key
        while (peek() != '=' && peek() != '>' && peek() != '/' && !std::isspace(peek()) && peek() != '\0') {
            key += std::tolower(advance());
        }
        
        skipWhitespace();
        
        if (peek() == '=') {
            advance();  // consume '='
            skipWhitespace();
            
            // Parse value
            if (peek() == '"' || peek() == '\'') {
                char quote = advance();
                while (peek() != quote && peek() != '\0') {
                    value += advance();
                }
                if (peek() == quote) advance();
            } else {
                while (peek() != '>' && peek() != '/' && !std::isspace(peek()) && peek() != '\0') {
                    value += advance();
                }
            }
        }
        
        return {key, value};
    }
    
    std::unique_ptr<HtmlNode> parseText() {
        std::string text;
        while (peek() != '<' && peek() != '\0') {
            text += advance();
        }
        
        // Trim whitespace
        size_t start = text.find_first_not_of(" \t\n\r");
        size_t end = text.find_last_not_of(" \t\n\r");
        
        if (start == std::string::npos) {
            return nullptr;  // All whitespace
        }
        
        text = text.substr(start, end - start + 1);
        return HtmlNode::makeText(text);
    }
};

} // namespace browser_ast
