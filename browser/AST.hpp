#pragma once
#include <string>
#include <vector>
#include <map>
#include <memory>
#include <variant>

namespace browser_ast {

// ============================================================================
// HTML AST
// ============================================================================

struct HtmlNode {
    enum Type { Element, Text, Comment, Doctype };
    
    Type type;
    std::string tag;  // For Element
    std::map<std::string, std::string> attributes;
    std::vector<std::unique_ptr<HtmlNode>> children;
    std::string content;  // For Text/Comment/Doctype
    
    HtmlNode(Type t) : type(t) {}
    
    static std::unique_ptr<HtmlNode> makeElement(const std::string& tag) {
        auto node = std::make_unique<HtmlNode>(Element);
        node->tag = tag;
        return node;
    }
    
    static std::unique_ptr<HtmlNode> makeText(const std::string& text) {
        auto node = std::make_unique<HtmlNode>(Text);
        node->content = text;
        return node;
    }
    
    static std::unique_ptr<HtmlNode> makeComment(const std::string& text) {
        auto node = std::make_unique<HtmlNode>(Comment);
        node->content = text;
        return node;
    }
    
    static std::unique_ptr<HtmlNode> makeDoctype(const std::string& doctype) {
        auto node = std::make_unique<HtmlNode>(Doctype);
        node->content = doctype;
        return node;
    }
};

// ============================================================================
// CSS AST
// ============================================================================

struct CssDeclaration {
    std::string property;
    std::string value;
    bool important = false;
};

struct CssRule {
    std::vector<std::string> selectors;
    std::vector<CssDeclaration> declarations;
};

struct CssMediaQuery {
    std::string media_type;
    std::vector<std::string> conditions;
    std::vector<CssRule> rules;
};

struct CssStylesheet {
    std::vector<CssRule> rules;
    std::vector<CssMediaQuery> media_queries;
    std::vector<std::string> imports;  // @import URLs
};

// ============================================================================
// JavaScript AST (Simplified - Token Stream)
// ============================================================================

struct JsToken {
    enum Type {
        Keyword,      // if, function, var, let, const, etc.
        Identifier,   // variable names
        Literal,      // strings, numbers, booleans
        Operator,     // +, -, *, /, ==, etc.
        Punctuation,  // {, }, (, ), [, ], ;, etc.
        Comment,      // // or /* */
        Whitespace,
        Unknown
    };
    
    Type type;
    std::string value;
    size_t line;
    size_t column;
    
    JsToken(Type t, const std::string& v, size_t l = 0, size_t c = 0)
        : type(t), value(v), line(l), column(c) {}
};

struct JsTokenStream {
    std::vector<JsToken> tokens;
    std::string source_url;
};

// ============================================================================
// Complete Page AST
// ============================================================================

struct PageAst {
    std::unique_ptr<HtmlNode> html_root;
    std::vector<CssStylesheet> stylesheets;
    std::vector<JsTokenStream> scripts;
    std::string url;
    std::string title;
};

} // namespace browser_ast
