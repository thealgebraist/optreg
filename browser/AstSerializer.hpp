#pragma once
#include "AST.hpp"
#include <sstream>
#include <fstream>
#include <iomanip>

namespace browser_ast {

class AstSerializer {
public:
    // Serialize complete page AST to S-expression format
    static std::string serialize(const PageAst& page) {
        std::ostringstream oss;
        oss << "(page\n";
        oss << "  (url \"" << escape(page.url) << "\")\n";
        oss << "  (title \"" << escape(page.title) << "\")\n";
        
        if (page.html_root) {
            oss << "  (html\n";
            serializeHtml(oss, *page.html_root, 4);
            oss << "  )\n";
        }
        
        if (!page.stylesheets.empty()) {
            oss << "  (stylesheets\n";
            for (const auto& sheet : page.stylesheets) {
                serializeCss(oss, sheet, 4);
            }
            oss << "  )\n";
        }
        
        if (!page.scripts.empty()) {
            oss << "  (scripts\n";
            for (const auto& script : page.scripts) {
                serializeJs(oss, script, 4);
            }
            oss << "  )\n";
        }
        
        oss << ")\n";
        return oss.str();
    }
    
    // Save to file
    static bool saveToFile(const PageAst& page, const std::string& filename) {
        std::ofstream file(filename);
        if (!file.is_open()) return false;
        
        file << serialize(page);
        file.close();
        return true;
    }

private:
    static std::string indent(size_t level) {
        return std::string(level, ' ');
    }
    
    static std::string escape(const std::string& str) {
        std::string result;
        for (char c : str) {
            if (c == '"') result += "\\\"";
            else if (c == '\\') result += "\\\\";
            else if (c == '\n') result += "\\n";
            else if (c == '\t') result += "\\t";
            else result += c;
        }
        return result;
    }
    
    static void serializeHtml(std::ostringstream& oss, const HtmlNode& node, size_t level) {
        std::string ind = indent(level);
        
        switch (node.type) {
            case HtmlNode::Element:
                oss << ind << "(" << node.tag;
                if (!node.attributes.empty()) {
                    oss << "\n" << ind << "  (attrs";
                    for (const auto& [key, value] : node.attributes) {
                        oss << "\n" << ind << "    (" << key << " \"" << escape(value) << "\")";
                    }
                    oss << ")";
                }
                if (!node.children.empty()) {
                    oss << "\n";
                    for (const auto& child : node.children) {
                        serializeHtml(oss, *child, level + 2);
                    }
                    oss << ind;
                }
                oss << ")\n";
                break;
                
            case HtmlNode::Text:
                if (!node.content.empty() && node.content.find_first_not_of(" \t\n\r") != std::string::npos) {
                    oss << ind << "(text \"" << escape(node.content) << "\")\n";
                }
                break;
                
            case HtmlNode::Comment:
                oss << ind << "(comment \"" << escape(node.content) << "\")\n";
                break;
                
            case HtmlNode::Doctype:
                oss << ind << "(doctype \"" << escape(node.content) << "\")\n";
                break;
        }
    }
    
    static void serializeCss(std::ostringstream& oss, const CssStylesheet& sheet, size_t level) {
        std::string ind = indent(level);
        
        oss << ind << "(stylesheet\n";
        
        for (const auto& rule : sheet.rules) {
            oss << ind << "  (rule\n";
            oss << ind << "    (selectors";
            for (const auto& sel : rule.selectors) {
                oss << " \"" << escape(sel) << "\"";
            }
            oss << ")\n";
            
            oss << ind << "    (declarations\n";
            for (const auto& decl : rule.declarations) {
                oss << ind << "      (" << decl.property << " \"" << escape(decl.value) << "\"";
                if (decl.important) oss << " !important";
                oss << ")\n";
            }
            oss << ind << "    )\n";
            oss << ind << "  )\n";
        }
        
        oss << ind << ")\n";
    }
    
    static void serializeJs(std::ostringstream& oss, const JsTokenStream& stream, size_t level) {
        std::string ind = indent(level);
        
        oss << ind << "(script\n";
        if (!stream.source_url.empty()) {
            oss << ind << "  (src \"" << escape(stream.source_url) << "\")\n";
        }
        
        oss << ind << "  (tokens\n";
        size_t count = 0;
        for (const auto& token : stream.tokens) {
            if (token.type == JsToken::Whitespace || token.type == JsToken::Comment) continue;
            if (count++ > 100) {  // Limit token output
                oss << ind << "    ... (" << (stream.tokens.size() - 100) << " more tokens)\n";
                break;
            }
            oss << ind << "    (" << tokenTypeName(token.type) << " \"" << escape(token.value) << "\")\n";
        }
        oss << ind << "  )\n";
        oss << ind << ")\n";
    }
    
    static const char* tokenTypeName(JsToken::Type type) {
        switch (type) {
            case JsToken::Keyword: return "keyword";
            case JsToken::Identifier: return "id";
            case JsToken::Literal: return "lit";
            case JsToken::Operator: return "op";
            case JsToken::Punctuation: return "punct";
            case JsToken::Comment: return "comment";
            case JsToken::Whitespace: return "ws";
            default: return "unknown";
        }
    }
};

} // namespace browser_ast
