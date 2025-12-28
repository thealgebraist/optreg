#pragma once
#include "AST.hpp"
#include <optional>
#include <string>
#include <algorithm>
#include <sstream>

namespace browser_ast {

struct ComputedStyle {
    enum Display { Block, Inline, InlineBlock, None };
    
    Display display = Block;
    std::optional<int> width;
    std::optional<int> height;
    
    struct BoxEdge {
        int top = 0, right = 0, bottom = 0, left = 0;
    };
    
    BoxEdge margin;
    BoxEdge padding;
    BoxEdge border;
    
    struct Color {
        uint8_t r = 255, g = 255, b = 255;
    } background_color, text_color;
    
    std::string font_size = "16px";
    std::string font_weight = "normal";
};

class StyleEngine {
public:
    // Compute style for a node given stylesheets
    static ComputedStyle computeStyle(
        const HtmlNode& node,
        const std::vector<CssStylesheet>& sheets,
        const ComputedStyle* parent_style = nullptr
    ) {
        ComputedStyle style;
        
        // Default styles based on tag
        applyDefaultStyles(node, style);
        
        // Apply CSS rules
        for (const auto& sheet : sheets) {
            for (const auto& rule : sheet.rules) {
                if (matchesSelector(node, rule.selectors)) {
                    applyDeclarations(rule.declarations, style);
                }
            }
        }
        
        // Apply inline styles
        auto style_attr = node.attributes.find("style");
        if (style_attr != node.attributes.end()) {
            applyInlineStyle(style_attr->second, style);
        }
        
        // Inherit from parent
        if (parent_style) {
            inheritStyles(*parent_style, style);
        }
        
        return style;
    }

private:
    static void applyDefaultStyles(const HtmlNode& node, ComputedStyle& style) {
        if (node.type != HtmlNode::Element) {
            style.display = ComputedStyle::Inline;
            return;
        }
        
        // Block-level elements
        static const std::vector<std::string> blockElements = {
            "html", "body", "div", "p", "h1", "h2", "h3", "h4", "h5", "h6",
            "ul", "ol", "li", "header", "footer", "section", "article", "nav",
            "main", "aside", "form", "table", "tr"
        };
        
        if (std::find(blockElements.begin(), blockElements.end(), node.tag) != blockElements.end()) {
            style.display = ComputedStyle::Block;
        } else if (node.tag == "td" || node.tag == "th") {
            // Table cells behave like InlineBlock in simplified model (shrink-to-fit, side-by-side)
            style.display = ComputedStyle::InlineBlock;
        } else {
            style.display = ComputedStyle::Inline;
        }
        
        // Default margins for headings and paragraphs
        if (node.tag == "h1") {
            style.margin = {16, 0, 16, 0};
            style.font_size = "32px";
            style.font_weight = "bold";
        } else if (node.tag == "h2") {
            style.margin = {14, 0, 14, 0};
            style.font_size = "24px";
            style.font_weight = "bold";
        } else if (node.tag == "p") {
            style.margin = {8, 0, 8, 0};
        } else if (node.tag == "body") {
            style.margin = {8, 8, 8, 8};
        }
    }
    
    static bool matchesSelector(const HtmlNode& node, const std::vector<std::string>& selectors) {
        if (node.type != HtmlNode::Element) return false;
        
        for (const auto& selector : selectors) {
            if (matchesSingleSelector(node, selector)) {
                return true;
            }
        }
        return false;
    }
    
    static bool matchesSingleSelector(const HtmlNode& node, const std::string& selector) {
        std::string trimmed = trim(selector);
        
        // Universal selector
        if (trimmed == "*") return true;
        
        // Tag selector
        if (trimmed[0] != '.' && trimmed[0] != '#') {
            return node.tag == trimmed;
        }
        
        // Class selector
        if (trimmed[0] == '.') {
            std::string className = trimmed.substr(1);
            auto classAttr = node.attributes.find("class");
            if (classAttr != node.attributes.end()) {
                return classAttr->second.find(className) != std::string::npos;
            }
            return false;
        }
        
        // ID selector
        if (trimmed[0] == '#') {
            std::string id = trimmed.substr(1);
            auto idAttr = node.attributes.find("id");
            return idAttr != node.attributes.end() && idAttr->second == id;
        }
        
        return false;
    }
    
    static void applyDeclarations(const std::vector<CssDeclaration>& declarations, ComputedStyle& style) {
        for (const auto& decl : declarations) {
            applyDeclaration(decl, style);
        }
    }
    
    static void applyDeclaration(const CssDeclaration& decl, ComputedStyle& style) {
        if (decl.property == "display") {
            if (decl.value == "block") style.display = ComputedStyle::Block;
            else if (decl.value == "inline") style.display = ComputedStyle::Inline;
            else if (decl.value == "inline-block") style.display = ComputedStyle::InlineBlock;
            else if (decl.value == "none") style.display = ComputedStyle::None;
        }
        else if (decl.property == "width") {
            style.width = parsePx(decl.value);
        }
        else if (decl.property == "height") {
            style.height = parsePx(decl.value);
        }
        else if (decl.property == "margin") {
            auto values = parseBoxEdge(decl.value);
            style.margin = values;
        }
        else if (decl.property == "margin-top") {
            style.margin.top = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "margin-right") {
            style.margin.right = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "margin-bottom") {
            style.margin.bottom = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "margin-left") {
            style.margin.left = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "padding") {
            auto values = parseBoxEdge(decl.value);
            style.padding = values;
        }
        else if (decl.property == "padding-top") {
            style.padding.top = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "padding-right") {
            style.padding.right = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "padding-bottom") {
            style.padding.bottom = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "padding-left") {
            style.padding.left = parsePx(decl.value).value_or(0);
        }
        else if (decl.property == "float") {
            if (decl.value == "left" || decl.value == "right") {
                // Simplified Engine: Treat float as InlineBlock to enforce shrink-to-fit
                style.display = ComputedStyle::InlineBlock;
            }
        }
        else if (decl.property == "background-color" || decl.property == "background") {
            style.background_color = parseColor(decl.value);
        }
        else if (decl.property == "color") {
            style.text_color = parseColor(decl.value);
        }
    }
    
    static void applyInlineStyle(const std::string& styleText, ComputedStyle& style) {
        // Parse inline style="prop: value; prop: value"
        std::istringstream ss(styleText);
        std::string declaration;
        
        while (std::getline(ss, declaration, ';')) {
            size_t colonPos = declaration.find(':');
            if (colonPos != std::string::npos) {
                std::string prop = trim(declaration.substr(0, colonPos));
                std::string value = trim(declaration.substr(colonPos + 1));
                CssDeclaration decl{prop, value, false};
                applyDeclaration(decl, style);
            }
        }
    }
    
    static void inheritStyles(const ComputedStyle& parent, ComputedStyle& child) {
        // Inherit text color
        if (child.text_color.r == 255 && child.text_color.g == 255 && child.text_color.b == 255) {
            child.text_color = parent.text_color;
        }
        
        // Inherit font properties
        // For text nodes (or any child really, unless overridden), font size/weight should inherit.
        // Simple logic: if child has default "16px" and parent has something else, use parent?
        // Better: Always overwrite if it's a Text node? 
        // Text nodes don't accept classes so they can't override via CSS rules (except inline logic which we don't have on text nodes).
        // Since StyleEngine sets defaults first, we need to know if it was *explicitly* set?
        // For now, let's just copy parent's font properties to child.
        // In a real engine, we'd handle the cascade better (only inherit if not specified).
        // But since Text nodes are generated and have no selectors, they rely 100% on inheritance.
        
        child.font_size = parent.font_size;
        child.font_weight = parent.font_weight;
    }
    
    static std::optional<int> parsePx(const std::string& value) {
        std::string trimmed = trim(value);
        if (trimmed.empty()) return std::nullopt;
        
        // Remove "px" suffix
        if (trimmed.size() >= 2 && trimmed.substr(trimmed.size() - 2) == "px") {
            trimmed = trimmed.substr(0, trimmed.size() - 2);
        }
        
        try {
            return std::stoi(trimmed);
        } catch (...) {
            return std::nullopt;
        }
    }
    
    static ComputedStyle::BoxEdge parseBoxEdge(const std::string& value) {
        std::istringstream ss(value);
        std::vector<int> values;
        std::string token;
        
        while (ss >> token) {
            auto px = parsePx(token);
            if (px) values.push_back(*px);
        }
        
        ComputedStyle::BoxEdge edge;
        if (values.size() == 1) {
            edge.top = edge.right = edge.bottom = edge.left = values[0];
        } else if (values.size() == 2) {
            edge.top = edge.bottom = values[0];
            edge.right = edge.left = values[1];
        } else if (values.size() == 3) {
            edge.top = values[0];
            edge.right = edge.left = values[1];
            edge.bottom = values[2];
        } else if (values.size() >= 4) {
            edge.top = values[0];
            edge.right = values[1];
            edge.bottom = values[2];
            edge.left = values[3];
        }
        
        return edge;
    }
    
    static ComputedStyle::Color parseColor(const std::string& value) {
        std::string trimmed = trim(value);
        ComputedStyle::Color color;
        
        // Named colors
        if (trimmed == "white") return {255, 255, 255};
        if (trimmed == "black") return {0, 0, 0};
        if (trimmed == "red") return {255, 0, 0};
        if (trimmed == "green") return {0, 128, 0};
        if (trimmed == "blue") return {0, 0, 255};
        if (trimmed == "gray" || trimmed == "grey") return {128, 128, 128};
        
        // Hex colors
        if (trimmed[0] == '#') {
            std::string hex = trimmed.substr(1);
            if (hex.size() == 6) {
                color.r = std::stoi(hex.substr(0, 2), nullptr, 16);
                color.g = std::stoi(hex.substr(2, 2), nullptr, 16);
                color.b = std::stoi(hex.substr(4, 2), nullptr, 16);
            } else if (hex.size() == 3) {
                color.r = std::stoi(std::string(2, hex[0]), nullptr, 16);
                color.g = std::stoi(std::string(2, hex[1]), nullptr, 16);
                color.b = std::stoi(std::string(2, hex[2]), nullptr, 16);
            }
        }
        
        // RGB colors
        if (trimmed.substr(0, 4) == "rgb(") {
            size_t start = 4;
            size_t end = trimmed.find(')');
            if (end != std::string::npos) {
                std::string rgb = trimmed.substr(start, end - start);
                std::istringstream ss(rgb);
                std::string token;
                std::vector<int> values;
                while (std::getline(ss, token, ',')) {
                    values.push_back(std::stoi(trim(token)));
                }
                if (values.size() >= 3) {
                    color.r = values[0];
                    color.g = values[1];
                    color.b = values[2];
                }
            }
        }
        
        return color;
    }
    
    static std::string trim(const std::string& str) {
        size_t start = str.find_first_not_of(" \t\n\r");
        if (start == std::string::npos) return "";
        size_t end = str.find_last_not_of(" \t\n\r");
        return str.substr(start, end - start + 1);
    }
};

} // namespace browser_ast
