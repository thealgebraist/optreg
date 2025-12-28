#pragma once
#include <string>
#include <vector>
#include <memory>
#include <variant>
#include <algorithm>
#include <iostream>
#include <numeric>
#include <cstdio>
#include <array>

// ============================================================================
// C++23 Browser IR Implementation
// Matches BrowserIR.agda structure
// ============================================================================

namespace browser_ir {

// In Agda: Node = Record { tag, children, width, content }
// In C++, we can use a single struct since "Text" is just a Node with specific tag.
// Or we could use storage variants if we wanted to save space.
// Let's stick to the Agda IR Rep: TRec [tag, children, width, content]

struct Node {
    std::string tag;
    std::vector<std::unique_ptr<Node>> children;
    std::string content;
    size_t width; 

    // Constructor for convenience
    Node(std::string t, std::vector<std::unique_ptr<Node>> c = {}, std::string txt = "", size_t w = 0)
        : tag(std::move(t)), children(std::move(c)), content(std::move(txt)), width(w) {}
};

// ============================================================================
// Constructors (Factories)
// ============================================================================

// makeText(content) -> Node
inline std::unique_ptr<Node> makeText(const std::string& content) {
    // Agda: width=10 default
    return std::make_unique<Node>("TEXT", std::vector<std::unique_ptr<Node>>{}, content, 10);
}

// makeFetch(url) -> Node
// Fetches content via HTTP (using curl) and returns a TEXT node.
inline std::unique_ptr<Node> makeFetch(const std::string& url) {
    std::string content = "Fetch Failed: " + url;
    
    // Safety: Basic sanitation would be needed here.
    std::string cmd = "curl -s -m 5 \"" + url + "\"";
    FILE* pipe = popen(cmd.c_str(), "r");
    if (pipe) {
        std::array<char, 128> buffer;
        std::string result;
        while (fgets(buffer.data(), buffer.size(), pipe) != nullptr) {
            result += buffer.data();
        }
        pclose(pipe);
        if (!result.empty()) content = result;
    }

    // Return as a SPECIAL Fetch Node, or just Text?
    // Agda IR said tag="FETCH".
    return std::make_unique<Node>("FETCH", std::vector<std::unique_ptr<Node>>{}, content, 50);
}

// makeElement(tag, children) -> Node
inline std::unique_ptr<Node> makeElement(const std::string& tag, std::vector<std::unique_ptr<Node>> children) {
    // Agda: width=100 default
    return std::make_unique<Node>(tag, std::move(children), "", 100);
}

// ============================================================================
// Functional Algorithms (Recursive)
// ============================================================================

// computeHeight : Node -> Nat
// height(node) = 1 + max(map height node.children)
inline size_t computeHeight(const std::unique_ptr<Node>& node) {
    if (!node) return 0; 
    size_t max_child_height = 0;
    
    // Manual loop replaces `process-list-max-ir`
    for(const auto& child : node->children) {
        size_t h = computeHeight(child);
        if (h > max_child_height) max_child_height = h;
    }
    
    return 1 + max_child_height;
}

// computeWidth : Node -> Nat
// Agda: max(own_width, children_max)
inline size_t computeWidth(const std::unique_ptr<Node>& node) { 
    if (!node) return 0;
    size_t child_max = 0;
    
    for(const auto& child : node->children) {
        size_t w = computeWidth(child);
        if (w > child_max) child_max = w;
    }
    
    // Logic from BrowserIR.agda: max(node.width, child_max)
    size_t result = std::max(node->width, child_max);
    
    return result;
}

// Full Layout Pass (Mutation in C++ vs reconstruction in pure Agda)
inline void layout(std::unique_ptr<Node>& node) {
    size_t w = computeWidth(node);
}

} // namespace
