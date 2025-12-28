#pragma once
#include <string>
#include <vector>
#include <memory>
#include <variant>
#include <algorithm>
#include <iostream>
#include <numeric>

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
inline size_t computeHeight(const Node& node) {
    size_t max_child_height = 0;
    
    // Manual loop replaces `process-list-max-ir`
    for(const auto& child : node.children) {
        size_t h = computeHeight(*child);
        if (h > max_child_height) max_child_height = h;
    }
    
    return 1 + max_child_height;
}

// computeWidth : Node -> Nat
// Agda: max(own_width, children_max)
inline size_t computeWidth(Node& node) { // Non-const to allow "lazy" updates if needed, but here pure calc
    size_t child_max = 0;
    
    for(const auto& child : node.children) {
        size_t w = computeWidth(*child);
        if (w > child_max) child_max = w;
    }
    
    // Logic from BrowserIR.agda: max(node.width, child_max)
    size_t result = std::max(node.width, child_max);
    
    // Note: In a real layout, we might WRITE this result back to `node.width` 
    // but the Agda function `compute-width-ir` returns a Nat, it doesn't mutate node (pure).
    // So we return the calculated layout width.
    return result;
}

// Full Layout Pass (Mutation in C++ vs reconstruction in pure Agda)
// Just for demonstration
inline void layout(Node& node) {
    size_t w = computeWidth(node);
    // In a mutating model, we might update: node.width = w;
    // but let's stick to the pure calculation return.
}

} // namespace
