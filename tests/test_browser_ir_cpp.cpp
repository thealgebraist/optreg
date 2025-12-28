#include <iostream>
#include <cassert>
#include <vector>
#include "../browser/BrowserIR.hpp"

using namespace browser_ir;

int main() {
    std::cout << "Testing Browser IR (C++23 conversion)...\n";
    
    // Construct Tree: div > [ "hello" ]
    // Corresponds to Agda: makeElement "div" (Cons (makeText "hello") Nil)
    
    std::vector<std::unique_ptr<Node>> children;
    children.push_back(makeText("hello"));
    
    auto root = makeElement("div", std::move(children));
    
    // Verify Structure
    assert(root->tag == "div");
    assert(root->children.size() == 1);
    assert(root->children[0]->tag == "TEXT");
    assert(root->children[0]->content == "hello");
    
    // Verify Algorithms
    std::cout << "Root Tag: " << root->tag << "\n";
    
    size_t height = computeHeight(*root);
    std::cout << "Height: " << height << "\n";
    // Text has height 1 (leaf)
    // Div has height 1 + max(child) = 2
    assert(height == 2);
    
    size_t width = computeWidth(*root);
    std::cout << "Width: " << width << "\n";
    
    // Text default width = 10
    // Div default width = 100
    // Logic: max(100, 10) = 100
    assert(width == 100);
    
    // Test nested
    // div2 > div > text
    std::vector<std::unique_ptr<Node>> outer_children;
    outer_children.push_back(std::move(root)); // Move root into outer
    
    auto outer = makeElement("section", std::move(outer_children));
    
    size_t h2 = computeHeight(*outer);
    std::cout << "Nested Height: " << h2 << "\n"; // Should be 3
    assert(h2 == 3);
    
    std::cout << "All tests passed.\n";
    return 0;
}
