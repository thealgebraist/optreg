#include "BrowserIR.hpp"
#include <iostream>
#include <vector>
#include <memory>
#include <cstring>

using namespace browser_ir;

extern "C" {

// ABI: Pointers are passed as uint64_t / pointer (X0)

// Helper: Vector of Node pointers (opaque to ASM)
typedef std::vector<std::unique_ptr<Node>> NodeVec;

// c_make_nil() -> NodeVec*
void* c_make_nil() {
    return new NodeVec();
}

// c_cons(Node* head, NodeVec* tail) -> NodeVec*
// Takes ownership of head.
void* c_cons(void* head, void* tail) {
    auto vec = static_cast<NodeVec*>(tail);
    auto node = static_cast<Node*>(head);
    // Insert at beginning (Cons)
    vec->insert(vec->begin(), std::unique_ptr<Node>(node));
    return vec;
}

// c_make_text(char* content) -> Node*
void* c_make_text(const char* content) {
    auto node = makeText(content);
    return node.release();
}

// c_make_fetch(char* url) -> Node*
void* c_make_fetch(const char* url) {
    auto node = makeFetch(url);
    return node.release();
}

// c_make_element(char* tag, NodeVec* children) -> Node*
void* c_make_element(const char* tag, void* children) {
    auto vec = static_cast<NodeVec*>(children);
    // makeElement takes ownership of vector contents
    // We pass *vec (move it?) makeElement takes vector by value.
    auto node = makeElement(tag, std::move(*vec));
    delete vec; // Delete the vector container, contents moved.
    return node.release();
}

// c_compute_height(Node* root) -> uint64_t
uint64_t c_compute_height(void* root) {
    Node* node = static_cast<Node*>(root);
    // Re-wrap in unique_ptr for the call (non-owning? No, computeHeight takes const ref)
    // But computeHeight expects unique_ptr<Node>&. 
    // We can allow it to bind to a temporary unique_ptr wrapping this raw pointer
    // BUT we must `release()` it after, or it will delete `root`.
    
    std::unique_ptr<Node> ptr(node);
    size_t h = computeHeight(ptr);
    ptr.release(); // release ownership so it doesn't destruct
    return h;
}

// c_compute_width(Node* root) -> uint64_t
uint64_t c_compute_width(void* root) {
    Node* node = static_cast<Node*>(root);
    std::unique_ptr<Node> ptr(node);
    size_t w = computeWidth(ptr);
    ptr.release();
    return w;
}

void c_print_result(uint64_t res) {
    std::cout << "ARM64 Result: " << res << std::endl;
}

}
