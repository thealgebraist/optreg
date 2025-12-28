#include "optreg/browser/AST.hpp"
#include "optreg/browser/AstSerializer.hpp"
#include "optreg/browser/HtmlParser.hpp"
#include "optreg/browser/CssParser.hpp"
#include "optreg/browser/JsTokenizer.hpp"
#include "optreg/browser/StyleEngine.hpp"
#include "optreg/browser/LayoutEngine.hpp"
#include "optreg/browser/Renderer.hpp"
#include <iostream>
#include <cstdio>
#include <array>

using namespace browser_ast;

// Fetch URL content using curl
std::string fetchUrl(const std::string& url) {
    std::string cmd = "curl -s -L -m 10 \"" + url + "\"";
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        std::cerr << "Failed to execute curl" << std::endl;
        return "";
    }
    
    std::array<char, 128> buffer;
    std::string result;
    while (fgets(buffer.data(), buffer.size(), pipe) != nullptr) {
        result += buffer.data();
    }
    pclose(pipe);
    
    return result;
}

// Extract inline CSS from <style> tags
std::vector<CssStylesheet> extractInlineCss(const HtmlNode& node) {
    std::vector<CssStylesheet> stylesheets;
    
    if (node.type == HtmlNode::Element && node.tag == "style") {
        for (const auto& child : node.children) {
            if (child->type == HtmlNode::Text) {
                auto stylesheet = CssParser::parse(child->content);
                stylesheets.push_back(stylesheet);
            }
        }
    }
    
    for (const auto& child : node.children) {
        auto childSheets = extractInlineCss(*child);
        stylesheets.insert(stylesheets.end(), childSheets.begin(), childSheets.end());
    }
    
    return stylesheets;
}

int main(int argc, char* argv[]) {
    std::string url = "https://www.cnn.com";
    
    // Allow custom URL from command line
    if (argc > 1) {
        url = argv[1];
    }
    
    std::cout << "=== MiniChrome Visual Browser ===" << std::endl;
    std::cout << "Fetching " << url << "..." << std::endl;
    
    std::string html = fetchUrl(url);
    
    if (html.empty()) {
        std::cerr << "Failed to fetch content" << std::endl;
        return 1;
    }
    
    std::cout << "Fetched " << html.size() << " bytes" << std::endl;
    std::cout << "Parsing HTML..." << std::endl;
    
    // Parse HTML
    auto htmlRoot = HtmlParser::parse(html);
    
    // Extract and parse CSS
    std::cout << "Parsing CSS..." << std::endl;
    auto stylesheets = extractInlineCss(*htmlRoot);
    std::cout << "Found " << stylesheets.size() << " stylesheets" << std::endl;
    
    // Compute layout
    std::cout << "Computing layout..." << std::endl;
    int viewport_width = 1024;
    auto layoutRoot = LayoutEngine::computeLayout(*htmlRoot, stylesheets, viewport_width);
    
    std::cout << "Layout computed: " << layoutRoot.borderBoxWidth() << "x" << layoutRoot.borderBoxHeight() << std::endl;
    
    // Count total boxes
    auto flatBoxes = LayoutEngine::flatten(layoutRoot);
    std::cout << "Total layout boxes: " << flatBoxes.size() << std::endl;
    
    // Initialize renderer
    std::cout << "Initializing renderer..." << std::endl;
    Renderer renderer;
    if (!renderer.init(viewport_width, 768, "MiniChrome - " + url)) {
        std::cerr << "Failed to initialize renderer" << std::endl;
        return 1;
    }
    
    std::cout << "\n=== Controls ===" << std::endl;
    std::cout << "Mouse Wheel: Scroll" << std::endl;
    std::cout << "ESC or Q: Quit" << std::endl;
    std::cout << "\nRendering..." << std::endl;
    
    // Render and run event loop
    renderer.render(layoutRoot);
    renderer.handleEvents();
    
    std::cout << "Browser closed." << std::endl;
    return 0;
}
