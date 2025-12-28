#pragma once
#include "AST.hpp"
#include "StyleEngine.hpp"
#include <vector>
#include <algorithm>
#include <cmath>
#include <iostream>
#include <cassert>

namespace browser_ast {

struct LayoutBox {
    // Position (relative to containing block)
    int x = 0, y = 0;
    
    // Content box dimensions
    int content_width = 0, content_height = 0;
    
    // Box model edges
    struct {
        int top = 0, right = 0, bottom = 0, left = 0;
    } margin, border, padding;
    
    // Visual properties
    uint8_t bg_r = 255, bg_g = 255, bg_b = 255;
    
    // Content
    std::string text_content;
    ComputedStyle::Display display_type;
    
    // Children
    std::vector<LayoutBox> children;
    
    // Computed dimensions including box model
    int borderBoxWidth() const {
        return padding.left + content_width + padding.right + 
               border.left + border.right;
    }
    
    int borderBoxHeight() const {
        return padding.top + content_height + padding.bottom + 
               border.top + border.bottom;
    }
    
    int marginBoxWidth() const {
        return margin.left + borderBoxWidth() + margin.right;
    }
    
    int marginBoxHeight() const {
        return margin.top + borderBoxHeight() + margin.bottom;
    }
};

class LayoutEngine {
public:
    static LayoutBox computeLayout(
        const HtmlNode& node,
        const std::vector<CssStylesheet>& sheets,
        int containing_block_width,
        int containing_block_x = 0,
        int containing_block_y = 0,
        const ComputedStyle* parent_style = nullptr
    ) {
        auto style = StyleEngine::computeStyle(node, sheets, parent_style);
        
        if (style.display == ComputedStyle::None) {
            return LayoutBox{};
        }
        
        LayoutBox box;
        box.display_type = style.display;
        
        // Apply box model edges
        applyBoxModel(box, style);
        
        // Background color
        box.bg_r = style.background_color.r;
        box.bg_g = style.background_color.g;
        box.bg_b = style.background_color.b;
        
        // Handle text nodes
        if (node.type == HtmlNode::Text) {
            box.text_content = node.content;
            layoutTextNode(box, style, containing_block_width);
            box.x = containing_block_x;
            box.y = containing_block_y;
            return box;
        }
        
        // Layout based on display type
        if (style.display == ComputedStyle::Block) {
            layoutBlockBox(box, node, style, sheets, 
                          containing_block_width, containing_block_x, containing_block_y);
        } else if (style.display == ComputedStyle::Inline || 
                   style.display == ComputedStyle::InlineBlock) {
            layoutInlineBox(box, node, style, sheets,
                           containing_block_width, containing_block_x, containing_block_y);
        }
        
        return box;
    }

private:
    static void applyBoxModel(LayoutBox& box, const ComputedStyle& style) {
        box.margin.top = style.margin.top;
        box.margin.right = style.margin.right;
        box.margin.bottom = style.margin.bottom;
        box.margin.left = style.margin.left;
        
        box.padding.top = style.padding.top;
        box.padding.right = style.padding.right;
        box.padding.bottom = style.padding.bottom;
        box.padding.left = style.padding.left;
        
        box.border.top = style.border.top;
        box.border.right = style.border.right;
        box.border.bottom = style.border.bottom;
        box.border.left = style.border.left;
    }
    
    static void layoutTextNode(LayoutBox& box, const ComputedStyle& style, int containing_width) {
        // Simplified text layout - estimate dimensions
        // In real browser, this would use font metrics
        int char_width = 8;  // Approximate character width
        int line_height = 20;  // Approximate line height
        
        int text_length = box.text_content.length();
        int available_width = containing_width - box.padding.left - box.padding.right;
        
        if (available_width <= 0) available_width = containing_width;
        
        // Estimate number of lines
        int chars_per_line = std::max(1, available_width / char_width);
        int num_lines = std::max(1, (text_length + chars_per_line - 1) / chars_per_line);
        
        box.content_width = std::min(text_length * char_width, available_width);
        box.content_height = num_lines * line_height;
    }
    
    static void layoutBlockBox(
        LayoutBox& box,
        const HtmlNode& node,
        const ComputedStyle& style,
        const std::vector<CssStylesheet>& sheets,
        int containing_block_width,
        int cb_x,
        int cb_y
    ) {
        // CSS 2.1 Section 10.3.3: Block-level, non-replaced elements in normal flow
        
        // Calculate width
        int available_width = containing_block_width;
        
        if (style.width.has_value()) {
            // Explicit width
            box.content_width = *style.width;
        } else {
            // Auto width: width = containing_block_width - horizontal margins/borders/padding
            int horizontal_space = box.margin.left + box.border.left + box.padding.left +
                                  box.padding.right + box.border.right + box.margin.right;
            box.content_width = available_width - horizontal_space;
            
            // Ensure non-negative
            if (box.content_width < 0) box.content_width = 0;
        }
        
        // Position: blocks start at left edge of containing block (after margin)
        box.x = cb_x + box.margin.left;
        box.y = cb_y + box.margin.top;
        
        // Layout children in normal flow
        int child_y = box.y + box.border.top + box.padding.top;
        int content_area_width = box.content_width;
        int max_child_height = 0;
        
        static int call_depth = 0;
        call_depth++;
        if (call_depth < 5 && child_y > 1000) {
            std::cerr << "Depth " << call_depth << ": Starting child_y=" << child_y << std::endl;
        }
        
        LayoutBox* prev_child = nullptr;
        
        for (const auto& child_node : node.children) {
            auto child_box = computeLayout(
                *child_node,
                sheets,
                content_area_width,
                box.x + box.border.left + box.padding.left,
                child_y,
                &style
            );
            
            if (child_box.content_width == 0 && child_box.content_height == 0) {
                continue;  // Skip empty boxes
            }
            
            // Apply margin collapsing for block-level children
            if (child_box.display_type == ComputedStyle::Block && prev_child) {
                int collapse = collapseMargins(prev_child->margin.bottom, child_box.margin.top);
                child_y -= (prev_child->margin.bottom + child_box.margin.top - collapse);
                child_box.y = child_y + child_box.margin.top;
            }
            
            // Update position for next child
            if (child_box.display_type == ComputedStyle::Block) {
                child_y = child_box.y + child_box.borderBoxHeight() + child_box.margin.bottom;
            }
            
            box.children.push_back(child_box);
            prev_child = &box.children.back();
        }
        
        // Calculate height: distance from content start to last child's bottom
        // This is correct for block layout where children stack vertically
        if (!box.children.empty()) {
            int content_start_y = box.y + box.border.top + box.padding.top;
            const auto& last_child = box.children.back();
            int last_child_bottom = last_child.y + last_child.borderBoxHeight();
            max_child_height = last_child_bottom - content_start_y;
            
            // ASSERT: Sanity check on calculated height
            if (max_child_height > 100000) {
                std::cerr << "WARNING: Large height calculated!" << std::endl;
                std::cerr << "  Tag: " << (node.type == HtmlNode::Element ? node.tag : "text") << std::endl;
                std::cerr << "  Calculated height: " << max_child_height << std::endl;
                std::cerr << "  Last child height: " << last_child.borderBoxHeight() << std::endl;
                std::cerr << "  Last child content_height: " << last_child.content_height << std::endl;
                std::cerr << "  Last child y: " << last_child.y << std::endl;
                std::cerr << "  Content start y: " << content_start_y << std::endl;
                std::cerr << "  Number of children: " << box.children.size() << std::endl;
                
                if (node.type == HtmlNode::Element) {
                    auto class_it = node.attributes.find("class");
                    if (class_it != node.attributes.end()) {
                        std::cerr << "  Class: " << class_it->second.substr(0, 100) << std::endl;
                    }
                }
                std::cerr << std::endl;
                
                // assert(max_child_height <= 500000 && "Height exceeds reasonable bounds (500K pixels)");
            }
        }
        
        // Calculate height
        if (style.height.has_value()) {
            box.content_height = *style.height;
            
            // ASSERT: Check explicit heights
            // assert(*style.height <= 500000 && "Explicit CSS height exceeds 500K pixels");
        } else {
            // Auto height: distance to last child's bottom
            box.content_height = max_child_height;
        }
    }
    
    static void layoutInlineBox(
        LayoutBox& box,
        const HtmlNode& node,
        const ComputedStyle& style,
        const std::vector<CssStylesheet>& sheets,
        int containing_block_width,
        int cb_x,
        int cb_y
    ) {
        // Simplified inline layout
        // In real browser, this would handle line breaking, baseline alignment, etc.
        
        box.x = cb_x;
        box.y = cb_y;
        
        // Inline boxes shrink to content
        int total_width = 0;
        int max_height = 0;
        int current_x = box.x + box.border.left + box.padding.left;
        
        for (const auto& child_node : node.children) {
            auto child_box = computeLayout(
                *child_node,
                sheets,
                containing_block_width - total_width,
                current_x,
                box.y + box.border.top + box.padding.top,
                &style
            );
            
            if (child_box.content_width > 0 || child_box.content_height > 0) {
                total_width += child_box.marginBoxWidth();
                max_height = std::max(max_height, child_box.marginBoxHeight());
                current_x += child_box.marginBoxWidth();
                box.children.push_back(child_box);
            }
        }
        
        if (style.width.has_value()) {
            box.content_width = *style.width;
        } else {
            box.content_width = total_width;
        }
        
        if (style.height.has_value()) {
            box.content_height = *style.height;
        } else {
            box.content_height = max_height > 0 ? max_height : 20;  // Default line height
        }
    }
    
    // CSS 2.1 Section 8.3.1: Collapsing margins
    static int collapseMargins(int margin1, int margin2) {
        // Both positive: use larger
        if (margin1 >= 0 && margin2 >= 0) {
            return std::max(margin1, margin2);
        }
        // Both negative: use more negative
        if (margin1 < 0 && margin2 < 0) {
            return std::min(margin1, margin2);
        }
        // One positive, one negative: sum them
        return margin1 + margin2;
    }
    
public:
    // Flatten layout tree for rendering
    static std::vector<LayoutBox> flatten(const LayoutBox& root) {
        std::vector<LayoutBox> result;
        flattenHelper(root, result);
        return result;
    }

private:
    static void flattenHelper(const LayoutBox& box, std::vector<LayoutBox>& result) {
        LayoutBox flat_box = box;
        flat_box.children.clear();
        result.push_back(flat_box);
        
        for (const auto& child : box.children) {
            flattenHelper(child, result);
        }
    }
};

} // namespace browser_ast
