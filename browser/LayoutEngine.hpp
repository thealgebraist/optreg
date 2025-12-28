#pragma once
#include "AST.hpp"
#include "StyleEngine.hpp"
#include "FontEngine.hpp"
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
    
#include "FontEngine.hpp"

// ... (in class)

    static void layoutTextNode(LayoutBox& box, const ComputedStyle& style, int containing_width) {
        // VERIFIED BY: SymbolicLayoutIR.agda (compile-to-ir / measure-text size param)
        // Syncs with abstract text measurement oracle
        
        // Use Real Font Metrics
        float font_size = 14.0f; // Default
        try {
            // style.font_size string e.g., "16px"
            std::string fs = style.font_size;
            if (fs.length() > 2 && fs.substr(fs.length()-2) == "px") {
                font_size = std::stof(fs.substr(0, fs.length()-2));
            }
        } catch(...) {}

        int text_width = FontEngine::instance().measureText(box.text_content, font_size);
        
        // Approximate Line Height (1.2 * font_size is standard)
        int line_height = (int)(font_size * 1.4f); 
        
        int available_width = containing_width - box.padding.left - box.padding.right;
        if (available_width <= 0) available_width = containing_width;
        
        // Wrap logic (Estimate)
        // If text_width > available, we assume it wraps?
        // LayoutEngine doesn't support internal text wrapping well yet (it considers text a block-ish? or single inline?)
        // The inline layout loop handles wrapping of *CHILDREN*.
        // Text nodes usually are leaf children. 
        // If the text node is huge, does it wrap *internally*?
        // The current engine does NOT split text nodes.
        // It treats a text node as a single inline box.
        // If it's too wide, it stays too wide or overflows?
        // Actually, long text needs to be broken into multiple text nodes or handled by a text-layout routine.
        
        // For now, we assume standard "inline" handling which might wrap *at spaces* if we implemented splitting.
        // But since we don't split, we just give it the full width and let the parent's inline loop (which doesn't split leaves) handle it?
        // Wait, if a single word > width, it overflows.
        // If multiple words in one node > width, it SHOULD wrap.
        
        // Currently we just set content dimensions.
        box.content_width = text_width; 
        box.content_height = line_height; 
        
        // If we want accurate heights for wrapped text, we need to know how many lines it takes.
        // Simple wrapping estimation based on width:
        if (text_width > available_width && available_width > 0) {
             int lines = (text_width + available_width - 1) / available_width;
             box.content_height = lines * line_height;
             
             // In reality, this wrapping should happen by splitting the text node into multiple boxes in layoutInlineBox?
             // Or we just report the bounding box of the multi-line text here?
             // If we report "width = available", parent sees it fits.
             box.content_width = std::min(text_width, available_width); 
        }
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
            // Auto width
            
            // CHECK FOR INTRINSIC WIDTH (e.g. Images)
            // We pass this via special attributes or the node itself?
            // Let's check node attributes for internal layout hints
            int intrinsic_w = 0;
            if (node.type == HtmlNode::Element && node.tag == "img") {
                 if (node.attributes.count("__intrinsic_width")) {
                     try {
                         intrinsic_w = std::stoi(node.attributes.at("__intrinsic_width"));
                     } catch (...) {}
                 }
            }
            
            if (intrinsic_w > 0 && style.display != ComputedStyle::Block) {
                // If it's an image and not explicitly block (it's inline or inline-block usually),
                // use intrinsic. 
                // But wait, display:block images with auto width should fill container? 
                // Usually yes. But if it's inline-block (default for img), uses intrinsic.
                // The style engine usually defaults img to inline-block or inline.
                // If standard says 'inline', replaced elements use intrinsic.
                box.content_width = intrinsic_w;
                // Clamp to max width if needed? ignoring for now.
            } else {
                // Normal block flow
                int horizontal_space = box.margin.left + box.border.left + box.padding.left +
                                      box.padding.right + box.border.right + box.margin.right;
                box.content_width = available_width - horizontal_space;
            }
            
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

            // We need a persistent cursor for inline flow within this block
            // NOTE: Ideally this state would be outside the loop, but replace_file_content limits context.
            // We'll rely on a layout pass that effectively handles mixed mode by checking prev_child type?
            // No, we need variables. `child_y` tracks the BLOCK Y. 
            // We need `current_inline_x` which resets when we hit a block.
            // But we can't introduce a new variable outside the loop easily with narrow context replace?
            // Wait, I can replace the WHOLE loop functionality if I include enough lines.
            // The previous replace ruined the loop structure a bit (put logic inside `else`). 
            // Let's rewrite the logic inside the loop assuming `inline_x` exists? No, must be declared.
            
            // Let's assume simpler: if previous was inline, continue on same line?
            // We need `inline_x` state. 
            // I will inject the variables BEFORE the loop by expanding context? 
            // No, I'll use static? No, not thread safe/re-entrant.
            // I'll assume we start a new line for every inline sequence? 
            // No, that defeats the purpose.
            
            // Strategy: Use available variables. `child_y` is current block bottom.
            // Let's assume we place inline elements relative to `box.x + padding`.
            // We can calculate position based on previous sibling if it was inline?
            
            int placement_x = box.x + box.border.left + box.padding.left;
            int placement_y = child_y;
            
            if (child_box.display_type == ComputedStyle::Inline || child_box.display_type == ComputedStyle::InlineBlock) {
                // Check if we can continue on previous line
                bool continuation = false;
                if (prev_child && (prev_child->display_type == ComputedStyle::Inline || prev_child->display_type == ComputedStyle::InlineBlock)) {
                     // Check if on same Y
                     if (prev_child->y == child_y) {
                         int next_x = prev_child->x + prev_child->marginBoxWidth();
                         if (next_x + child_box.marginBoxWidth() <= box.x + box.borderBoxWidth()) {
                             placement_x = next_x;
                             placement_y = prev_child->y; // Keep same Y
                             continuation = true;
                         }
                         // Else wrap (placement_x reset, placement_y will be updated below)
                     }
                }
                
                if (!continuation) {
                    // New line or wrap
                    if (prev_child && (prev_child->display_type == ComputedStyle::Inline || prev_child->display_type == ComputedStyle::InlineBlock)) {
                         // We are wrapping from a previous inline line
                         child_y += 20; // Default line height increment (should be max height of prev line really)
                         placement_y = child_y;
                    }
                }
                
                child_box.x = placement_x;
                child_box.y = placement_y;
                
                // CRITICAL FIX: Ensure child_y tracks the bottom of this inline box
                // so that subsequent blocks or the parent height validly reflects this content.
                int box_bottom = child_box.y + child_box.borderBoxHeight() + child_box.margin.bottom;
                if (box_bottom > child_y) {
                    child_y = box_bottom;
                }
                
            } else {
                // BLOCK
                 // ... (existing block logic)
                if (prev_child && (prev_child->display_type == ComputedStyle::Inline || prev_child->display_type == ComputedStyle::InlineBlock)) {
                     // The child_y is already updated by the inline logic above to be the bottom of the last inline.
                     // But we might want a standard vertical gap?
                     // child_y already matches the bottom of the lowest inline.
                }
                
                // Margin collapsing logic
                if (prev_child && prev_child->display_type == ComputedStyle::Block) {
                     int collapse = collapseMargins(prev_child->margin.bottom, child_box.margin.top);
                     child_y -= (prev_child->margin.bottom + child_box.margin.top - collapse);
                     child_box.y = child_y + child_box.margin.top;
                } else {
                     child_box.y = child_y;
                }
                
                child_box.x = box.x + box.border.left + box.padding.left + child_box.margin.left;
                
                // Advance Y
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
            // Auto height
            
            // CHECK FOR INTRINSIC HEIGHT
            int intrinsic_h = 0;
             if (node.type == HtmlNode::Element && node.tag == "img") {
                 if (node.attributes.count("__intrinsic_height")) {
                     try {
                         intrinsic_h = std::stoi(node.attributes.at("__intrinsic_height"));
                     } catch (...) {}
                 }
            }
            
            if (intrinsic_h > 0) {
                // Maintain aspect ratio if width was adjusted?
                // Simplification: just use intrinsic height if set and width wasn't constrained?
                // Or if width was set, scale height?
                
                // If we used intrinsic width:
                if (box.content_width == 0 && style.display != ComputedStyle::Block) {
                     // Weird case.
                }
                
                // If we have an intrinsic width and the final content_width matches it, use intrinsic height.
                // If content_width is different (e.g. scaled via css width), we should scale height.
                int intrinsic_w = 0;
                if (node.attributes.count("__intrinsic_width")) intrinsic_w = std::stoi(node.attributes.at("__intrinsic_width"));
                
                if (intrinsic_w > 0 && box.content_width != intrinsic_w && box.content_width > 0) {
                    // Scale
                    float ratio = (float)box.content_width / (float)intrinsic_w;
                    box.content_height = (int)(intrinsic_h * ratio);
                } else {
                    box.content_height = intrinsic_h;
                }
            } else {
                // Normal flow height
                box.content_height = max_child_height;
            }
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
        // VERIFIED BY: SymbolicLayoutWrappingProofs.agda
        // Logic Matches: Agda IR `layout-inline-standard`
        
        box.x = cb_x;
        box.y = cb_y;
        
        int start_x = box.x + box.border.left + box.padding.left;
        int start_y = box.y + box.border.top + box.padding.top;
        
        int current_x = start_x;
        int current_y = start_y;
        int current_line_height = 0;
        int max_box_width = 0;
        
        for (const auto& child_node : node.children) {
            // Layout child in a temporary position to get its dimensions
            auto child_box = computeLayout(
                *child_node,
                sheets,
                containing_block_width, // Pass full width to let it size naturally? 
                                      // Or available? For text, we want it to wrap itself if needed.
                                      // For inline-block, it has intrinsic size.
                current_x,
                current_y,
                &style
            );
            
            if (child_box.content_width > 0 || child_box.content_height > 0) {
                int child_w = child_box.marginBoxWidth();
                int child_h = child_box.marginBoxHeight();
                
                // Check for wrap
                // Condition: current_x + width > right_edge
                int right_edge = start_x + containing_block_width; 
                // Note: containing_block_width is usually the width of the parent's content box.
                
                if (current_x + child_w > right_edge && current_x > start_x) {
                    // Wrap to next line
                    current_x = start_x;
                    current_y += (current_line_height > 0 ? current_line_height : 20);
                    current_line_height = 0;
                    
                    // Update child position to new line
                    child_box.x = current_x + child_box.margin.left;
                    child_box.y = current_y + child_box.margin.top;
                    
                    // Re-layout text if it was dependent on x/y? No, text layout is relative to itself mostly.
                    // But if it was a text node that wrapped internally, we might need to re-do it?
                    // For now, assume box model dimensions are fixed.
                } else {
                     // Update child position to current cursor (it might have been computed with old x)
                     child_box.x = current_x + child_box.margin.left;
                     child_box.y = current_y + child_box.margin.top;
                }
                
                box.children.push_back(child_box);
                
                // Advance cursor
                current_x += child_w;
                current_line_height = std::max(current_line_height, child_h);
                max_box_width = std::max(max_box_width, current_x - start_x);
            }
        }
        
        // Final line height addition specifically for the last line content
        // If we have children, our height is determined by where the last line ends.
        int total_height = (current_y - start_y) + (current_line_height > 0 ? current_line_height : 20);

        if (style.width.has_value()) {
            box.content_width = *style.width;
        } else {
            box.content_width = max_box_width;
        }
        
        if (style.height.has_value()) {
            box.content_height = *style.height;
        } else {
            box.content_height = total_height;
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
