#pragma once
#include "LayoutEngine.hpp"
#include <SDL2/SDL.h>
#include <iostream>
#include <algorithm>

namespace browser_ast {

class Renderer {
public:
    Renderer() : window(nullptr), renderer(nullptr), running(false) {}
    
    ~Renderer() {
        cleanup();
    }
    
    bool init(int width, int height, const std::string& title = "MiniChrome Browser") {
        if (SDL_Init(SDL_INIT_VIDEO) < 0) {
            std::cerr << "SDL initialization failed: " << SDL_GetError() << std::endl;
            return false;
        }
        
        window = SDL_CreateWindow(
            title.c_str(),
            SDL_WINDOWPOS_CENTERED,
            SDL_WINDOWPOS_CENTERED,
            width, height,
            SDL_WINDOW_SHOWN | SDL_WINDOW_RESIZABLE
        );
        
        if (!window) {
            std::cerr << "Window creation failed: " << SDL_GetError() << std::endl;
            return false;
        }
        
        renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED);
        if (!renderer) {
            std::cerr << "Renderer creation failed: " << SDL_GetError() << std::endl;
            return false;
        }
        
        viewport_width = width;
        viewport_height = height;
        scroll_y = 0;
        
        return true;
    }
    
    void render(const LayoutBox& root) {
        current_layout = root;
        renderFrame();
    }
    
    void handleEvents() {
        running = true;
        
        while (running) {
            SDL_Event event;
            while (SDL_PollEvent(&event)) {
                handleEvent(event);
            }
            
            renderFrame();
            SDL_Delay(16);  // ~60 FPS
        }
    }

private:
    SDL_Window* window;
    SDL_Renderer* renderer;
    bool running;
    
    LayoutBox current_layout;
    int viewport_width;
    int viewport_height;
    int scroll_y;
    
    void cleanup() {
        if (renderer) {
            SDL_DestroyRenderer(renderer);
            renderer = nullptr;
        }
        if (window) {
            SDL_DestroyWindow(window);
            window = nullptr;
        }
        SDL_Quit();
    }
    
    void handleEvent(const SDL_Event& event) {
        switch (event.type) {
            case SDL_QUIT:
                running = false;
                break;
                
            case SDL_KEYDOWN:
                if (event.key.keysym.sym == SDLK_ESCAPE || event.key.keysym.sym == SDLK_q) {
                    running = false;
                }
                break;
                
            case SDL_MOUSEWHEEL:
                // Scroll handling
                scroll_y -= event.wheel.y * 20;
                scroll_y = std::max(0, scroll_y);
                break;
                
            case SDL_WINDOWEVENT:
                if (event.window.event == SDL_WINDOWEVENT_RESIZED) {
                    viewport_width = event.window.data1;
                    viewport_height = event.window.data2;
                }
                break;
        }
    }
    
    void renderFrame() {
        // Clear background
        SDL_SetRenderDrawColor(renderer, 255, 255, 255, 255);
        SDL_RenderClear(renderer);
        
        // Render layout boxes
        renderBox(current_layout, scroll_y);
        
        // Present
        SDL_RenderPresent(renderer);
    }
    
    void renderBox(const LayoutBox& box, int scroll_offset) {
        // Adjust y position for scrolling
        int render_y = box.y - scroll_offset;
        
        // Viewport culling
        int box_height = box.borderBoxHeight();
        if (render_y + box_height < 0 || render_y > viewport_height) {
            return;  // Box is outside viewport
        }
        
        // Draw background (content + padding area)
        if (box.bg_r != 255 || box.bg_g != 255 || box.bg_b != 255) {
            SDL_Rect rect = {
                box.x + box.border.left,
                render_y + box.border.top,
                box.content_width + box.padding.left + box.padding.right,
                box.content_height + box.padding.top + box.padding.bottom
            };
            
            SDL_SetRenderDrawColor(renderer, box.bg_r, box.bg_g, box.bg_b, 255);
            SDL_RenderFillRect(renderer, &rect);
        }
        
        // Draw border
        if (box.border.top > 0 || box.border.right > 0 || 
            box.border.bottom > 0 || box.border.left > 0) {
            SDL_Rect border_rect = {
                box.x,
                render_y,
                box.borderBoxWidth(),
                box.borderBoxHeight()
            };
            
            SDL_SetRenderDrawColor(renderer, 0, 0, 0, 255);
            SDL_RenderDrawRect(renderer, &border_rect);
        }
        
        // Draw text content as a colored box
        if (!box.text_content.empty()) {
            SDL_Rect text_rect = {
                box.x + box.border.left + box.padding.left,
                render_y + box.border.top + box.padding.top,
                std::min(box.content_width, 
                        (int)box.text_content.length() * 8),
                box.content_height
            };
            
            // Use a light gray to indicate text
            SDL_SetRenderDrawColor(renderer, 200, 200, 200, 255);
            SDL_RenderFillRect(renderer, &text_rect);
            
            // Draw outline
            SDL_SetRenderDrawColor(renderer, 100, 100, 100, 255);
            SDL_RenderDrawRect(renderer, &text_rect);
        }
        
        // Render children
        for (const auto& child : box.children) {
            renderBox(child, scroll_offset);
        }
    }
};

} // namespace browser_ast
