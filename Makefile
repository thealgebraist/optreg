CXX = g++
CXXFLAGS = -std=c++23 -Wall -Wextra -O3 -march=native
INCLUDES = -Iinclude -I/opt/homebrew/include/eigen3
LDFLAGS = -lm

SRC_DIR = src
INC_DIR = include
TEST_DIR = tests
BUILD_DIR = build

# Source files (only those implemented)
SRCS = 

# Task 1-4: Foundation (COMPLETE - no external deps)
SRCS += $(SRC_DIR)/ir_parser.cpp
SRCS += $(SRC_DIR)/live_range.cpp
SRCS += $(SRC_DIR)/interference_graph.cpp

# Main driver (foundation only for now)
SRCS += $(SRC_DIR)/main.cpp

# LP solver enabled (Eigen installed, implementation in headers)
SRCS += $(SRC_DIR)/interior_point.cpp
SRCS += $(SRC_DIR)/graph_coloring.cpp

OBJS = $(SRCS:$(SRC_DIR)/%.cpp=$(BUILD_DIR)/%.o)
TARGET = optreg

.PHONY: all clean test

all: $(BUILD_DIR) $(TARGET)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(TARGET): $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $^ $(LDFLAGS)

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

test: $(TARGET)
	./$(TARGET) --test

clean:
	rm -rf $(BUILD_DIR) $(TARGET) benchmark

# Individual tasks (for incremental development)
.PHONY: task1 task2 task3 task4 mediumrandom

task1: $(BUILD_DIR)/ir_parser.o
task2: $(BUILD_DIR)/live_range.o  
task3: $(BUILD_DIR)/interference_graph.o
task4: task1 task2 task3

# Medium random benchmark: 256 tests comparing heuristic vs optimal
mediumrandom: $(BUILD_DIR) tests/benchmark.cpp
	@echo "Building benchmark..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/benchmark.cpp \
		$(BUILD_DIR)/ir_parser.o \
		$(BUILD_DIR)/live_range.o \
		$(BUILD_DIR)/interference_graph.o \
		$(BUILD_DIR)/interior_point.o \
		$(BUILD_DIR)/graph_coloring.o \
		-o benchmark $(LDFLAGS)
	@echo "Running 256 random register allocation tests..."
	@./benchmark
