CXX = clang++
CXXFLAGS = -std=c++23 -Wall -Wextra -O3 -march=native -DACCELERATE_NEW_LAPACK
INCLUDES = -Iinclude -I/opt/homebrew/include/eigen3
LDFLAGS = -lm -framework Accelerate

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
SRCS += $(SRC_DIR)/global_allocator.cpp
SRCS += $(SRC_DIR)/gradient_descent.cpp
SRCS += $(SRC_DIR)/branch_bound.cpp
SRCS += $(SRC_DIR)/accelerate_solver.cpp
SRCS += $(SRC_DIR)/eigen_solver.cpp
SRCS += $(SRC_DIR)/metaheuristics.cpp
SRCS += $(SRC_DIR)/tsplib_parser.cpp
SRCS += $(SRC_DIR)/tsp_solver.cpp

# Accelerate framework for AMX
# LDFLAGS += -framework Accelerate

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
		$(BUILD_DIR)/global_allocator.o \
		$(BUILD_DIR)/gradient_descent.o \
		-o benchmark $(LDFLAGS)
	@echo "Running 256 random register allocation tests..."
	@./benchmark

# Merge sort comparison test
test_mergesort: $(BUILD_DIR) tests/test_mergesort.cpp $(BUILD_DIR)/global_allocator.o
	@echo "Building merge sort test..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/test_mergesort.cpp \
		$(BUILD_DIR)/ir_parser.o \
		$(BUILD_DIR)/live_range.o \
		$(BUILD_DIR)/interference_graph.o \
		$(BUILD_DIR)/interior_point.o \
		$(BUILD_DIR)/graph_coloring.o \
		$(BUILD_DIR)/global_allocator.o \
		-o test_mergesort $(LDFLAGS)
	@echo "Running merge sort allocation comparison..."
	@./test_mergesort

# Spill heavy test
test_spills: $(BUILD_DIR) tests/test_spills.cpp
	@echo "Building spill heavy test..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/test_spills.cpp \
		$(BUILD_DIR)/ir_parser.o \
		$(BUILD_DIR)/live_range.o \
		$(BUILD_DIR)/interference_graph.o \
		$(BUILD_DIR)/interior_point.o \
		$(BUILD_DIR)/graph_coloring.o \
		$(BUILD_DIR)/global_allocator.o \
		-o test_spills $(LDFLAGS)
	@echo "Running spill heavy test..."
	@./test_spills

# Sanity test suites
.PHONY: sanity_eigen sanity_amx
sanity_eigen: $(BUILD_DIR) tests/sanity_eigen.cpp
	@echo "Building Eigen sanity test suite..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/sanity_eigen.cpp \
		$(BUILD_DIR)/ir_parser.o \
		$(BUILD_DIR)/live_range.o \
		$(BUILD_DIR)/interference_graph.o \
		$(BUILD_DIR)/interior_point.o \
		$(BUILD_DIR)/graph_coloring.o \
		$(BUILD_DIR)/global_allocator.o \
		$(BUILD_DIR)/gradient_descent.o \
		$(BUILD_DIR)/branch_bound.o \
		$(BUILD_DIR)/accelerate_solver.o \
		$(BUILD_DIR)/eigen_solver.o \
		-o sanity_eigen $(LDFLAGS)
	@echo "Running Eigen sanity tests..."
	@./sanity_eigen

sanity_amx: $(BUILD_DIR) tests/sanity_amx.cpp $(BUILD_DIR)/accelerate_solver.o
	@echo "Building AMX sanity test suite..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/sanity_amx.cpp \
		$(BUILD_DIR)/accelerate_solver.o \
		-o sanity_amx $(LDFLAGS)
	@echo "Running AMX sanity tests..."
	@./sanity_amx

repro_amx_crash: $(BUILD_DIR) tests/repro_amx_crash.cpp $(BUILD_DIR)/accelerate_solver.o
	@echo "Building AMX crash repro..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/repro_amx_crash.cpp \
		$(BUILD_DIR)/accelerate_solver.o \
		-o repro_amx_crash $(LDFLAGS)

repro_amx_asan: $(BUILD_DIR) tests/repro_amx_crash.cpp
	@echo "Building AMX crash repro with ASAN..."
	$(CXX) $(CXXFLAGS) -fsanitize=address -g $(INCLUDES) tests/repro_amx_crash.cpp \
		src/accelerate_solver.cpp \
		-o repro_amx_asan $(LDFLAGS)
	@echo "Running repro with ASAN..."
	@./repro_amx_asan

benchmark_backends: $(BUILD_DIR) tests/benchmark_backends.cpp $(OBJS)
	@echo "Building backend comparison benchmark..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/benchmark_backends.cpp $(filter-out build/main.o, $(OBJS)) -o benchmark_backends $(LDFLAGS)
	@echo "Running backend comparison benchmark..."
	@./benchmark_backends

benchmark_amx_scale: $(BUILD_DIR) tests/benchmark_amx_scale.cpp $(OBJS)
	@echo "Building AMX scaling benchmark..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/benchmark_amx_scale.cpp $(filter-out build/main.o, $(OBJS)) -o benchmark_amx_scale $(LDFLAGS)
	@echo "Running AMX scaling benchmark..."
	@./benchmark_amx_scale

benchmark_clique: $(BUILD_DIR) tests/benchmark_clique.cpp $(OBJS)
	@echo "Building clique benchmark..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/benchmark_clique.cpp $(filter-out build/main.o, $(OBJS)) -o benchmark_clique $(LDFLAGS)
	@echo "Running clique benchmark..."
	@./benchmark_clique

benchmark_tsplib: $(BUILD_DIR) tests/benchmark_tsplib.cpp $(OBJS)
	@echo "Building TSPLIB benchmark..."
	$(CXX) $(CXXFLAGS) $(INCLUDES) tests/benchmark_tsplib.cpp $(filter-out build/main.o, $(OBJS)) -o benchmark_tsplib $(LDFLAGS)
	@echo "Running TSPLIB benchmark..."
	@./benchmark_tsplib
