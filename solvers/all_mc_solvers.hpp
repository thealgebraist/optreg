#pragma once
#include "monte_carlo_solvers.hpp"
#include <set>

namespace optsolve {

// Graph Coloring MC
class GraphColoringMonteCarlo : public MonteCarloBase<GraphColoringProblem, GraphColoringSolution> {
public:
    GraphColoringMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    std::string name() const override { return "GraphColoring_MonteCarlo"; }
protected:
    void initialize_solution(const GraphColoringProblem& problem, GraphColoringSolution& solution) override {
        solution.colors.assign(problem.n_vertices, 0);
    }

    void propose_random_walk(const GraphColoringProblem& problem, const GraphColoringSolution& current, GraphColoringSolution& proposal) override {
        std::uniform_int_distribution<int> col_dist(0, (int)problem.n_vertices - 1);
        for (size_t i = 0; i < problem.n_vertices; ++i) {
            proposal.colors[i] = col_dist(gen);
        }
    }
    void propose_mcmc(const GraphColoringProblem& problem, const GraphColoringSolution& current, GraphColoringSolution& proposal) override {
        std::uniform_int_distribution<size_t> v_dist(0, problem.n_vertices - 1);
        std::uniform_int_distribution<int> c_dist(0, (int)problem.n_vertices - 1);
        proposal.colors[v_dist(gen)] = c_dist(gen);
    }
    double energy(const GraphColoringProblem& problem, const GraphColoringSolution& solution) override {
        int conflicts = 0;
        size_t max_color = 0;
        for (const auto& edge : problem.edges) {
            if (solution.colors[edge.first] == solution.colors[edge.second]) {
                conflicts++;
            }
        }
        for (size_t c : solution.colors) if (c > max_color) max_color = c;
        return (double)conflicts * 1000.0 + (double)max_color;
    }
};

class GraphColoringMonteCarloRW : public GraphColoringMonteCarlo {
public:
    GraphColoringMonteCarloRW(unsigned seed = 1234) : GraphColoringMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    std::string name() const override { return "GraphColoring_MonteCarloRW"; }
};

// Vertex Cover MC
class VertexCoverMonteCarlo : public MonteCarloBase<VertexCoverProblem, VertexCoverSolution> {
public:
    VertexCoverMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    std::string name() const override { return "VertexCover_MonteCarlo"; }
protected:
    void initialize_solution(const VertexCoverProblem& problem, VertexCoverSolution& solution) override {
        solution.in_cover.assign(problem.n_vertices, false);
    }

    void propose_random_walk(const VertexCoverProblem& problem, const VertexCoverSolution& current, VertexCoverSolution& proposal) override {
        std::uniform_int_distribution<int> bin(0, 1);
        for (size_t i = 0; i < problem.n_vertices; ++i) {
            proposal.in_cover[i] = bin(gen);
        }
    }
    void propose_mcmc(const VertexCoverProblem& problem, const VertexCoverSolution& current, VertexCoverSolution& proposal) override {
        std::uniform_int_distribution<size_t> v_dist(0, problem.n_vertices - 1);
        size_t v = v_dist(gen);
        proposal.in_cover[v] = !proposal.in_cover[v];
    }
    double energy(const VertexCoverProblem& problem, const VertexCoverSolution& solution) override {
        int uncovered = 0;
        int count = 0;
        for (const auto& edge : problem.edges) {
            if (!solution.in_cover[edge.first] && !solution.in_cover[edge.second]) {
                uncovered++;
            }
        }
        for (bool b : solution.in_cover) if (b) count++;
        return (double)uncovered * 1000.0 + (double)count;
    }
};

class VertexCoverMonteCarloRW : public VertexCoverMonteCarlo {
public:
    VertexCoverMonteCarloRW(unsigned seed = 1234) : VertexCoverMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    std::string name() const override { return "VertexCover_MonteCarloRW"; }
};

// Clique MC
class CliqueMonteCarlo : public MonteCarloBase<CliqueProblem, CliqueSolution> {
public:
    CliqueMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    std::string name() const override { return "Clique_MonteCarlo"; }
protected:
    void initialize_solution(const CliqueProblem& problem, CliqueSolution& solution) override {
        solution.vertices.clear();
    }

    void propose_random_walk(const CliqueProblem& problem, const CliqueSolution& current, CliqueSolution& proposal) override {
        std::uniform_int_distribution<int> bin(0, 1);
        proposal.vertices.clear();
        for (size_t i = 0; i < problem.n_vertices; ++i) {
            if (bin(gen)) proposal.vertices.push_back(i);
        }
    }
    void propose_mcmc(const CliqueProblem& problem, const CliqueSolution& current, CliqueSolution& proposal) override {
        std::uniform_int_distribution<size_t> v_dist(0, problem.n_vertices - 1);
        size_t v = v_dist(gen);
        auto it = std::find(proposal.vertices.begin(), proposal.vertices.end(), v);
        if (it == proposal.vertices.end()) proposal.vertices.push_back(v);
        else proposal.vertices.erase(it);
    }
    double energy(const CliqueProblem& problem, const CliqueSolution& solution) override {
        std::set<std::pair<size_t, size_t>> edge_set;
        for (const auto& edge : problem.edges) edge_set.emplace(std::min(edge.first, edge.second), std::max(edge.first, edge.second));
        
        int non_edges = 0;
        for (size_t i = 0; i < solution.vertices.size(); ++i) {
            for (size_t j = i + 1; j < solution.vertices.size(); ++j) {
                size_t u = solution.vertices[i], v = solution.vertices[j];
                if (!edge_set.count({std::min(u, v), std::max(u, v)})) non_edges++;
            }
        }
        return (double)non_edges * 1000.0 - (double)solution.vertices.size();
    }

    bool solve_impl(const CliqueProblem& problem, CliqueSolution& solution, SolverMetrics& metrics) override {
        bool res = MonteCarloBase<CliqueProblem, CliqueSolution>::solve_impl(problem, solution, metrics);
        metrics.objective_value = -metrics.objective_value;
        return res;
    }
};

class CliqueMonteCarloRW : public CliqueMonteCarlo {
public:
    CliqueMonteCarloRW(unsigned seed = 1234) : CliqueMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    std::string name() const override { return "Clique_MonteCarloRW"; }
};

// Hamiltonian MC
class HamiltonianMonteCarlo : public MonteCarloBase<HamiltonianProblem, HamiltonianSolution> {
public:
    HamiltonianMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    std::string name() const override { return "Hamiltonian_MonteCarlo"; }
protected:
    void initialize_solution(const HamiltonianProblem& problem, HamiltonianSolution& solution) override {
        solution.cycle.resize(problem.n_vertices);
    }

    void propose_random_walk(const HamiltonianProblem& problem, const HamiltonianSolution& current, HamiltonianSolution& proposal) override {
        std::iota(proposal.cycle.begin(), proposal.cycle.end(), 0);
        std::shuffle(proposal.cycle.begin(), proposal.cycle.end(), gen);
        proposal.exists = true;
    }
    void propose_mcmc(const HamiltonianProblem& problem, const HamiltonianSolution& current, HamiltonianSolution& proposal) override {
        std::uniform_int_distribution<size_t> v_dist(0, problem.n_vertices - 1);
        size_t i = v_dist(gen);
        size_t j = v_dist(gen);
        std::swap(proposal.cycle[i], proposal.cycle[j]);
        proposal.exists = true;
    }
    double energy(const HamiltonianProblem& problem, const HamiltonianSolution& solution) override {
        std::set<std::pair<size_t, size_t>> edge_set;
        for (const auto& edge : problem.edges) edge_set.emplace(std::min(edge.first, edge.second), std::max(edge.first, edge.second));
        
        int invalid_edges = 0;
        if (solution.cycle.empty()) return (double)problem.n_vertices;
        for (size_t i = 0; i < solution.cycle.size(); ++i) {
            size_t u = solution.cycle[i];
            size_t v = solution.cycle[(i + 1) % solution.cycle.size()];
            if (!edge_set.count({std::min(u, v), std::max(u, v)})) invalid_edges++;
        }
        return (double)invalid_edges;
    }
};

class HamiltonianMonteCarloRW : public HamiltonianMonteCarlo {
public:
    HamiltonianMonteCarloRW(unsigned seed = 1234) : HamiltonianMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    std::string name() const override { return "Hamiltonian_MonteCarloRW"; }
};

// Set Cover MC
class SetCoverMonteCarlo : public MonteCarloBase<SetCoverProblem, SetCoverSolution> {
public:
    SetCoverMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    std::string name() const override { return "SetCover_MonteCarlo"; }
protected:
    void initialize_solution(const SetCoverProblem& problem, SetCoverSolution& solution) override {
        solution.selected_sets.assign(problem.n_sets, false);
    }

    void propose_random_walk(const SetCoverProblem& problem, const SetCoverSolution& current, SetCoverSolution& proposal) override {
        std::uniform_int_distribution<int> bin(0, 1);
        for (size_t i = 0; i < problem.n_sets; ++i) proposal.selected_sets[i] = bin(gen);
    }
    void propose_mcmc(const SetCoverProblem& problem, const SetCoverSolution& current, SetCoverSolution& proposal) override {
        std::uniform_int_distribution<size_t> s_dist(0, problem.n_sets - 1);
        size_t s = s_dist(gen);
        proposal.selected_sets[s] = !proposal.selected_sets[s];
    }
    double energy(const SetCoverProblem& problem, const SetCoverSolution& solution) override {
        std::vector<bool> covered(problem.n_elements, false);
        for (size_t i = 0; i < problem.n_sets; ++i) {
            if (solution.selected_sets[i]) {
                for (size_t e : problem.sets[i]) covered[e] = true;
            }
        }
        int uncovered = 0;
        for (bool b : covered) if (!b) uncovered++;
        int count = 0;
        for (bool b : solution.selected_sets) if (b) count++;
        return (double)uncovered * 1000.0 + (double)count;
    }
};

class SetCoverMonteCarloRW : public SetCoverMonteCarlo {
public:
    SetCoverMonteCarloRW(unsigned seed = 1234) : SetCoverMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    std::string name() const override { return "SetCover_MonteCarloRW"; }
};

// Subset Sum MC
class SubsetSumMonteCarlo : public MonteCarloBase<SubsetSumProblem, SubsetSumSolution> {
public:
    SubsetSumMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    std::string name() const override { return "SubsetSum_MonteCarlo"; }
protected:
    void initialize_solution(const SubsetSumProblem& problem, SubsetSumSolution& solution) override {
        solution.selected.assign(problem.numbers.size(), false);
    }

    void propose_random_walk(const SubsetSumProblem& problem, const SubsetSumSolution& current, SubsetSumSolution& proposal) override {
        std::uniform_int_distribution<int> bin(0, 1);
        long long sum = 0;
        for (size_t i = 0; i < problem.numbers.size(); ++i) {
            proposal.selected[i] = bin(gen);
            if (proposal.selected[i]) sum += problem.numbers[i];
        }
        proposal.exists = (sum == (long long)problem.target);
    }
    void propose_mcmc(const SubsetSumProblem& problem, const SubsetSumSolution& current, SubsetSumSolution& proposal) override {
        std::uniform_int_distribution<size_t> i_dist(0, problem.numbers.size() - 1);
        size_t i = i_dist(gen);
        proposal.selected[i] = !proposal.selected[i];
        
        long long sum = 0;
        for (size_t j = 0; j < proposal.selected.size(); ++j) {
            if (proposal.selected[j]) sum += problem.numbers[j];
        }
        proposal.exists = (sum == (long long)problem.target);
    }
    double energy(const SubsetSumProblem& problem, const SubsetSumSolution& solution) override {
        long long sum = 0;
        for (size_t i = 0; i < problem.numbers.size(); ++i) if (solution.selected[i]) sum += problem.numbers[i];
        return (double)std::abs(sum - (long long)problem.target);
    }
};

class SubsetSumMonteCarloRW : public SubsetSumMonteCarlo {
public:
    SubsetSumMonteCarloRW(unsigned seed = 1234) : SubsetSumMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    std::string name() const override { return "SubsetSum_MonteCarloRW"; }
};

// Steiner Tree MC
class SteinerMonteCarlo : public MonteCarloBase<SteinerTreeProblem, SteinerTreeSolution> {
public:
    SteinerMonteCarlo(unsigned seed = 1234) : MonteCarloBase(seed) {
        config.random_walk_prob = 0.0;
    }
    std::string name() const override { return "Steiner_MonteCarlo"; }
protected:
    void initialize_solution(const SteinerTreeProblem& problem, SteinerTreeSolution& solution) override {
        solution.tree_edges.clear();
    }

    void propose_random_walk(const SteinerTreeProblem& problem, const SteinerTreeSolution& current, SteinerTreeSolution& proposal) override {
        std::uniform_int_distribution<int> bin(0, 1);
        proposal.tree_edges.clear();
        for (const auto& edge : problem.edges) {
            if (bin(gen)) proposal.tree_edges.push_back(edge);
        }
    }
    void propose_mcmc(const SteinerTreeProblem& problem, const SteinerTreeSolution& current, SteinerTreeSolution& proposal) override {
        std::uniform_int_distribution<size_t> e_dist(0, problem.edges.size() - 1);
        auto edge = problem.edges[e_dist(gen)];
        auto it = std::find(proposal.tree_edges.begin(), proposal.tree_edges.end(), edge);
        if (it == proposal.tree_edges.end()) proposal.tree_edges.push_back(edge);
        else proposal.tree_edges.erase(it);
    }
    double energy(const SteinerTreeProblem& problem, const SteinerTreeSolution& solution) override {
        if (solution.is_valid(problem)) {
            double weight = 0;
            for (const auto& [u, v, w] : solution.tree_edges) weight += w;
            return weight;
        }
        return 1e9;
    }
};

class SteinerMonteCarloRW : public SteinerMonteCarlo {
public:
    SteinerMonteCarloRW(unsigned seed = 1234) : SteinerMonteCarlo(seed) {
        config.random_walk_prob = 0.3;
    }
    std::string name() const override { return "Steiner_MonteCarloRW"; }
};

} // namespace optsolve
