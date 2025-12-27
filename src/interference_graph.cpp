#include "interference_graph.h"

namespace optreg {

InterferenceGraph build_interference_graph(
    const LivenessInfo& liveness,
    const ControlFlowGraph& cfg
) {
    InterferenceGraph graph;
    graph.num_variables = cfg.variables.size();
    
    // Build edges: variables interfere if their live ranges overlap
    for (size_t i = 0; i < liveness.ranges.size(); ++i) {
        for (size_t j = i + 1; j < liveness.ranges.size(); ++j) {
            if (ranges_interfere(liveness.ranges[i], liveness.ranges[j])) {
                uint32_t v1 = liveness.ranges[i].var_id;
                uint32_t v2 = liveness.ranges[j].var_id;
                
                graph.edges[v1].insert(v2);
                graph.edges[v2].insert(v1);
                
                graph.degree[v1]++;
                graph.degree[v2]++;
            }
        }
    }
    
    return graph;
}

bool variables_interfere(
    const InterferenceGraph& graph,
    uint32_t v1,
    uint32_t v2
) {
    auto it = graph.edges.find(v1);
    if (it == graph.edges.end()) return false;
    return it->second.count(v2) > 0;
}

const std::unordered_set<uint32_t>& get_neighbors(
    const InterferenceGraph& graph,
    uint32_t var
) {
    static std::unordered_set<uint32_t> empty;
    auto it = graph.edges.find(var);
    return (it != graph.edges.end()) ? it->second : empty;
}

} // namespace optreg
