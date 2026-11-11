#include "ARCSCSSolver.h"
#include "CapacitySearch.h"
#include <stdexcept>

ARCSCSSolver::ARCSCSSolver(Graph &graph, const ARCSCSConfig &config)
    : graph_(graph), config_(config)
{
    graph_.set_concise_log(config_.concise_log);
}

SearchResult ARCSCSSolver::solve_arc_scs(int query_vertex,
    int size_lower_bound, int size_upper_bound, int &k_min, int &k_max)
{
    if (query_vertex < 0 || size_lower_bound <= 0 || size_upper_bound < size_lower_bound)
        throw std::invalid_argument("invalid ARC-SCS query bounds or vertex");
    const Query query(query_vertex, size_lower_bound, size_upper_bound);
    CapacitySearch::solve(graph_, query, config_, k_min, k_max);
    return graph_.get_last_query_result();
}
