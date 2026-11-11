#include "CapacitySearch.h"
#include "Graph.h"

void CapacitySearch::solve(Graph &graph, const Query &query, const ARCSCSConfig &config, int &k_min, int &k_max)
{
	graph.ARC_SCS(query, k_min, k_max, config);
}
