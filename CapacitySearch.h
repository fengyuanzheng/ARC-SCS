#ifndef ARC_SCS_CAPACITY_SEARCH_H
#define ARC_SCS_CAPACITY_SEARCH_H

#include "ARCSCSConfig.h"
#include "SearchStatistics.h"

class Graph;

// Dispatches a typed query to the exact graph search.
class CapacitySearch
{
public:
	static void solve(Graph &graph, const Query &query, const ARCSCSConfig &config, int &k_min, int &k_max);
};

#endif
