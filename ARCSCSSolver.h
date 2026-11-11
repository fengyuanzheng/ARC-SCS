#ifndef ARC_SCS_SOLVER_H
#define ARC_SCS_SOLVER_H

#include "Graph.h"
#include "ARCSCSConfig.h"
#include "SearchStatistics.h"

// Solver interface. Graph must outlive the solver.
class ARCSCSSolver
{
public:
	ARCSCSSolver(Graph &graph, const ARCSCSConfig &config);

	SearchResult solve_arc_scs(int query_vertex, int size_lower_bound,
		int size_upper_bound, int &k_min, int &k_max);

private:
	Graph &graph_;
	ARCSCSConfig config_;

};

#endif
