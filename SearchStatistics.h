#ifndef ARC_SCS_SEARCH_STATISTICS_H
#define ARC_SCS_SEARCH_STATISTICS_H

#include <string>
#include <vector>

// Immutable query description shared by public and internal entry points.
struct Query
{
	int vertex;
	int size_lower_bound;
	int size_upper_bound;

	Query(int query_vertex, int lower_bound, int upper_bound)
		: vertex(query_vertex), size_lower_bound(lower_bound),
		  size_upper_bound(upper_bound) {}
};

struct SearchResult
{
	long long total_us;
	int opt_k;
	std::string core_source;
	bool success;
	// A completed infeasibility proof is not a successful empty community.
	bool infeasible;
	std::vector<unsigned int> vertices;

	SearchResult() : total_us(0), opt_k(0), core_source(""), success(false), infeasible(false) {}
};

#endif
