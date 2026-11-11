#ifndef ARC_SCS_INDEX_BUILDER_H
#define ARC_SCS_INDEX_BUILDER_H

#include "../Utility.h"
#include <string>

class Graph;

struct IndexBuildOptions
{
	bool core_only = false;
	bool core_peel_only = false;
	bool core_threshold_bitmap = false;
	ui core_threshold_max = 11;
	bool hybrid_core_threshold_bitmap = false;
	bool core_ordered_adjacency = false;
};

class IndexBuilder
{
public:
	// Returns false if construction or writing the index fails.
	static bool build(Graph &graph, const std::string &path,
		const IndexBuildOptions &options);
};

#endif
