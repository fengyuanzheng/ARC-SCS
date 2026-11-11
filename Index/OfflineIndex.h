#ifndef ARC_SCS_OFFLINE_INDEX_H
#define ARC_SCS_OFFLINE_INDEX_H

#include <string>

class Graph;

// Query-side index boundary. Binary layout and mmap ownership remain in the
// validated Graph implementation for now; callers no longer depend on those
// details directly.
class OfflineIndex
{
public:
	static bool load(Graph &graph, const std::string &path);

};

#endif
