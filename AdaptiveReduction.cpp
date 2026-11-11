#include "Graph.h"

#include <limits>

using namespace std;

namespace
{
const ui INVALID_VERTEX = numeric_limits<ui>::max();
}

void Graph::update_query_vertex(ui n, ui *out_mapping, int &query_vertex, const int original_q_ID)
{
	int new_query_vertex = n;
	for (ui i = 0; i < n; i++)
		if (out_mapping[i] == static_cast<ui>(original_q_ID))
		{
			new_query_vertex = i;
			break;
		}
	query_vertex = new_query_vertex;
}

void Graph::update_feasible_solution(ui *out_mapping, vector<ui> &record_solution, bool &find_feasible_solution)
{
	find_feasible_solution = true;
	record_solution.resize(feasible_solution.size());
	// A query's local ID can happen to equal its original ID even though
	// other vertices were renumbered. The mapping is identity without shrink,
	// so always applying it is both necessary and safe.
	for (ui i = 0; i < feasible_solution.size(); i++)
		record_solution[i] = out_mapping[feasible_solution[i]];
}

void Graph::give_ininital_feasible_sol(ui S)
{
	feasible_solution.clear();
	for (int i = 0; static_cast<ui>(i) < S; i++)
		feasible_solution.push_back(i);
}

void Graph::extract_subgraph_within_2hops(ui u, vector<ui> &ids, ui *rid, vector<pair<ui, ui>> &vp, char *exists, ept *pstart, ui *edges)
{
	ids.clear();
	vp.clear();
	ids.push_back(u);
	exists[u] = 1;
	rid[u] = 0;

	for (ept i = pstart[u]; i < pstart[u + 1]; i++)
	{
		ids.push_back(edges[i]);
		exists[edges[i]] = 1;
		rid[edges[i]] = ids.size() - 1;
	}

	ui old_size = ids.size();
	for (ui i = 1; i < old_size; i++)
	{
		ui v = ids[i];
		for (ept j = pstart[v]; j < pstart[v + 1]; j++)
		{
			ui w = edges[j];
			if (exists[w])
				continue;
			ids.push_back(w);
			exists[w] = 1;
			rid[w] = ids.size() - 1;
		}
	}

	for (ui i = 0; i < ids.size(); i++)
	{
		ui v = ids[i];
		for (ept j = pstart[v]; j < pstart[v + 1]; j++)
			if (exists[edges[j]] && rid[v] < rid[edges[j]])
				vp.push_back(make_pair(rid[v], rid[edges[j]]));
	}

	for (ui i = 0; i < ids.size(); i++)
		exists[ids[i]] = 0;
}

// Query-independent online 2-hop extraction over the immutable source CSR.
// The core-shrink mapping filters deleted vertices, while out_mapping maps the
// surviving local ids back to source ids for adjacency scans. This avoids
// materializing the full shrunk CSR merely to construct the Matrix subgraph.
bool Graph::extract_subgraph_within_2hops_readonly(ui original_q,
												 const ui *out_mapping,
												 const ept *source_pstart, const ui *source_edges,
												 bool source_core_ordered,
												 vector<ui> &ids,
												 vector<pair<ui, ui>> &vp)
{
	ids.clear();
	vp.clear();
	if (original_q >= shrink_old2new.size())
		return false;
	ui query_vertex = shrink_old2new[original_q];
	if (query_vertex == INVALID_VERTEX)
		return false;

	vector<char> exists(n, 0);
	vector<ui> rid(n, INVALID_VERTEX);
	ids.push_back(query_vertex);
	exists[query_vertex] = 1;
	rid[query_vertex] = 0;

	for (ept i = source_pstart[original_q]; i < source_pstart[original_q + 1]; ++i)
	{
		ui old_v = source_edges[i];
		if (old_v >= shrink_old2new.size())
			continue;
		ui new_v = shrink_old2new[old_v];
		if (new_v == INVALID_VERTEX)
		{
			if (source_core_ordered)
				break;
			continue;
		}
		if (exists[new_v])
			continue;
		rid[new_v] = ids.size();
		exists[new_v] = 1;
		ids.push_back(new_v);
	}

	const size_t one_hop_end = ids.size();
	for (size_t i = 1; i < one_hop_end; ++i)
	{
		ui old_v = out_mapping[ids[i]];
		for (ept j = source_pstart[old_v]; j < source_pstart[old_v + 1]; ++j)
		{
			ui old_w = source_edges[j];
			if (old_w >= shrink_old2new.size())
				continue;
			ui new_w = shrink_old2new[old_w];
			if (new_w == INVALID_VERTEX)
			{
				if (source_core_ordered)
					break;
				continue;
			}
			if (exists[new_w])
				continue;
			rid[new_w] = ids.size();
			exists[new_w] = 1;
			ids.push_back(new_w);
		}
	}

	for (ui new_v : ids)
	{
		ui old_v = out_mapping[new_v];
		for (ept j = source_pstart[old_v]; j < source_pstart[old_v + 1]; ++j)
		{
			ui old_w = source_edges[j];
			if (old_w >= shrink_old2new.size())
				continue;
			ui new_w = shrink_old2new[old_w];
			if (new_w == INVALID_VERTEX)
			{
				if (source_core_ordered)
					break;
				continue;
			}
			if (exists[new_w] && rid[new_v] < rid[new_w])
				vp.push_back(make_pair(rid[new_v], rid[new_w]));
		}
	}
	return true;
}

void Graph::core_shrink_graph(ui &n, ept &m, ui *peel_sequence, ui *core, ui *out_mapping, ui *in_mapping, ui *rid, ept *&pstart, ui *&edges, bool output)
{
	ui cnt = 0;
	for (ui i = 0; i < n; i++)
		if (core[i] + S > feasible_solution.size())
		{
			rid[i] = cnt;
			if (in_mapping == nullptr)
				out_mapping[cnt] = i;
			else
				out_mapping[cnt] = in_mapping[i];
			++cnt;
		}

	if (cnt != n)
	{

		cnt = 0;
		ept pos = 0;
		for (ui i = 0; i < n; i++)
			if (core[i] + S > feasible_solution.size())
			{
				ept t_start = pstart[i];
				pstart[cnt] = pos;
				for (ept j = t_start; j < pstart[i + 1]; j++)
					if (core[edges[j]] + S > feasible_solution.size())
					{
						edges[pos++] = rid[edges[j]];
					}
				++cnt;
			}
		pstart[cnt] = pos;

		// Compact core into local numbering. Legacy indexes may additionally
		// carry a peel sequence; keep it consistent when present, but the
		// core-only query path neither constructs nor consumes that sequence.
		if (peel_sequence != nullptr)
		{
			assert(core[peel_sequence[n - cnt - 1]] == 0 || core[peel_sequence[n - cnt - 1]] + S <= feasible_solution.size());
			assert(cnt == 0 || core[peel_sequence[n - cnt]] + S > feasible_solution.size());
		}
		for (ui i = 0; i < cnt; i++)
		{
			if (peel_sequence != nullptr)
				peel_sequence[i] = rid[peel_sequence[n - cnt + i]];
			core[i] = core[out_mapping[i]];
		}

		if (pos > 0u && pos < m / 2)
		{
			ept *pstart_new = new ept[cnt + 1];
			ui *edges_new = new ui[pos];

			memcpy(pstart_new, pstart, sizeof(ept) * (cnt + 1));
			memcpy(edges_new, edges, sizeof(ui) * pos);

			delete[] pstart;
			pstart = pstart_new;
			delete[] edges;
			edges = edges_new;
		}

		n = cnt;
		m = pos;
	}

	if (output)
		printf("*** After core shrink: n = %s, m = %s (undirected)\n", Utility::integer_to_string(n).c_str(), Utility::integer_to_string(m / 2).c_str());
}

// Materialize the exact induced CSR described by rid[original_id].
// Two passes first count and then allocate the exact number of retained arcs.
// Keeping this operation separate lets the Matrix path postpone it until
// Fallback actually needs the full graph without changing CSR capacity/order.
void Graph::materialize_query_csr_from_mapping(ui source_n, ui local_n,
											const ui *rid,
											const ept *source_pstart, const ui *source_edges,
											bool source_core_ordered,
											ept *&query_pstart, ui *&query_edges, ept &query_m,
											bool &owns_query_graph)
{
	ept kept_edges = 0;
	for (ui old_u = 0; old_u < source_n; ++old_u)
	{
		if (rid[old_u] == INVALID_VERTEX)
			continue;
		for (ept j = source_pstart[old_u]; j < source_pstart[old_u + 1]; ++j)
		{
			ui new_v = rid[source_edges[j]];
			if (new_v == INVALID_VERTEX)
			{
				if (source_core_ordered)
					break;
				continue;
			}
			++kept_edges;
		}
	}

	ept *local_pstart = new ept[(size_t)local_n + 1];
	ui *local_edges = new ui[kept_edges == 0u ? 1 : kept_edges];
	ept pos = 0;
	ui new_u = 0;
	for (ui old_u = 0; old_u < source_n; ++old_u)
	{
		if (rid[old_u] == INVALID_VERTEX)
			continue;
		assert(rid[old_u] == new_u);
		local_pstart[new_u++] = pos;
		const ept row_begin = pos;
		for (ept j = source_pstart[old_u]; j < source_pstart[old_u + 1]; ++j)
		{
			ui new_v = rid[source_edges[j]];
			if (new_v == INVALID_VERTEX)
			{
				if (source_core_ordered)
					break;
				continue;
			}
			local_edges[pos++] = new_v;
		}
		if (source_core_ordered)
			std::sort(local_edges + row_begin, local_edges + pos);
	}
	local_pstart[local_n] = pos;
	assert(new_u == local_n && pos == kept_edges);

	query_pstart = local_pstart;
	query_edges = local_edges;
	query_m = kept_edges;
	owns_query_graph = true;
}

// Memory-safe batch variant of core_shrink_graph.
//
// The original graph remains immutable.  We always build the survivor mapping
// and compact core/peel.  With a candidate index, edge materialization is
// deferred: Matrix can extract its small indexed subgraph directly from the
// immutable original CSR, while Fallback materializes this exact induced CSR
// on demand.  Without a candidate index the previous eager behavior remains.
void Graph::core_shrink_graph_readonly(ui &n, ept &m, ui *peel_sequence, ui *core,
									  ui *out_mapping, ui *rid,
									  const ept *source_pstart, const ui *source_edges,
									  ept *&query_pstart, ui *&query_edges,
									  bool &owns_query_graph,
									  bool &query_graph_deferred,
									  bool defer_edges,
									  bool output)
{
	const ui source_n = n;
	ui cnt = 0;
	for (ui i = 0; i < source_n; ++i)
	{
		if (core[i] + S > feasible_solution.size())
		{
			rid[i] = cnt;
			out_mapping[cnt] = i;
			++cnt;
		}
	}

	if (cnt == source_n)
	{
		query_pstart = const_cast<ept *>(source_pstart);
		query_edges = const_cast<ui *>(source_edges);
		owns_query_graph = false;
		query_graph_deferred = false;
		if (output)
			printf("*** After read-only core shrink: n = %s, m = %s (undirected), borrowed_original=1\n",
				   Utility::integer_to_string(n).c_str(),
				   Utility::integer_to_string(m / 2).c_str());
		return;
	}

	if (peel_sequence != nullptr)
	{
		assert(core[peel_sequence[source_n - cnt - 1]] == 0 ||
			   core[peel_sequence[source_n - cnt - 1]] + S <= feasible_solution.size());
		assert(cnt == 0 || core[peel_sequence[source_n - cnt]] + S > feasible_solution.size());
	}
	for (ui i = 0; i < cnt; ++i)
	{
		if (peel_sequence != nullptr)
			peel_sequence[i] = rid[peel_sequence[source_n - cnt + i]];
		core[i] = core[out_mapping[i]];
	}

	n = cnt;
	if (defer_edges)
	{
		m = 0;
		query_pstart = const_cast<ept *>(source_pstart);
		query_edges = const_cast<ui *>(source_edges);
		owns_query_graph = false;
		query_graph_deferred = true;
	}
	else
	{
		materialize_query_csr_from_mapping(source_n, cnt, rid,
										 source_pstart, source_edges, false,
										 query_pstart, query_edges, m,
										 owns_query_graph);
		query_graph_deferred = false;
	}
	if (output)
		printf("*** After read-only core shrink: n = %s, m = %s (undirected), borrowed_original=0 deferred_csr=%d\n",
			   Utility::integer_to_string(n).c_str(),
			   query_graph_deferred ? "deferred" : Utility::integer_to_string(m / 2).c_str(),
			   query_graph_deferred ? 1 : 0);
}
