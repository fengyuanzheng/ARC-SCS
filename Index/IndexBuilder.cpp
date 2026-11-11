#include "IndexBuilder.h"
#include "../Graph.h"

bool IndexBuilder::build(Graph &graph, const std::string &path,
	const IndexBuildOptions &options)
{
	return graph.build_offline_index(path, options.core_only,
		options.core_peel_only, options.core_threshold_bitmap,
		options.core_threshold_max, options.hybrid_core_threshold_bitmap,
		options.core_ordered_adjacency);
}

#include <algorithm>
#include <fstream>
#include <limits>
#include <map>

using namespace std;

namespace
{
const char INDEX_MAGIC_FULL_CORE_PEEL_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '7'};
const char INDEX_MAGIC_CORE_PEEL_ONLY_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '9'};
const char INDEX_MAGIC_CORE_ONLY_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'A'};
const char INDEX_MAGIC_CORE_THRESHOLD_BITMAP_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'B'};
const char INDEX_MAGIC_HYBRID_CORE_THRESHOLD_BITMAP_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'C'};
const char INDEX_MAGIC_CORE_ORDERED_ADJACENCY_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'D'};

unsigned long long saturating_add_ull(unsigned long long a, unsigned long long b)
{
	if (numeric_limits<unsigned long long>::max() - a < b)
		return numeric_limits<unsigned long long>::max();
	return a + b;
}
}

bool Graph::build_offline_index(const std::string &index_file, bool core_only,
		bool core_peel_only, bool core_threshold_bitmap, ui core_threshold_max,
		bool hybrid_core_threshold_bitmap, bool core_ordered_adjacency_index)
{
	const bool build_core_ordered_adjacency = core_ordered_adjacency_index;
	if (n == 0u)
	{
		fprintf(stderr, "Cannot build index %s: the graph is empty.\n", index_file.c_str());
		return false;
	}

	Timer total_timer;
	Timer stage_timer;
	ensure_graph_fingerprint();
	vector<ui> query_vertices;
	if (core_only || core_peel_only || core_threshold_bitmap ||
		hybrid_core_threshold_bitmap || build_core_ordered_adjacency)
	{
		// Query-independent lightweight index: candidate lists are deliberately
		// omitted. Every future query derives its local candidates online.
	}
	else
	{
		// Candidate indexes always cover every graph vertex.
		query_vertices.reserve(n);
		for (ui q = 0; q < n; ++q)
			query_vertices.push_back(q);
	}

	// Core decomposition is computed once. peel_sequence remains construction
	// scratch for degen(), but the lightweight format deliberately omits it.
	char *vis = new char[n];
	ui *peel_sequence = new ui[n], *core = new ui[n], *degree = new ui[n], core_q = n;
	ListLinearHeap *heap = new ListLinearHeap(n, n - 1);
	stage_timer.restart();
	degen(n, peel_sequence, core, pstart, edges, degree, vis, heap, core_q, 0);
	long long core_time = stage_timer.elapsed();

	vector<unsigned long long> offsets(query_vertices.size() + 1, 0);
	vector<ui> candidate_ids;
	vector<ui> candidate_phi;
	vector<ui> stamps;
	vector<ui> phi;
	vector<ui> touched;
	if (!core_only && !core_peel_only && !core_threshold_bitmap &&
		!hybrid_core_threshold_bitmap && !build_core_ordered_adjacency)
	{
		stamps.assign(n, 0);
		phi.assign(n, 0);
		touched.reserve(1024);
	}
	ui stamp = 1;

	for (ui qi = 0; qi < query_vertices.size(); ++qi)
	{
		ui q = query_vertices[qi];
		offsets[qi] = candidate_ids.size();
		touched.clear();
		ui current_stamp = stamp++;
		if (stamp == 0u)
		{
			fill(stamps.begin(), stamps.end(), 0);
			current_stamp = stamp++;
		}

		for (ept i = pstart[q]; i < pstart[q + 1]; ++i)
		{
			ui v = edges[i];
			if (v == q)
				continue;

			if (stamps[v] != current_stamp)
			{
				stamps[v] = current_stamp;
				phi[v] = core[v];
				touched.push_back(v);
			}
			else if (phi[v] < core[v])
				phi[v] = core[v];
		}

		for (ept i = pstart[q]; i < pstart[q + 1]; ++i)
		{
			ui witness = edges[i];
			if (witness == q)
				continue;

			for (ept j = pstart[witness]; j < pstart[witness + 1]; ++j)
			{
				ui w = edges[j];
				if (w == q)
					continue;

				if (stamps[w] != current_stamp)
				{
					stamps[w] = current_stamp;
					phi[w] = core[witness];
					touched.push_back(w);
				}
				else if (phi[w] < core[witness])
					phi[w] = core[witness];
			}
		}

		for (ui v : touched)
		{
			candidate_ids.push_back(v);
			candidate_phi.push_back(phi[v]);
		}
	}

	offsets[query_vertices.size()] = candidate_ids.size();

	ofstream out(index_file, ios::binary);
	if (!out.is_open())
	{
		fprintf(stderr, "Failed to open index file %s for writing\n", index_file.c_str());
		delete heap;
		delete[] core;
		delete[] peel_sequence;
		delete[] vis;
		delete[] degree;
		return false;
	}

	// Full candidate indexes use the original query id directly as the offset index.
	unsigned long long total_candidates = candidate_ids.size();
	if (core_threshold_bitmap || hybrid_core_threshold_bitmap ||
		build_core_ordered_adjacency)
	{
		const unsigned long long word_count = ((unsigned long long)n + 63ull) >> 6;
		const unsigned long long threshold_count = (unsigned long long)core_threshold_max + 1ull;
		if (threshold_count > 4096ull ||
			(word_count != static_cast<unsigned long long>(0) && threshold_count >
			 std::numeric_limits<size_t>::max() / word_count))
		{
			printf("CTBI threshold range is too large: max_threshold=%u\n", core_threshold_max);
			out.close();
			delete heap;
			delete[] core;
			delete[] peel_sequence;
			delete[] vis;
			delete[] degree;
			return false;
		}
		vector<unsigned long long> threshold_counts(threshold_count, 0);
		vector<unsigned long long> threshold_core_sums(threshold_count, 0);
		vector<unsigned long long> threshold_bits((size_t)(threshold_count * word_count), 0);
		for (ui v = 0; v < n; ++v)
		{
			const ui limit = std::min(core[v], core_threshold_max + 1u);
			const unsigned long long word = (unsigned long long)v >> 6;
			const unsigned long long bit = 1ull << (v & 63u);
			for (ui threshold = 0; threshold < limit; ++threshold)
			{
				++threshold_counts[threshold];
				threshold_core_sums[threshold] = saturating_add_ull(
					threshold_core_sums[threshold], core[v]);
				threshold_bits[(size_t)((unsigned long long)threshold * word_count + word)] |= bit;
			}
		}

		vector<ui> core_ordered_edges;
		long long core_ordered_adjacency_time = 0;
		if (build_core_ordered_adjacency)
		{
			stage_timer.restart();
				core_ordered_edges.assign(edges, edges + m);
				for (ui u = 0; u < n; ++u)
					std::sort(core_ordered_edges.begin() + (size_t)pstart[u],
						core_ordered_edges.begin() + (size_t)pstart[u + 1],
						[&](ui a, ui b) {
							if (core[a] != core[b])
								return core[a] > core[b];
							return a < b;
						});
			core_ordered_adjacency_time = stage_timer.elapsed();
		}

		if (core_ordered_adjacency_index)
			out.write(INDEX_MAGIC_CORE_ORDERED_ADJACENCY_FP,
				sizeof(INDEX_MAGIC_CORE_ORDERED_ADJACENCY_FP));
		else if (hybrid_core_threshold_bitmap)
			out.write(INDEX_MAGIC_HYBRID_CORE_THRESHOLD_BITMAP_FP,
				sizeof(INDEX_MAGIC_HYBRID_CORE_THRESHOLD_BITMAP_FP));
		else
			out.write(INDEX_MAGIC_CORE_THRESHOLD_BITMAP_FP,
				sizeof(INDEX_MAGIC_CORE_THRESHOLD_BITMAP_FP));
		out.write(reinterpret_cast<const char *>(&original_graph_n), sizeof(ui));
		out.write(reinterpret_cast<const char *>(&original_graph_m), sizeof(ept));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_lo), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_hi), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(&core_threshold_max), sizeof(ui));
		out.write(reinterpret_cast<const char *>(&word_count), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(core), sizeof(ui) * n);
		out.write(reinterpret_cast<const char *>(threshold_counts.data()),
			  sizeof(unsigned long long) * threshold_counts.size());
		out.write(reinterpret_cast<const char *>(threshold_core_sums.data()),
			  sizeof(unsigned long long) * threshold_core_sums.size());
		out.write(reinterpret_cast<const char *>(threshold_bits.data()),
			  sizeof(unsigned long long) * threshold_bits.size());
		if (build_core_ordered_adjacency)
		{
			out.write(reinterpret_cast<const char *>(core_ordered_edges.data()),
				sizeof(ui) * (size_t)m);
			printf("\tThe core-ordered adjacency construction time is: %s (microseconds)\n",
				Utility::integer_to_string(core_ordered_adjacency_time).c_str());
		}
		if (hybrid_core_threshold_bitmap || build_core_ordered_adjacency)
			out.write(reinterpret_cast<const char *>(peel_sequence), sizeof(ui) * n);
	}
	else if (core_only)
	{
		out.write(INDEX_MAGIC_CORE_ONLY_FP, sizeof(INDEX_MAGIC_CORE_ONLY_FP));
		out.write(reinterpret_cast<const char *>(&original_graph_n), sizeof(ui));
		out.write(reinterpret_cast<const char *>(&original_graph_m), sizeof(ept));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_lo), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_hi), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(core), sizeof(ui) * n);
	}
	else if (core_peel_only)
	{
		out.write(INDEX_MAGIC_CORE_PEEL_ONLY_FP, sizeof(INDEX_MAGIC_CORE_PEEL_ONLY_FP));
		out.write(reinterpret_cast<const char *>(&original_graph_n), sizeof(ui));
		out.write(reinterpret_cast<const char *>(&original_graph_m), sizeof(ept));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_lo), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_hi), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(core), sizeof(ui) * n);
		out.write(reinterpret_cast<const char *>(peel_sequence), sizeof(ui) * n);
	}
	else
	{
		out.write(INDEX_MAGIC_FULL_CORE_PEEL_FP, sizeof(INDEX_MAGIC_FULL_CORE_PEEL_FP));
		out.write(reinterpret_cast<const char *>(&original_graph_n), sizeof(ui));
		out.write(reinterpret_cast<const char *>(&original_graph_m), sizeof(ept));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_lo), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(&graph_fingerprint_hi), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(&total_candidates), sizeof(unsigned long long));
		out.write(reinterpret_cast<const char *>(core), sizeof(ui) * n);
		out.write(reinterpret_cast<const char *>(peel_sequence), sizeof(ui) * n);
		out.write(reinterpret_cast<const char *>(offsets.data()), sizeof(unsigned long long) * offsets.size());
	}
	if (total_candidates > static_cast<unsigned long long>(0))
	{
		out.write(reinterpret_cast<const char *>(candidate_ids.data()), sizeof(ui) * candidate_ids.size());
		out.write(reinterpret_cast<const char *>(candidate_phi.data()), sizeof(ui) * candidate_phi.size());
	}
	out.flush();
	out.close();
	const bool written = static_cast<bool>(out);

	delete heap;
	delete[] core;
	delete[] peel_sequence;
	delete[] vis;
	delete[] degree;

	if (!written)
	{
		fprintf(stderr, "Failed to write or close index file %s\n", index_file.c_str());
		return false;
	}
	ifstream size_in(index_file, ios::binary | ios::ate);
	double index_file_size_MB = size_in.is_open() ? (double)size_in.tellg() / (1024.0 * 1024.0) : 0.0;

	printf("Offline index has been written to %s\n", index_file.c_str());
	const char *built_index_type = core_ordered_adjacency_index ? "core_ordered_adjacency_hybrid_ctbi" :
		hybrid_core_threshold_bitmap ? "hybrid_core_peel_threshold_bitmap" :
		core_threshold_bitmap ? "core_threshold_bitmap" :
		core_only ? "core_only" :
		core_peel_only ? "core_peel_only" :
		"full_candidate";
	printf("index_type=%s\n", built_index_type);
	if (core_threshold_bitmap || hybrid_core_threshold_bitmap ||
		build_core_ordered_adjacency)
		printf("ctbi_max_threshold=%u\n", core_threshold_max);
	printf("\tThe core preprocessing time for index construction is: %s (microseconds)\n", Utility::integer_to_string(core_time).c_str());
	printf("indexed_query_count=%s\n", Utility::integer_to_string((long long)query_vertices.size()).c_str());
	printf("total_indexed_candidates=%s\n", Utility::integer_to_string((long long)total_candidates).c_str());
	double average_candidates = query_vertices.empty() ? 0.0 : (double)total_candidates / (double)query_vertices.size();
	printf("average_candidates_per_query=%.2f\n", average_candidates);
	printf("index_file_size_MB=%.2f\n", index_file_size_MB);
	printf("\tThe total index construction time is: %s (microseconds)\n", Utility::integer_to_string(total_timer.elapsed()).c_str());
	return true;
}
