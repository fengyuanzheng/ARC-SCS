#ifndef _GRAPH_H_
#define _GRAPH_H_

#include "Utility.h"
#include "Timer.h"
#include "LinearHeap.h"
#include "ARCSCSConfig.h"
#include "SearchStatistics.h"

class Graph
{
public:
	using QueryResult = SearchResult;

private:
	std::string dir; // input graph directory
	ui n;			 // number of nodes of the graph
	ept m;			 // number of edges of the graph
	ui S;			 // the value of k in k-plex
	ui original_graph_n;
	ept original_graph_m;
	bool graph_fingerprint_ready;
	unsigned long long graph_fingerprint_lo;
	unsigned long long graph_fingerprint_hi;
	bool concise_log_enabled;
	bool concise_query_log() const { return concise_log_enabled; }

	ept *pstart; // offset of neighbors of nodes
	ept *pend;	 // used in search
	ept *pend_buf;
	ui *edges; // adjacent ids of edges
	ui *edgelist_pointer;

	std::vector<ui> feasible_solution;
	bool index_loaded;
	std::vector<unsigned long long> index_offsets;
	std::vector<ui> index_candidate_ids;
	std::vector<ui> index_candidate_phi;
	std::vector<ui> shrink_old2new;
	bool index_is_full;
	bool index_core_loaded;

	std::vector<ui> index_core;
	// Core-Threshold Bitmap Index (CTBI): bitmap t contains exactly the
	// original vertices whose core number is greater than t. Counts and core
	// sums let query-time shrink avoid a graph-wide counting pass.
	bool index_core_threshold_bitmap_loaded;
	ui index_core_threshold_max;
	unsigned long long index_core_threshold_words;
	std::vector<unsigned long long> index_core_threshold_counts;
	std::vector<unsigned long long> index_core_threshold_core_sums;
	bool index_core_threshold_bitmap_available;
	std::string index_core_threshold_bitmap_file;
	unsigned long long index_core_threshold_bitmap_offset;
	size_t index_core_threshold_bitmap_bytes;
	int index_core_threshold_bitmap_fd;
	void *index_core_threshold_bitmap_map_base;
	size_t index_core_threshold_bitmap_map_length;
	const char *index_core_threshold_bitmap_mapped_data;
	// COAP stores every original CSR row in descending neighbor-core order.
	// With a CTBI threshold t, the first neighbor with core <= t terminates
	// the row scan, eliminating repeated rejected-edge probes.
	bool index_core_ordered_adjacency_loaded;
	bool index_core_ordered_adjacency_available;
	std::string index_core_ordered_adjacency_file;
	unsigned long long index_core_ordered_adjacency_offset;
	size_t index_core_ordered_adjacency_bytes;
	int index_core_ordered_adjacency_fd;
	void *index_core_ordered_adjacency_map_base;
	size_t index_core_ordered_adjacency_map_length;
	const ui *index_core_ordered_adjacency_mapped_data;
	bool index_peel_loaded;
	bool index_peel_available;
	long long index_peel_load_us;
	std::vector<ui> index_peel_sequence;
	std::string index_peel_file;
	unsigned long long index_peel_offset;
	size_t index_peel_bytes;
	int index_peel_fd;
	void *index_peel_map_base;
	size_t index_peel_map_length;
	const ui *index_peel_mapped_data;
	QueryResult last_query_result;

	// Query-time heuristic acceleration.  One persistent packed word per vertex
	// stores an epoch, membership, solution degree, and degree into the current
	// greedy solution.  Advancing the epoch replaces repeated O(n) clearing and
	// lets a batch reuse the same workspace without changing greedy decisions.

	std::vector<ui> heuristic_epoch_state;
	ui heuristic_epoch_counter;

public:
	Graph(const char *_dir, const int _K);
	~Graph();
	void readBinFile();
	void set_concise_log(bool enabled);

	std::string get_file_name_without_suffix(const std::string &file_path);
	// Internal exact-search entry point; use ARCSCSSolver for queries.
	void ARC_SCS(const Query &query, int &k_min, int &k_max, const ARCSCSConfig &config);
	bool build_offline_index(const std::string &index_file, bool core_only = false,
						 bool core_peel_only = false,
						 bool core_threshold_bitmap = false,
						 ui core_threshold_max = 11,
						 bool hybrid_core_threshold_bitmap = false,
						 bool core_ordered_adjacency_index = false);

	// Map every read-only lazy index plane before a fork-based batch starts.
	// Children inherit these mappings instead of reopening index sections.

	bool load_offline_index(const std::string &index_file);

	const QueryResult &get_last_query_result() const;
	bool extract_subgraph_from_index(ui original_q, int k_min, std::vector<ui> &ids, std::vector<std::pair<ui, ui>> &vp);
	bool extract_subgraph_from_index_readonly(ui original_q, int k_min,
										 const ui *out_mapping,
										 const ept *source_pstart, const ui *source_edges,
										 bool source_core_ordered,
										 std::vector<ui> &ids,
										 std::vector<std::pair<ui, ui>> &vp);

private:
	ui degen(ui n, ui *peel_sequence, ui *core, ept *pstart, ui *edges, ui *degree, char *vis, ListLinearHeap *heap, ui &core_q, ui query_vertex);
	void core_shrink_graph(ui &n, ept &m, ui *peel_sequence, ui *core, ui *out_mapping, ui *in_mapping, ui *rid, ept *&pstart, ui *&edges, bool output);
	void core_shrink_graph_readonly(ui &n, ept &m, ui *peel_sequence, ui *core,
									ui *out_mapping, ui *rid,
									const ept *source_pstart, const ui *source_edges,
									ept *&query_pstart, ui *&query_edges,
									bool &owns_query_graph, bool &query_graph_deferred,
									bool defer_edges,
									bool output);
	void materialize_query_csr_from_mapping(ui source_n, ui local_n,
										 const ui *rid,
										 const ept *source_pstart, const ui *source_edges,
										 bool source_core_ordered,
										 ept *&query_pstart, ui *&query_edges, ept &query_m,
										 bool &owns_query_graph);
	void give_ininital_feasible_sol(ui S);
	void update_query_vertex(ui n, ui *out_mapping, int &query_vertex, const int original_q_ID);
	void extract_subgraph_within_2hops(ui u, std::vector<ui> &ids, ui *rid, std::vector<std::pair<ui, ui>> &vp, char *exists, ept *pstart, ui *edges);
	bool extract_subgraph_within_2hops_readonly(ui original_q,
											 const ui *out_mapping,
											 const ept *source_pstart, const ui *source_edges,
											 bool source_core_ordered,
											 std::vector<ui> &ids,
											 std::vector<std::pair<ui, ui>> &vp);
	void update_feasible_solution(ui *out_mapping, std::vector<ui> &record_solution, bool &find_feasible_solution);
	bool get_index_range(ui original_q, unsigned long long &begin, unsigned long long &end) const;
	void ensure_graph_fingerprint();
	bool ensure_index_peel_loaded();
	void release_index_peel_mapping();
	bool ensure_index_core_threshold_bitmap_loaded();
	void release_index_core_threshold_bitmap_mapping();
	bool ensure_index_core_ordered_adjacency_loaded();
	void release_index_core_ordered_adjacency_mapping();
	void SCS_heu_star(int QID, int N1, int N2, std::vector<ui> &H, int &k_min, int k_max, ui *core);

	void budgeted_monotone_multistart_refine(int QID, int LB_size, int UB_size, std::vector<ui> &heu_solution, int &k_min, int &k_max, ui *core);
	int size_aware_support_upper_bound(int QID, int UB_size, int incumbent_k,
		int original_upper, ui *core, unsigned long long &edge_work,
		bool &exact) const;
	void my_heu(std::vector<ui> &heu_solution, ui &k_min, ui k_max, int QID, int LB_size, int UB_size, ui *core);
};
#endif
