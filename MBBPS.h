#ifndef _MBBPS_
#define _MBBPS_

#include "Utility.h"
#include "Timer.h"
#include "CapacityBound.h"
#include <limits>
#include "ARCSCSConfig.h"

class MBBPS
{
public:
	struct SearchStats
	{

		unsigned long long adaptive_budget_run_cnt = 0;

		unsigned long long adaptive_budget_removed_vertices_so_far = 0;

		unsigned long long pair_capacity_bound_gap_max = 0;

		unsigned long long pair_capacity_bound_hit_C_max = 0;

		unsigned long long pair_capacity_bound_excess_min =
			std::numeric_limits<unsigned long long>::max();

		unsigned long long triple_capacity_bound_hit_C_max = 0;

		unsigned long long work_adaptive_work_ops = 0;
		unsigned long long work_adaptive_search_credit = 0;
		unsigned long long work_adaptive_removed_credit = 0;

		long long adaptive_budget_us_so_far = 0;

		ui work_adaptive_probe_interval = 1;

		void reset()
		{
			*this = SearchStats();
		}

	};

private:
	ui n;
	ept *pstart;
	ept *pend;
	ui *edges;
	ept edges_cap;

	ui *degree;
	ui *degree_in_S;

	ui S;
	ui *best_solution;
	ui optimal_sol_size;
	ui _size_UB_;
	ui UB_size;

	ui *neighbors;
	ui *nonneighbors;

	ui *SR;
	ui *SR_rid;
	queue<ui> Qv;
	ui *level_id;
	int query_vertex_global;

	ui *buf;
	ui *buf1;
	ui *buf2;
	char *vis;

	vector<pair<ui, ui>> vp;
	ui tau = 5; // the threshold used to control the invocation of our proposed query decomposition technique

	ARCWorkLedger work_ledger;
	unsigned long long pair_ledger_runs;
	unsigned long long pair_ledger_skips;
	unsigned long long pair_probe_interval;
	ui pair_last_candidate_count;
	unsigned long long triple_ledger_runs;
	unsigned long long triple_ledger_skips;
	unsigned long long triple_probe_interval;

	bool fallback_uism_active;
	struct UISMEdgeSwap
	{
		ui row;
		ept position;
		ept last;
	};
	struct UISMRemovalFrame
	{
		ui vertex;
		size_t swap_begin;
	};
	vector<ept> uism_reverse_edge;
	vector<UISMEdgeSwap> uism_edge_swap_trail;
	vector<UISMRemovalFrame> uism_removal_trail;

	SearchStats stats;
	// A zero limit keeps the exact solver unchanged.  Target-demotion probes
	// use a structural node budget and treat exhaustion as "unknown", never as
	// an infeasibility result.
	unsigned long long search_node_limit;
	unsigned long long search_nodes_visited;
	bool search_node_limit_exhausted;
	struct SearchNodeBudgetExhausted {};

	unsigned long long work_adaptive_total_work;
	unsigned long long work_adaptive_total_removed;
	unsigned long long work_adaptive_search_credit;
	unsigned long long work_adaptive_removal_benefit;

	unsigned long long work_adaptive_total_runs;
	unsigned long long work_adaptive_initial_total_work;
	unsigned long long work_adaptive_initial_total_removed;
	unsigned long long work_adaptive_initial_search_credit;
	unsigned long long work_adaptive_initial_removal_benefit;
	unsigned long long work_adaptive_initial_total_runs;
	ui work_adaptive_initial_probe_interval;
	ui work_adaptive_skips_since_probe;
	ui work_adaptive_probe_interval;
	bool work_adaptive_forced_probe;

	struct RR1BudgetWork
	{
		unsigned long long word_ops = 0;
		unsigned long long candidate_checks = 0;
		unsigned long long bucket_visits = 0;
	};

	ui rr1_budget_csr_member_epoch_counter;
	ui rr1_budget_csr_seen_epoch_counter;
	vector<ui> rr1_budget_csr_member_epoch;
	vector<ui> rr1_budget_csr_seen_epoch;
	vector<ui> rr1_budget_csr_bucket_by_vertex;
	vector<unsigned char> rr1_budget_csr_state;
	vector<ui> rr1_budget_csr_future_count;
	vector<ui> rr1_budget_csr_kept_count;
	vector<ui> rr1_budget_csr_future_suffix;
	vector<ui> rr1_budget_csr_kept_suffix;
	vector<ui> rr1_budget_csr_adjacent_count;

	static const unsigned long long MAX_CSR_SCRATCH_BYTES = ARCSCSMemoryLimits::auxiliary_bytes;

	bool ledger_probe_due(unsigned long long cost, unsigned long long credit,
		unsigned long long runs, unsigned long long &skips,
		unsigned long long interval)
	{
		if (runs == static_cast<unsigned long long>(0) || credit >= cost)
			return true;
		++skips;
		return skips >= interval;
	}

	void ledger_probe_started(unsigned long long cost,
		unsigned long long &credit, unsigned long long &runs,
		unsigned long long &skips)
	{
		credit = credit > cost ? credit - cost : 0ull;
		++runs;
		skips = 0;
	}

	void ledger_probe_finished(bool hit, unsigned long long benefit,
		unsigned long long &credit, unsigned long long runs,
		unsigned long long &interval)
	{
		if (hit)
		{
			credit = std::numeric_limits<unsigned long long>::max() - credit < benefit
				? std::numeric_limits<unsigned long long>::max() : credit + benefit;
			interval = 1;
		}
		else if (runs > static_cast<unsigned long long>(1))
			interval = interval > std::numeric_limits<unsigned long long>::max() / 2
				? std::numeric_limits<unsigned long long>::max() : interval * 2;
	}

public:
	MBBPS()
	{
		n = 0;
		edges_cap = 0;
		pstart = NULL;
		pend = NULL;
		edges = NULL;
		degree = degree_in_S = NULL;

		best_solution = NULL;
		S = optimal_sol_size = _size_UB_ = 0;

		SR = SR_rid = NULL;
		level_id = NULL;

		neighbors = nonneighbors = NULL;
		buf = buf1 = buf2 = NULL;
		vis = NULL;

		pair_ledger_runs = pair_ledger_skips = triple_ledger_runs = triple_ledger_skips = 0;
		pair_probe_interval = triple_probe_interval = 1;
		pair_last_candidate_count = std::numeric_limits<ui>::max();

		fallback_uism_active = false;

		search_node_limit = 0;
		search_nodes_visited = 0;
		search_node_limit_exhausted = false;

		work_adaptive_total_work = 0;
		work_adaptive_total_removed = 0;
		work_adaptive_search_credit = 0;
		work_adaptive_removal_benefit = 0;

		work_adaptive_total_runs = 0;
		work_adaptive_initial_total_work = 0;
		work_adaptive_initial_total_removed = 0;
		work_adaptive_initial_search_credit = 0;
		work_adaptive_initial_removal_benefit = 0;
		work_adaptive_initial_total_runs = 0;
		work_adaptive_initial_probe_interval = 1;
		work_adaptive_skips_since_probe = 0;
		work_adaptive_probe_interval = 1;
		work_adaptive_forced_probe = false;

		rr1_budget_csr_member_epoch_counter = 0;
		rr1_budget_csr_seen_epoch_counter = 0;

		stats.reset();
	}

	~MBBPS()
	{
		if (pstart != NULL)
		{
			delete[] pstart;
			pstart = NULL;
		}
		if (pend != NULL)
		{
			delete[] pend;
			pend = NULL;
		}
		if (edges != NULL)
		{
			delete[] edges;
			edges = NULL;
		}
		if (degree != NULL)
		{
			delete[] degree;
			degree = NULL;
		}
		if (degree_in_S != NULL)
		{
			delete[] degree_in_S;
			degree_in_S = NULL;
		}
		if (best_solution != NULL)
		{
			delete[] best_solution;
			best_solution = NULL;
		}
		if (SR != NULL)
		{
			delete[] SR;
			SR = NULL;
		}
		if (SR_rid != NULL)
		{
			delete[] SR_rid;
			SR_rid = NULL;
		}
		if (level_id != NULL)
		{
			delete[] level_id;
			level_id = NULL;
		}
		if (neighbors != NULL)
		{
			delete[] neighbors;
			neighbors = NULL;
		}
		if (nonneighbors != NULL)
		{
			delete[] nonneighbors;
			nonneighbors = NULL;
		}
		if (buf != NULL)
		{
			delete[] buf;
			buf = NULL;
		}
		if (buf1 != NULL)
		{
			delete[] buf1;
			buf1 = NULL;
		}
		if (buf2 != NULL)
		{
			delete[] buf2;
			buf2 = NULL;
		}
		if (vis != NULL)
		{
			delete[] vis;
			vis = NULL;
		}
	}

	void allocateMemory(ui n)
	{
		if (n <= 0u)
			return;
		pstart = new ept[n + 1];
		pend = new ept[n + 1];
		edges = new ui[1];
		edges_cap = 1;

		degree = new ui[n + 1];
		degree_in_S = new ui[n + 1];
		best_solution = new ui[n + 1];
		SR = new ui[n + 1];
		SR_rid = new ui[n + 1];
		neighbors = new ui[n + 1];
		nonneighbors = new ui[n + 1];
		level_id = new ui[n + 1];

		buf = new ui[n + 1];
		buf1 = new ui[n + 1];
		buf2 = new ui[n + 1];
		vis = new char[n + 1];
	}

	void set_adaptive_triple_capacity_bound(ui max_dp_states)
	{
		if (max_dp_states == 0u)
		{
			fprintf(stderr, "MBBPS triple-capacity bound max DP states must be positive\n");
			exit(1);
		}

	}

	void set_automatic_work_ledger()
	{

		work_ledger = ARCWorkLedger();
		pair_ledger_runs = pair_ledger_skips = triple_ledger_runs = triple_ledger_skips = 0;
		pair_probe_interval = triple_probe_interval = 1;
		pair_last_candidate_count = std::numeric_limits<ui>::max();
	}

	void set_search_node_limit(unsigned long long limit)
	{
		search_node_limit = limit;
	}

	bool was_search_node_limit_exhausted() const
	{
		return search_node_limit_exhausted;
	}

	unsigned long long get_search_nodes_visited() const
	{
		return search_nodes_visited;
	}

	void set_work_adaptive_initial_totals(unsigned long long work_ops,
		unsigned long long removed_vertices, unsigned long long search_credit,
		unsigned long long removal_benefit, unsigned long long run_count,
		ui probe_interval)
	{
		work_adaptive_initial_total_work = work_ops;
		work_adaptive_initial_total_removed = removed_vertices;
		work_adaptive_initial_search_credit = search_credit;
		work_adaptive_initial_removal_benefit = removal_benefit;
		work_adaptive_initial_total_runs = run_count;
		work_adaptive_initial_probe_interval = probe_interval == 0u ? 1 :
			probe_interval;
	}

	void reset_stats()
	{
		stats.reset();

	}

	inline bool adjacency_scan_continues(ept pos, ept end, ui level) const
	{
		return pos < end &&
			(fallback_uism_active || level_id[edges[pos]] >= level);
	}

	inline bool adjacency_edge_is_visible()
	{
		if (!fallback_uism_active)
			return true;

		return true;
	}

	inline void uism_swap_edge_entries(ept a, ept b)
	{
		if (a == b)
			return;
		swap(edges[a], edges[b]);
		swap(uism_reverse_edge[a], uism_reverse_edge[b]);
		uism_reverse_edge[uism_reverse_edge[a]] = a;
		uism_reverse_edge[uism_reverse_edge[b]] = b;
	}

	bool fallback_uism_root_work_gate(unsigned long long directed_edges)
	{
		// UISM's reversible active-row maintenance amortizes only when the
		// target is at least as cohesive as the missing-edge allowance:
		// target_k = target_size - S >= S. AQER now certifies the formerly
		// expensive high-k trials before fallback, so the remaining S>k trials
		// are shallow and cannot repay an O(n+m) incremental-state setup.
		// Failing this gate selects the established exact fallback backend and
		// therefore changes performance only, never feasibility or the answer.
		const bool cohesion_pass =
			2ull * (unsigned long long)S <=
				(unsigned long long)UB_size;

		if (!cohesion_pass)
			return false;

		// Read-only simulation of the root degree/core peeling.  It predicts the
		// work of the reduced state without touching SR, CSR row order, pend, or
		// any recursive-search state.  Large estimates fail closed.
		//
		// The simulation itself is O(n+m), so first reject raw states whose mean
		// row density is below twice the current missing-edge budget S.  Such
		// sparse inputs cannot amortize a second full-graph pass before the real
		// root reductions.  This is a query-structural cost gate only: rejecting
		// it selects the scalar exact backend and cannot change the answer.
		const unsigned long long min_raw_directed_edges =
			2ull * (unsigned long long)S * (unsigned long long)n;
		const bool raw_density_pass = directed_edges >= min_raw_directed_edges;

		if (!raw_density_pass)
			return false;

		const unsigned long long max_gate_bytes = ARCSCSMemoryLimits::auxiliary_bytes;
		const unsigned long long gate_bytes = (unsigned long long)n *
			(4ull * sizeof(ui) + sizeof(unsigned char));
		if (gate_bytes > max_gate_bytes)
			return false;

		vector<ui> work_degree(n);
		vector<ui> peel_queue;
		vector<unsigned char> removed(n, 0);
		peel_queue.reserve(n);
		for (ui u = 0; u < n; ++u)
		{
			work_degree[u] = pstart[u + 1] - pstart[u];
			if (work_degree[u] + S <= optimal_sol_size)
			{
				removed[u] = 1;
				peel_queue.push_back(u);
			}
		}
		for (size_t head = 0; head < peel_queue.size(); ++head)
		{
			ui u = peel_queue[head];
			for (ept pos = pstart[u]; pos < pstart[u + 1]; ++pos)
			{
				ui v = edges[pos];
				if (removed[v])
					continue;
				assert(work_degree[v] > 0);
				--work_degree[v];
				if (work_degree[v] + S <= optimal_sol_size)
				{
					removed[v] = 1;
					peel_queue.push_back(v);
				}
			}
		}

		if (query_vertex_global < 0 || (ui)query_vertex_global >= n ||
			removed[(ui)query_vertex_global])
			return false;

		// Root initialization immediately fixes the query vertex in S and applies
		// the distance reduction.  This is the dominant shrink on web-like graphs,
		// so simulate the same bounded BFS and subsequent degree cascade read-only.
		if (2 * S <= optimal_sol_size)
			return false;
		const ui dist_limit = 2 * S - optimal_sol_size;
		vector<ui> dist(n, n);
		vector<ui> bfs_queue;
		bfs_queue.reserve(n);
		while (true)
		{
			fill(dist.begin(), dist.end(), n);
			bfs_queue.clear();
			ui query = (ui)query_vertex_global;
			dist[query] = 0;
			bfs_queue.push_back(query);
			for (size_t head = 0; head < bfs_queue.size(); ++head)
			{
				ui u = bfs_queue[head];
				if (dist[u] >= dist_limit)
					continue;
				for (ept pos = pstart[u]; pos < pstart[u + 1]; ++pos)
				{
					ui v = edges[pos];
					if (!removed[v] && dist[v] == n)
					{
						dist[v] = dist[u] + 1;
						bfs_queue.push_back(v);
					}
				}
			}

			size_t wave_begin = peel_queue.size();
			for (ui u = 0; u < n; ++u)
				if (!removed[u] && dist[u] > dist_limit)
				{
					removed[u] = 1;
					peel_queue.push_back(u);
				}
			if (peel_queue.size() == wave_begin)
				break;
			for (size_t head = wave_begin; head < peel_queue.size(); ++head)
			{
				ui u = peel_queue[head];
				for (ept pos = pstart[u]; pos < pstart[u + 1]; ++pos)
				{
					ui v = edges[pos];
					if (removed[v])
						continue;
					assert(work_degree[v] > 0);
					--work_degree[v];
					if (work_degree[v] + S <= optimal_sol_size)
					{
						removed[v] = 1;
						peel_queue.push_back(v);
					}
				}
			}
			if (removed[query])
				return false;
		}
		unsigned long long active_vertices = 0;
		unsigned long long active_edges = 0;
		for (ui u = 0; u < n; ++u)
			if (!removed[u])
			{
				++active_vertices;
				active_edges += work_degree[u];
			}
		// Two-sided work model: sparse states cannot amortize active-row
		// maintenance, while very large active edge sets make the reversible
		// trail itself dominate.  The cap is expressed in predicted edge
		// operations, not dataset identity or query size.
		static const unsigned long long MAX_PREDICTED_ACTIVE_EDGES = 12000000ull;
		bool pass = active_vertices >= static_cast<unsigned long long>(4096) &&
			active_edges >= 20ull * active_vertices &&
			active_edges <= MAX_PREDICTED_ACTIVE_EDGES;

		return pass;
	}

	bool prepare_fallback_uism_backend()
	{
		fallback_uism_active = false;
		uism_reverse_edge.clear();
		uism_edge_swap_trail.clear();
		uism_removal_trail.clear();
		if (n < 4096u)
			return false;

		const unsigned long long directed_edges = pstart[n];
		const unsigned long long MAX_REVERSE_EDGE_BYTES = ARCSCSMemoryLimits::auxiliary_bytes;
		if (directed_edges > MAX_REVERSE_EDGE_BYTES / sizeof(ept))
			return false;
		if (!fallback_uism_root_work_gate(directed_edges))
			return false;

		// A reciprocal position is well-defined only for a simple undirected CSR.
		// Rows are normally sorted by the graph converter. Reject rather than
		// silently changing semantics when a row is unsorted, duplicated, has an
		// invalid endpoint/self-loop, or lacks its reciprocal entry.
		//
		// Build the reciprocal map in O(n+m), rather than binary-searching every
		// directed edge. For a fixed row v, lower endpoint u values arrive in
		// increasing order as the outer loop advances, so reciprocal_cursor[v]
		// only moves forward. This preserves the exact validation contract of the
		// previous implementation while removing its O(m log d) setup cost.
		Timer validation_timer;
		for (ui u = 0; u < n; ++u)
		{
			for (ept j = pstart[u]; j < pstart[u + 1]; ++j)
			{
				if (edges[j] >= n || edges[j] == u ||
					(j > pstart[u] && edges[j - 1] >= edges[j]))
					return false;
			}
		}

		Timer reciprocal_timer;
		const ept invalid_position = std::numeric_limits<ept>::max();
		uism_reverse_edge.assign((size_t)directed_edges, std::numeric_limits<ept>::max());
		vector<ept> reciprocal_cursor(n);
		for (ui u = 0; u < n; ++u)
			reciprocal_cursor[u] = pstart[u];
		for (ui u = 0; u < n; ++u)
		{
			for (ept j = pstart[u]; j < pstart[u + 1]; ++j)
			{
				ui v = edges[j];
				if (v < u)
				{
					if (uism_reverse_edge[j] == invalid_position)
					{
						uism_reverse_edge.clear();
						return false;
					}
					continue;
				}
				ept &cursor = reciprocal_cursor[v];
				while (cursor < pstart[v + 1] && edges[cursor] < u)
					++cursor;
				if (cursor == pstart[v + 1] || edges[cursor] != u ||
					uism_reverse_edge[j] != invalid_position ||
					uism_reverse_edge[cursor] != invalid_position)
				{
					uism_reverse_edge.clear();
					return false;
				}
				uism_reverse_edge[j] = cursor;
				uism_reverse_edge[cursor] = j;
				++cursor;
			}
		}

		fallback_uism_active = true;
		return true;
	}

	void record_fallback_uism_root(ui R_end)
	{
		unsigned long long active_edges = 0;
		unsigned long long csr_edges = 0;
		for (ui i = 0; i < R_end; ++i)
		{
			ui u = SR[i];
			active_edges += degree[u];
			csr_edges += (unsigned long long)(pstart[u + 1] - pstart[u]);
		}

	}

	void uism_begin_vertex_removal(ui u)
	{
		UISMRemovalFrame frame = {u, uism_edge_swap_trail.size()};
		uism_removal_trail.push_back(frame);
	}

	void uism_remove_edge_from_active_row(ui row, ept reciprocal_position)
	{
		assert(fallback_uism_active);
		assert(reciprocal_position >= pstart[row] && reciprocal_position < pend[row]);
		ept last = --pend[row];
		UISMEdgeSwap entry = {row, reciprocal_position, last};
		uism_edge_swap_trail.push_back(entry);
		uism_swap_edge_entries(reciprocal_position, last);
	}

	void uism_restore_last_removed_vertex(ui u)
	{
		(void)u; // Used by the restoration invariant.
		assert(fallback_uism_active && !uism_removal_trail.empty());
		UISMRemovalFrame frame = uism_removal_trail.back();
		assert(frame.vertex == u);
		while (uism_edge_swap_trail.size() > frame.swap_begin)
		{
			UISMEdgeSwap entry = uism_edge_swap_trail.back();
			uism_edge_swap_trail.pop_back();
			assert(pend[entry.row] == entry.last);
			uism_swap_edge_entries(entry.position, entry.last);
			++pend[entry.row];
			++degree[entry.row];
		}
		uism_removal_trail.pop_back();
	}

	void reset_adaptive_budget_state()
	{

		work_adaptive_total_work = work_adaptive_initial_total_work;
		work_adaptive_total_removed = work_adaptive_initial_total_removed;
		work_adaptive_search_credit = work_adaptive_initial_search_credit;
		work_adaptive_removal_benefit = work_adaptive_initial_removal_benefit;
		work_adaptive_total_runs = work_adaptive_initial_total_runs;
		work_adaptive_skips_since_probe = 0;
		work_adaptive_probe_interval = work_adaptive_initial_probe_interval;
		work_adaptive_forced_probe = false;

	}

	const SearchStats &get_stats() const
	{
		return stats;
	}

	void load_graph(ui _n, const vector<pair<ui, ui>> &vp)
	{
		n = _n;
		if (vp.size() * 2 > edges_cap)
		{
			do
			{
				edges_cap *= 2;
			} while (vp.size() * 2 > edges_cap);
			delete[] edges;
			edges = new ui[edges_cap];
		}
		for (ui i = 0; i < n; i++)
			degree[i] = 0;
		for (ept i = 0; i < vp.size(); i++)
		{
			assert(vp[i].first < n && vp[i].second < n);
			++degree[vp[i].first];
			++degree[vp[i].second];
		}
		for (ui i = 1; i < n; i++)
		{
			degree[i] += degree[i - 1];
			pstart[i] = degree[i - 1];
		}
		pstart[0] = 0;
		for (ept i = 0; i < vp.size(); i++)
		{
			ui a = vp[i].first, b = vp[i].second;
			edges[pstart[a]++] = b;
			edges[pstart[b]++] = a;
		}
		for (ui i = n; i > 0u; i--)
			pstart[i] = pstart[i - 1];
		pstart[0] = 0;
	}

	void load_graph(ui n_, ui *_pstart, ui *_pend, ui *_edges)
	{
		ept m = 0;
		n = n_;
		for (ui i = 0; i < n; i++)
			m += _pend[i] - _pstart[i];
		if (m > edges_cap)
		{
			do
			{
				edges_cap *= 2;
			} while (m > edges_cap);
			delete[] edges;
			edges = new ui[edges_cap];
		}

		m = 0;
		for (ui i = 0; i < n; i++)
		{
			pstart[i] = m;
			for (ept j = _pstart[i]; j < _pend[i]; j++)
			{
				assert(_edges[j] < n);
				edges[m++] = _edges[j];
			}
		}
		pstart[n] = m;

	}

	void find_feasible(ui S_, ui size_UB_, vector<ui> &feasible_solution, bool must_include_0, int _query_vertex, int _UB_size)
	{
		(void)must_include_0; // The sparse backend requires an explicit query vertex.
		reset_stats();
		search_nodes_visited = 0;
		search_node_limit_exhausted = false;

			reset_adaptive_budget_state();

		assert(must_include_0 == false);
		S = S_;
		_size_UB_ = size_UB_;
		optimal_sol_size = feasible_solution.size();
		ui S_end = 0, R_end = n;
		query_vertex_global = _query_vertex;
		UB_size = _UB_size;

		prepare_fallback_uism_backend();
		initialization(S_end, R_end);

		assert(S_end == 1);
		record_fallback_uism_root(R_end);

		try
		{
			if (R_end && optimal_sol_size < _size_UB_)
				BB_search(S_end, R_end, 1);
		}
		catch (const SearchNodeBudgetExhausted &)
		{
			search_node_limit_exhausted = true;
		}
		if (optimal_sol_size > feasible_solution.size())
		{
			feasible_solution.clear();
			for (int i = 0; static_cast<ui>(i) < optimal_sol_size; i++)
				feasible_solution.push_back(best_solution[i]);
		}
	}

private:
	bool adaptive_budget_tracking_enabled() const
	{
		return true;
	}

	void initialization(ui &S_end, ui &R_end)
	{
		memset(vis, 0, sizeof(char) * (n + 1));
		memset(degree_in_S, 0, sizeof(ui) * (n + 1));
		for (ui i = 0; i < n; i++)
			level_id[i] = n;
		for (ui i = 0; i < n; i++)
			SR[i] = SR_rid[i] = i;
		for (ui i = 0; i < n; i++)
			pend[i] = pstart[i + 1];
		while (!Qv.empty())
			Qv.pop();

		for (ui i = 0; i < n; i++)
		{
			degree[i] = pstart[i + 1] - pstart[i];
			if (degree[i] + S <= optimal_sol_size)
			{
				if (i == static_cast<ui>(query_vertex_global))
				{
					R_end = 0;
					printf("Sorry! But the query vertex has been removed from the graph due to core reduction! \n");
					return;
				}
				level_id[i] = 0;
				Qv.push(i);
			}
		}

		remove_vertices_with_prune(S_end, R_end, 0);
		if (level_id[query_vertex_global] == 0u)
		{
			R_end = 0;
			return;
		}
		assert(S_end == 0);

		if (!move_u_to_S_with_prune(query_vertex_global, S_end, R_end, 0) || !delete_vertices_based_on_dist(S_end, R_end, 0))
		{
			R_end = 0;
			return;
		}
		assert(S_end == 1);
	}

	void reorganize_edges(ui R_end, ui level)
	{
		Timer reorganize_timer;
		unsigned long long scanned_edges = 0;
		assert(level > 0);
		for (ui i = 0; i < R_end; i++)
		{
			ui u = SR[i];
			ui non_neighbors_n = 0, end = pstart[u];
			for (ui j = pstart[u]; j < pend[u] && level_id[edges[j]] >= level - 1; j++)
			{
				++scanned_edges;
				assert(level_id[edges[j]] == level - 1 || level_id[edges[j]] == n);
				if (level_id[edges[j]] >= level)
					edges[end++] = edges[j];
				else
					nonneighbors[non_neighbors_n++] = edges[j];
			}
			assert(degree[u] == end - pstart[u]);
			for (ui j = 0; j < non_neighbors_n; j++)
				edges[end++] = nonneighbors[j];
			assert((end < pend[u] && level_id[edges[end]] < level - 1) || end == pend[u]);
#ifndef NDEBUG
			for (ui j = end; j < pend[u]; j++)
			{
				if (level_id[edges[j]] >= level)
					printf("removed_level[edges[j]]: %u, level: %u\n", level_id[edges[j]], level);
				assert(level_id[edges[j]] < level);
			}
#endif
		}

	}

	void store_solution(ui size, bool is_R_end, ui level)
	{
		if (size <= optimal_sol_size)
		{
			printf("!!! the solution to store is no larger than the current best solution!");
			return;
		}

		char *matrix = new char[size * size]{};
		for (ui i = 0; i < size; i++)
		{
			ui t_u = SR[i];
			for (ui j = pstart[t_u]; adjacency_scan_continues(j, pend[t_u], level); j++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				for (ui k = i + 1; k < size; k++)
					if (edges[j] == SR[k])
						matrix[k * size + i] = matrix[i * size + k] = 1;
			}
		}

		if (is_R_end)
		{
			vector<bool> visited(size, false);
			function<void(int)> dfs = [&](int vertex)
			{
				visited[vertex] = true;
				for (int i = 0; static_cast<ui>(i) < size; ++i)
					if (matrix[vertex * size + i] && !visited[i])
						dfs(i);
			};

			assert(SR[0] == static_cast<ui>(query_vertex_global));
			dfs(0);

			vector<ui> t_solution;
			vector<ui> t_indices;
			for (int i = 0; static_cast<ui>(i) < size; i++)
				if (visited[i])
				{
					t_solution.push_back(SR[i]);
					t_indices.push_back(i);
				}

			// R may be a feasible connected super-set of the requested UB.  Delete
			// non-query DFS leaves until it fits.  Connectivity and S-plex
			// feasibility are hereditary under this deletion.
			while (t_indices.size() > _size_UB_)
			{
				vector<int> order;
				vector<char> seen(t_indices.size(), 0);
				vector<int> stack(1, 0);
				seen[0] = 1;
				while (!stack.empty())
				{
					int u = stack.back();
					stack.pop_back();
					order.push_back(u);
					for (int v = (int)t_indices.size() - 1; v >= 0; --v)
						if (!seen[v] && matrix[t_indices[u] * size + t_indices[v]])
						{
							seen[v] = 1;
							stack.push_back(v);
						}
				}
				assert(order.size() == t_indices.size());
				assert(order.back() != 0);
				t_indices.erase(t_indices.begin() + order.back());
				t_solution.erase(t_solution.begin() + order.back());
			}

			if (t_solution.size() > optimal_sol_size)
			{
				optimal_sol_size = t_solution.size();
				for (ui i = 0; i < optimal_sol_size; i++)
					best_solution[i] = t_solution[i];
			}
		}
		else
		{
			vector<bool> visited(size, false);
			function<void(int)> dfs = [&](int vertex)
			{
				visited[vertex] = true;
				for (int i = 0; static_cast<ui>(i) < size; i++)
					if (matrix[vertex * size + i] && !visited[i])
						dfs(i);
			};

			dfs(0);
			bool is_connected = true;

			for (int i = 0; static_cast<ui>(i) < size; i++)
				if (!visited[i])
					is_connected = false;

			if (is_connected)
			{
				assert(size <= _size_UB_);
				assert(size > optimal_sol_size);
				optimal_sol_size = size;
				for (ui i = 0; i < optimal_sol_size; i++)
					best_solution[i] = SR[i];
			}
		}
		delete[] matrix;
		assert(optimal_sol_size <= _size_UB_);

	}

	bool is_desired_feasible_sol(ui R_end)
	{
		for (ui i = 0; i < R_end; i++)
			if (degree[SR[i]] + S < R_end)
				return false;
		return true;
	}

	// Exact two-selected-vertex capacity upper bound (EPCUB), using the
	// fallback solver's sparse CSR adjacency.  This is the same relaxation as
	// the packed-row Matrix backend; only the common-neighbor counting backend
	// differs.
	bool adaptive_triple_capacity_bound_prunes(ui S_end, ui R_end, ui level,
											 ui best_u, ui best_v, ui best_w,
											 ui pair_node_ub, ui call_site)
	{
		(void)pair_node_ub; // Checked by the bound invariant.
		if ((best_w == n) || (S_end < 3u))
			return false;

		const bool full_row_scan = call_site == 3u;
		unsigned long long row_edges = full_row_scan
			? (unsigned long long)(pend[best_u] - pstart[best_u]) +
				  (pend[best_v] - pstart[best_v]) +
				  (pend[best_w] - pstart[best_w])
			: (unsigned long long)degree[best_u] + degree[best_v] + degree[best_w];
		unsigned long long estimated_edges = 2ull * row_edges;
		ui budgets[3] = {
			S + degree_in_S[best_u] - S_end,
			S + degree_in_S[best_v] - S_end,
			S + degree_in_S[best_w] - S_end};
		const unsigned long long dp_state_work =
			(unsigned long long)(budgets[0] + 1ull) *
			(unsigned long long)(budgets[1] + 1ull) *
			(unsigned long long)(budgets[2] + 1ull);
		bool triple_work_skip = false;
		{
			const bool funded = work_ledger.edge_scan_credit >= estimated_edges &&
				work_ledger.dp_state_credit >= dp_state_work;
			if (triple_ledger_runs != static_cast<unsigned long long>(0) && !funded)
			{
				++triple_ledger_skips;
				triple_work_skip = triple_ledger_skips < triple_probe_interval;
			}
		}
		if (triple_work_skip)
		{

			return false;
		}
		{
			work_ledger.edge_scan_credit = work_ledger.edge_scan_credit > estimated_edges
				? work_ledger.edge_scan_credit - estimated_edges : 0ull;
			work_ledger.dp_state_credit = work_ledger.dp_state_credit > dp_state_work
				? work_ledger.dp_state_credit - dp_state_work : 0ull;
			++triple_ledger_runs;
			triple_ledger_skips = 0;
		}

		Timer bound_timer;

		ui counts[8] = {0, 0, 0, 0, 0, 0, 0, 0};
		ui selected[3] = {best_u, best_v, best_w};
		ui union_n = 0;
		for (ui row = 0; row < 3u; ++row)
		{
			ui u = selected[row];
			for (ept j = pstart[u];
				 j < pend[u] && (full_row_scan || fallback_uism_active || level_id[edges[j]] >= level); ++j)
			{
				if (!full_row_scan && !adjacency_edge_is_visible())
					continue;
				ui candidate = edges[j];
				if (SR_rid[candidate] < S_end || SR_rid[candidate] >= R_end)
					continue;
				if (vis[candidate] == 0)
					buf[union_n++] = candidate;
				vis[candidate] |= (char)(1u << row);
			}
		}
		for (ui i = 0; i < union_n; ++i)
		{
			ui candidate = buf[i];
			ui adjacent_mask = (ui)vis[candidate] & 7u;
			ui miss_mask = (~adjacent_mask) & 7u;
			++counts[miss_mask];
			vis[candidate] = 0;
		}
		ui C_size = R_end - S_end;
		assert(union_n <= C_size);
		counts[7] = C_size - union_n;

		CapacityBound::TripleResult result;
		const ui exact_state_limit = (std::numeric_limits<ui>::max());
		if (!CapacityBound::exact_triple_relaxation(
				counts, budgets, exact_state_limit, result))
		{

			return false;
		}

		ui node_ub = S_end + result.upper_bound;
		assert(node_ub <= pair_node_ub);
		bool hit = node_ub <= optimal_sol_size;
		if (hit)
		{

			if (stats.triple_capacity_bound_hit_C_max < C_size)
				stats.triple_capacity_bound_hit_C_max = C_size;
		}
		{
			if (hit)
			{
				work_ledger.edge_scan_credit += estimated_edges;
				work_ledger.dp_state_credit += result.dp_states;
				triple_probe_interval = 1;
			}
			else if (triple_ledger_runs > static_cast<unsigned long long>(1))
				triple_probe_interval = triple_probe_interval >
					std::numeric_limits<unsigned long long>::max() / 2
					? std::numeric_limits<unsigned long long>::max()
					: triple_probe_interval * 2;
		}

		return (hit) && call_site == 3u;
	}

	bool pair_capacity_bound_prunes(ui S_end, ui R_end, ui level, ui call_site,
									 bool *deferred_triple_prune = nullptr)
	{
		if (deferred_triple_prune != nullptr)
			*deferred_triple_prune = false;
		if ((S_end < 2u) || (R_end <= S_end))
			return false;

		ui best_u = n, best_v = n, best_w = n;
		ui best_u_ub = UINT_MAX, best_v_ub = UINT_MAX, best_w_ub = UINT_MAX;
		for (ui i = 0; i < S_end; ++i)
		{
			ui u = SR[i];
			assert(degree[u] >= degree_in_S[u]);
			assert(S + degree_in_S[u] >= S_end);
			ui budget = S + degree_in_S[u] - S_end;
			ui neighbors_in_C = degree[u] - degree_in_S[u];
			ui single_ub = neighbors_in_C + budget;
			if (single_ub < best_u_ub)
			{
				best_w = best_v;
				best_w_ub = best_v_ub;
				best_v = best_u;
				best_v_ub = best_u_ub;
				best_u = u;
				best_u_ub = single_ub;
			}
			else if (single_ub < best_v_ub)
			{
				best_w = best_v;
				best_w_ub = best_v_ub;
				best_v = u;
				best_v_ub = single_ub;
			}
			else if (single_ub < best_w_ub)
			{
				best_w = u;
				best_w_ub = single_ub;
			}
		}
		assert(best_u != n && best_v != n);

		const bool full_row_scan = call_site == 3u;
		// Mark the lower-cost row so clearing it costs as little as possible.
		ui mark_u = best_u, scan_v = best_v;
		auto row_scan_size = [&](ui u) -> unsigned long long {
			return full_row_scan ? (unsigned long long)(pend[u] - pstart[u])
							  : (unsigned long long)degree[u];
		};
		if (row_scan_size(mark_u) > row_scan_size(scan_v))
			swap(mark_u, scan_v);
		unsigned long long estimated_edges =
			2ull * row_scan_size(mark_u) + row_scan_size(scan_v);
		const ui current_candidate_count = R_end - S_end;
		if (current_candidate_count != pair_last_candidate_count)
		{
			pair_last_candidate_count = current_candidate_count;
			pair_probe_interval = 1;
			pair_ledger_skips = 0;
		}
		const bool pair_work_skip = (!ledger_probe_due(estimated_edges, work_ledger.edge_scan_credit,
				pair_ledger_runs, pair_ledger_skips, pair_probe_interval));
		if (pair_work_skip)
		{

			return false;
		}
		{ ledger_probe_started(estimated_edges, work_ledger.edge_scan_credit,
				pair_ledger_runs, pair_ledger_skips); }

		Timer bound_timer;

		ui common_neighbors = 0;
		for (ept j = pstart[mark_u];
			 j < pend[mark_u] && (full_row_scan || fallback_uism_active || level_id[edges[j]] >= level); ++j)
		{
			if (!full_row_scan && !adjacency_edge_is_visible())
				continue;
			ui w = edges[j];
			if (SR_rid[w] >= S_end && SR_rid[w] < R_end)
				vis[w] = 1;
		}
		for (ept j = pstart[scan_v];
			 j < pend[scan_v] && (full_row_scan || fallback_uism_active || level_id[edges[j]] >= level); ++j)
		{
			if (!full_row_scan && !adjacency_edge_is_visible())
				continue;
			ui w = edges[j];
			if (SR_rid[w] >= S_end && SR_rid[w] < R_end && vis[w])
				++common_neighbors;
		}
		for (ept j = pstart[mark_u];
			 j < pend[mark_u] && (full_row_scan || fallback_uism_active || level_id[edges[j]] >= level); ++j)
		{
			if (!full_row_scan && !adjacency_edge_is_visible())
				continue;
			ui w = edges[j];
			if (SR_rid[w] >= S_end && SR_rid[w] < R_end)
				vis[w] = 0;
		}

		ui budget_u = S + degree_in_S[best_u] - S_end;
		ui budget_v = S + degree_in_S[best_v] - S_end;
		ui neighbors_u = degree[best_u] - degree_in_S[best_u];
		ui neighbors_v = degree[best_v] - degree_in_S[best_v];
		ui C_size = R_end - S_end;
		assert(common_neighbors <= neighbors_u && common_neighbors <= neighbors_v);
		assert(neighbors_u + neighbors_v >= common_neighbors);
		assert(neighbors_u + neighbors_v - common_neighbors <= C_size);

		ui only_miss_u = neighbors_v - common_neighbors;
		ui only_miss_v = neighbors_u - common_neighbors;
		ui miss_both = C_size - neighbors_u - neighbors_v + common_neighbors;
		ui take_only_u = min(only_miss_u, budget_u);
		ui take_only_v = min(only_miss_v, budget_v);
		ui take_both = min(miss_both,
						   min(budget_u - take_only_u, budget_v - take_only_v));
		ui extension_ub = common_neighbors + take_only_u + take_only_v + take_both;
		ui node_ub = S_end + extension_ub;
		bool hit = node_ub <= optimal_sol_size;
		if (hit)
		{

			ui gap = optimal_sol_size - node_ub;

			if (stats.pair_capacity_bound_gap_max < gap)
				stats.pair_capacity_bound_gap_max = gap;

			if (stats.pair_capacity_bound_hit_C_max < C_size)
				stats.pair_capacity_bound_hit_C_max = C_size;
		}
		else
		{
			ui excess = node_ub - optimal_sol_size;

			if (stats.pair_capacity_bound_excess_min > excess)
				stats.pair_capacity_bound_excess_min = excess;

		}
		{ ledger_probe_finished(hit, C_size,
				work_ledger.edge_scan_credit, pair_ledger_runs,
				pair_probe_interval); }

		bool triple_prunes = false;
		if (!hit && node_ub == optimal_sol_size + 1)
			triple_prunes = adaptive_triple_capacity_bound_prunes(
				S_end, R_end, level, best_u, best_v, best_w, node_ub, call_site);
		// A formal Fallback ATCUB hit is mathematically safe at node entry, but
		// returning before reorganize_edges() skips the persistent CSR ordering
		// side effect that sibling branches would otherwise inherit.  Defer only
		// that return until the caller has performed the baseline reorganization.
		// Low-slack trials (including the established [9,12] workload where
		// S <= 8) retain the admitted immediate-prune path.  The deferred path is
		// limited to the high-slack regime where persistent CSR order dominates
		// subsequent RR1 work, as exposed by Google q8518 at S=16.
		// EPCUB and every observational/late call site keep their existing policy.
		const bool high_slack_order_risk = S >= 12u;
		if (triple_prunes && call_site == 3u && deferred_triple_prune != nullptr &&
			high_slack_order_risk)
		{
			*deferred_triple_prune = true;
			triple_prunes = false;
		}
		return ((hit) && call_site == 3u) || triple_prunes;
	}

	void BB_search(ui S_end, ui R_end, ui level)
	{
		if (search_node_limit != static_cast<unsigned long long>(0) && search_nodes_visited >= search_node_limit)
			throw SearchNodeBudgetExhausted();
		++search_nodes_visited;

		// This node has not rebuilt the current-level row prefix yet. Level 0
		// keeps the established scan loop running to pend, so a just-removed
		// neighbor cannot hide later active neighbors during connectivity.
		const ui pre_reorder_solution_scan_level = 0;
		if (S_end > optimal_sol_size)
			store_solution(S_end, false, pre_reorder_solution_scan_level);
		if (R_end > optimal_sol_size && is_desired_feasible_sol(R_end))
		{
			store_solution(R_end, true, pre_reorder_solution_scan_level);
			return;
		}
		if (R_end <= optimal_sol_size + 1 || optimal_sol_size >= _size_UB_)
			return;

		// The formal certificates run at the node entry, before this node performs
		// propagation or reorganize_edges().  Pruning can still skip a reorder that
		// would have influenced a later equivalent branch, but it cannot interrupt
		// an in-progress reversible update.  Site 3 therefore uses full CSR rows.
		bool deferred_triple_prune = false;
		if (pair_capacity_bound_prunes(S_end, R_end, level, 3,
										&deferred_triple_prune))
			return;

		ui old_S_end = S_end, old_R_end = R_end;
		assert(Qv.empty());

		if (level >= 1u && !fallback_uism_active)
			reorganize_edges(R_end, level);
		// No reversible propagation has started yet.  Returning here preserves
		// the exact ATCUB certificate while retaining the baseline CSR order for
		// subsequent sibling branches.
		if (deferred_triple_prune)
			return;

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui u = SR[i], cnt = 0, cnt2 = 0;
			for (ui j = pstart[u]; adjacency_scan_continues(j, pend[u], level); j++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				if (SR_rid[edges[j]] < R_end)
				{
					++cnt;
					if (SR_rid[edges[j]] < S_end)
						++cnt2;
				}
			}
			if (degree[u] != cnt)
				printf("Degree mismatch: vertex u=%d, level=%d, recorded degree=%d, counted degree=%d\n", u, level, degree[u], cnt);
			assert(degree[u] == cnt);
			assert(degree_in_S[u] == cnt2);
		}

		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif

#ifdef _REDUCTION_RULE_
		if (S_end >= 2u)
		{
			{ missing_edge_based_reduction_rule(S_end, R_end, level); }
			bool rr1_succeed;
			{ rr1_succeed = remove_vertices_with_prune(S_end, R_end, level); }
			if (!rr1_succeed)
			{
				restore_SR(S_end, R_end, old_S_end, old_R_end, level);
				return;
			}
		}
#endif

		for (ui i = 0; i < S_end; i++)
		{
			ui u = SR[i];
			if (degree[u] == optimal_sol_size - S + 1)
			{
				ui forced_neighbors_n = 0;
				if (fallback_uism_active)
				{
					// Moving one forced candidate can delete other candidates and
					// therefore compact u's active adjacency prefix.  Snapshot the
					// current candidates before propagation so the scan itself is not
					// invalidated by those exact incremental updates.
					for (ept j = pstart[u]; j < pend[u]; ++j)
					{
						ui w = edges[j];
						if (SR_rid[w] >= S_end && SR_rid[w] < R_end)
							buf[forced_neighbors_n++] = w;
					}
				}
				if (fallback_uism_active)
				{
					for (ui j = 0; j < forced_neighbors_n; ++j)
					{
						ui w = buf[j];
						if (SR_rid[w] < S_end || SR_rid[w] >= R_end)
							continue;
						bool succeed = move_u_to_S_with_prune(w, S_end, R_end, level);
						if (succeed)
							succeed = delete_vertices_based_on_dist(S_end, R_end, level);
						if (!succeed)
						{
							restore_SR(S_end, R_end, old_S_end, old_R_end, level);
							return;
						}
					}
					continue;
				}
				for (ept j = pstart[u]; adjacency_scan_continues(j, pend[u], level); j++)
				{
					if (!adjacency_edge_is_visible())
						continue;
					ui w = edges[j];
					if (SR_rid[w] >= S_end && SR_rid[w] < R_end)
					{
						bool succeed = move_u_to_S_with_prune(w, S_end, R_end, level);
						if (succeed)
							succeed = delete_vertices_based_on_dist(S_end, R_end, level);
						if (!succeed)
						{

							restore_SR(S_end, R_end, old_S_end, old_R_end, level);
							return;
						}
					}
				}
			}
		}

		if (S_end > optimal_sol_size)
			store_solution(S_end, false, level);

		if (R_end > optimal_sol_size && is_desired_feasible_sol(R_end))
		{
			store_solution(R_end, true, level);
			restore_SR(S_end, R_end, old_S_end, old_R_end, level);
			return;
		}

		if (R_end <= optimal_sol_size + 1 || optimal_sol_size >= _size_UB_)
		{
			restore_SR(S_end, R_end, old_S_end, old_R_end, level);
			return;
		}

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui u = SR[i], cnt = 0, cnt2 = 0;
			for (ui j = pstart[u]; adjacency_scan_continues(j, pend[u], level); j++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				if (SR_rid[edges[j]] < R_end)
				{
					++cnt;
					if (SR_rid[edges[j]] < S_end)
						++cnt2;
				}
			}
			assert(degree[u] == cnt);
			assert(degree_in_S[u] == cnt2);
		}
#endif
		ui u;
		{ u = choose_branch_vertex(S_end, R_end, level); }
		assert(SR_rid[u] >= S_end && SR_rid[u] < R_end);
		assert(degree[u] + S > optimal_sol_size && degree[u] + S > S_end);

		ui pre_best_solution_size = optimal_sol_size, t_old_R_end = R_end;
#ifndef NDEBUG
		const ui t_old_S_end = S_end;
#endif
		bool include_succeed;
		{
			include_succeed = move_u_to_S_with_prune(u, S_end, R_end, level);

			if (include_succeed)
				include_succeed = delete_vertices_based_on_dist(S_end, R_end, level);
		}

		if (include_succeed)
			BB_search(S_end, R_end, level + 1);
		if (optimal_sol_size >= _size_UB_)
		{

			return;
		}
		assert(S_end == t_old_S_end + 1 && SR[S_end - 1] == u);
		restore_SR(S_end, R_end, S_end, t_old_R_end, level);

#ifndef NDEBUG
		for (ui i = 0; i < n; i++)
			assert(!vis[i]);
#endif

		assert(Qv.empty() && SR_rid[u] == S_end - 1);
		bool succeed;
		{ succeed = remove_u_from_S_with_prune(S_end, R_end, level); }

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui u = SR[i], cnt = 0, cnt2 = 0;
			for (ui j = pstart[u]; adjacency_scan_continues(j, pend[u], level); j++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				if (SR_rid[edges[j]] < R_end)
				{
					++cnt;
					if (SR_rid[edges[j]] < S_end)
						++cnt2;
				}
			}
			assert(degree[u] == cnt);
			assert(degree_in_S[u] == cnt2);
		}
#endif
		{
			if (succeed && optimal_sol_size > pre_best_solution_size)
				succeed = collect_removable_vertices(S_end, R_end, level);
			if (succeed)
				succeed = remove_vertices_with_prune(S_end, R_end, level);
		}
		if (succeed)
			BB_search(S_end, R_end, level + 1);

		if (optimal_sol_size >= _size_UB_)
			return;
		assert(S_end >= old_S_end && R_end <= old_R_end);
		restore_SR(S_end, R_end, old_S_end, old_R_end, level);
	}

	ui rr1_collect_saturated_vertices(ui S_end, ui *saturated)
	{
		ui saturated_n = 0;
		for (ui i = 0; i < S_end; i++)
		{
			ui u = SR[i];
			if (degree_in_S[u] + S == S_end)
				saturated[saturated_n++] = u;
		}
		return saturated_n;
	}

	ui rr1_saturated_condition2_original_body(ui S_end, ui R_end, ui level, ui *removed)
	{
		ui saturated_n = rr1_collect_saturated_vertices(S_end, buf1);
		if (saturated_n == 0u)
			return 0;

		for (ui i = 0; i < saturated_n; i++)
			vis[buf1[i]] = 1;

		ui removed_n = 0;
		for (ui i = S_end; i < R_end; i++)
		{
			ui v = SR[i];
			if (level_id[v] <= level)
				continue;

			ui neighbor_saturated_n = 0;
			for (ept j = pstart[v]; adjacency_scan_continues(j, pend[v], level); j++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				if (vis[edges[j]])
					++neighbor_saturated_n;
			}

			if (neighbor_saturated_n < saturated_n)
				removed[removed_n++] = v;
		}

		for (ui i = 0; i < saturated_n; i++)
			vis[buf1[i]] = 0;
		return removed_n;
	}

	ui rr1_saturated_condition2_original(ui S_end, ui R_end, ui level, ui *removed)
	{

		return rr1_saturated_condition2_original_body(S_end, R_end, level, removed);
	}

	ui rr1_apply_condition2_removals(ui *removed, ui removed_n, ui level)
	{
		ui actual_removed_n = 0;
		{
			for (ui i = 0; i < removed_n; i++)
			{
				ui v = removed[i];
				if (level_id[v] > level)
				{
					level_id[v] = level;
					Qv.push(v);
					++actual_removed_n;
				}
			}
		}

		return actual_removed_n;
	}

	template <bool CountWork>
	ui rr1_budget_condition2_original_body(ui S_end, ui, ui level, ui *ids, ui ids_n, ui total_budget, ui *removed, RR1BudgetWork *work, const unsigned char *certificate_mask)
	{
		ui new_n = 0, removed_n = 0;
		for (ui i = 0; i < ids_n; i++)
		{

			ui idx = ids[i], v = vp[idx].first;
			if (certificate_mask != NULL && certificate_mask[i])
			{
				removed[removed_n++] = v;
				continue;
			}
			assert(total_budget >= vp[idx].second);
			ui t_budget = total_budget - vp[idx].second;
			assert(S_end >= degree_in_S[v] && (S - 1) >= (S_end - degree_in_S[v]));
			ui num = S_end + 1;

			for (ept j = pstart[v]; adjacency_scan_continues(j, pend[v], level); j++)
			{
				if (adjacency_edge_is_visible())
					vis[edges[j]] = 1;
			}

			ui j = 0, v_budget = S - 1 - (S_end - degree_in_S[v]);
			while (true)
			{
				if (j == new_n)
					j = i + 1;
				if (j >= ids_n || num > optimal_sol_size || num + ids_n - j <= optimal_sol_size)
					break;
				ui u = vp[ids[j]].first, miss_edges = vp[ids[j]].second;
				if (t_budget < miss_edges || (miss_edges != 0u && num + (t_budget / miss_edges) <= optimal_sol_size))
					break;
				if (CountWork)
					++work->candidate_checks;
				if (vis[u])
				{
					assert(t_budget >= miss_edges);
					t_budget -= miss_edges;
					++num;
				}
				else if (v_budget > 0u)
				{
					--v_budget;
					assert(t_budget >= miss_edges);
					t_budget -= miss_edges;
					++num;
				}
				++j;
			}

			for (ept j = pstart[v]; adjacency_scan_continues(j, pend[v], level); j++)
			{
				if (adjacency_edge_is_visible())
					vis[edges[j]] = 0;
			}

			if (num <= optimal_sol_size)
				removed[removed_n++] = v;
			else
				ids[new_n++] = ids[i];
		}
		return removed_n;
	}

	bool rr1_budget_csr_bucket_worthwhile(ui ids_n, ui *ids,
		ui &max_miss_edges, unsigned long long &edge_scan_upper) const
	{
		max_miss_edges = 0;
		edge_scan_upper = 0;
		// Use set-oriented CSR scans when their estimated work is lower than
		// repeated pairwise candidate checks.
		if (ids_n < 4096u)
			return false;

		unsigned __int128 edge_work = 0;
		for (ui i = 0; i < ids_n; ++i)
		{
			ui idx = ids[i], v = vp[idx].first;
			max_miss_edges = std::max(max_miss_edges, vp[idx].second);
			edge_work += (unsigned long long)(pend[v] - pstart[v]);
		}
		edge_scan_upper = cabp_saturating_value(edge_work);
		const unsigned __int128 bucket_n = (unsigned __int128)max_miss_edges + 1u;
		const unsigned __int128 scratch_bytes =
			(unsigned __int128)n * (3u * sizeof(ui) + sizeof(unsigned char)) +
			(5u * bucket_n + 2u) * sizeof(ui);
		if (scratch_bytes > MAX_CSR_SCRATCH_BYTES)
			return false;
		const unsigned __int128 csr_work = edge_work +
			(unsigned __int128)ids_n * (2u * bucket_n + 8u);
		const unsigned __int128 scalar_work =
			(unsigned __int128)ids_n * ids_n + 2u * edge_work;
		// An 8x structural margin absorbs scalar early exits and CSR setup.
		return csr_work != static_cast<unsigned __int128>(0) && 8u * csr_work <= scalar_work;
	}

	template <bool CountWork>
	ui rr1_budget_condition2_csr_bucket_body(ui S_end, ui R_end, ui level,
		ui *ids, ui ids_n, ui total_budget, ui *removed, RR1BudgetWork *work,
		const unsigned char *certificate_mask, ui max_miss_edges)
	{
		(void)R_end;
		const ui bucket_n = max_miss_edges + 1;
		if (rr1_budget_csr_member_epoch.size() != n)
		{
			rr1_budget_csr_member_epoch.assign(n, 0);
			rr1_budget_csr_seen_epoch.assign(n, 0);
			rr1_budget_csr_bucket_by_vertex.resize(n);
			rr1_budget_csr_state.resize(n);
			rr1_budget_csr_member_epoch_counter = 0;
			rr1_budget_csr_seen_epoch_counter = 0;
		}
		if (++rr1_budget_csr_member_epoch_counter == 0u)
		{
			fill(rr1_budget_csr_member_epoch.begin(), rr1_budget_csr_member_epoch.end(), 0);
			rr1_budget_csr_member_epoch_counter = 1;
		}
		const ui member_epoch = rr1_budget_csr_member_epoch_counter;

		rr1_budget_csr_future_count.assign(bucket_n, 0);
		rr1_budget_csr_kept_count.assign(bucket_n, 0);
		rr1_budget_csr_future_suffix.resize((size_t)bucket_n + 1);
		rr1_budget_csr_kept_suffix.resize((size_t)bucket_n + 1);
		rr1_budget_csr_adjacent_count.assign(bucket_n, 0);

#ifndef NDEBUG
		ui previous_d = 0;
#endif
		for (ui i = 0; i < ids_n; ++i)
		{
			ui idx = ids[i], v = vp[idx].first, d = vp[idx].second;
#ifndef NDEBUG
			assert(i == 0 || previous_d <= d);
			previous_d = d;
#endif
			assert(d < bucket_n);
			assert(rr1_budget_csr_member_epoch[v] != member_epoch);
			rr1_budget_csr_member_epoch[v] = member_epoch;
			rr1_budget_csr_bucket_by_vertex[v] = d;
			rr1_budget_csr_state[v] = 1; // future
			++rr1_budget_csr_future_count[d];
		}

		ui new_n = 0, removed_n = 0;
		unsigned long long scanned_edges = 0;
		unsigned long long bucket_visits = 0;
		unsigned long long suffix_ops = 0;
		for (ui i = 0; i < ids_n; ++i)
		{

			ui idx = ids[i], v = vp[idx].first, v_miss_edges = vp[idx].second;
			assert(rr1_budget_csr_state[v] == 1);
			rr1_budget_csr_state[v] = 0;
			assert(rr1_budget_csr_future_count[v_miss_edges] > 0);
			--rr1_budget_csr_future_count[v_miss_edges];
			if (certificate_mask != NULL && certificate_mask[i])
			{
				removed[removed_n++] = v;
				continue;
			}

			fill(rr1_budget_csr_adjacent_count.begin(), rr1_budget_csr_adjacent_count.end(), 0);
			if (++rr1_budget_csr_seen_epoch_counter == 0u)
			{
				fill(rr1_budget_csr_seen_epoch.begin(), rr1_budget_csr_seen_epoch.end(), 0);
				rr1_budget_csr_seen_epoch_counter = 1;
			}
			const ui seen_epoch = rr1_budget_csr_seen_epoch_counter;
			for (ept j = pstart[v]; adjacency_scan_continues(j, pend[v], level); ++j)
			{
				if (!adjacency_edge_is_visible())
					continue;
				++scanned_edges;
				ui u = edges[j];
				if (rr1_budget_csr_member_epoch[u] != member_epoch ||
					rr1_budget_csr_state[u] == 0 ||
					rr1_budget_csr_seen_epoch[u] == seen_epoch)
					continue;
				rr1_budget_csr_seen_epoch[u] = seen_epoch;
				ui d = rr1_budget_csr_bucket_by_vertex[u];
				assert(d < bucket_n);
				++rr1_budget_csr_adjacent_count[d];
			}

			rr1_budget_csr_future_suffix[bucket_n] = 0;
			rr1_budget_csr_kept_suffix[bucket_n] = 0;
			for (ui d = bucket_n; d > 0u; --d)
			{
				rr1_budget_csr_future_suffix[d - 1] =
					rr1_budget_csr_future_suffix[d] + rr1_budget_csr_future_count[d - 1];
				rr1_budget_csr_kept_suffix[d - 1] =
					rr1_budget_csr_kept_suffix[d] + rr1_budget_csr_kept_count[d - 1];
			}
			suffix_ops += bucket_n;

			assert(total_budget >= v_miss_edges);
			ui t_budget = total_budget - v_miss_edges;
			assert(S_end >= degree_in_S[v] && (S - 1) >= (S_end - degree_in_S[v]));
			ui num = S_end + 1;
			ui v_budget = S - 1 - (S_end - degree_in_S[v]);
			for (ui d = 0; d < bucket_n; ++d)
			{
				++bucket_visits;
				ui remaining = rr1_budget_csr_future_suffix[d] + rr1_budget_csr_kept_suffix[d];
				if (remaining == 0u || num > optimal_sol_size || num + remaining <= optimal_sol_size)
					break;
				if (d != 0u && (t_budget < d || num + (t_budget / d) <= optimal_sol_size))
					break;

				ui bucket_total = rr1_budget_csr_future_count[d] + rr1_budget_csr_kept_count[d];
				if (bucket_total == 0u)
					continue;
				ui adjacent_count = rr1_budget_csr_adjacent_count[d];
				assert(adjacent_count <= bucket_total);
				ui nonadjacent_count = bucket_total - adjacent_count;
				ui nonadjacent_includable = std::min(nonadjacent_count, v_budget);
				ui includable = adjacent_count + nonadjacent_includable;
				if (includable == 0u)
					continue;

				if (d == 0u)
				{
					num += includable;
					v_budget -= nonadjacent_includable;
					continue;
				}
				ui budget_limited = t_budget / d;
				if (budget_limited >= includable)
				{
					num += includable;
					t_budget -= includable * d;
					v_budget -= nonadjacent_includable;
				}
				else
				{
					num += budget_limited;
					t_budget -= budget_limited * d;
					break;
				}
			}

			if (num <= optimal_sol_size)
				removed[removed_n++] = v;
			else
			{
				ids[new_n++] = ids[i];
				rr1_budget_csr_state[v] = 2; // kept
				++rr1_budget_csr_kept_count[v_miss_edges];
			}
		}

		if (CountWork)
		{
			// Charge the operations actually performed by this backend.  The
			// production work-adaptive ledger intentionally uses these backend-
			// aware counters, so a cheaper exact UISM backend may enable further
			// exact CABP calls without any wall-clock or result-dependent gate.
			work->candidate_checks += scanned_edges;
			work->word_ops += suffix_ops + bucket_visits;
			work->bucket_visits += bucket_visits;
		}

		return removed_n;
	}

	static unsigned long long work_adaptive_saturating_add(unsigned long long a, unsigned long long b)
	{
		const unsigned long long max_value = std::numeric_limits<unsigned long long>::max();
		return max_value - a < b ? max_value : a + b;
	}

	bool work_adaptive_has_credit() const
	{
		unsigned __int128 credit = (unsigned __int128)work_adaptive_search_credit;
		{ credit += (unsigned __int128)work_adaptive_removal_benefit; }
		return (unsigned __int128)work_adaptive_total_work <= credit;
	}

	bool work_adaptive_should_run(ui candidate_exposure, bool &forced_probe)
	{
		forced_probe = false;
		work_adaptive_search_credit = work_adaptive_saturating_add(work_adaptive_search_credit, candidate_exposure);
		stats.work_adaptive_search_credit = work_adaptive_saturating_add(stats.work_adaptive_search_credit, candidate_exposure);
		if (((work_adaptive_total_runs == static_cast<unsigned long long>(0))) || (work_adaptive_has_credit()))
			return true;
		if (work_adaptive_skips_since_probe >= work_adaptive_probe_interval)
		{
			forced_probe = true;
			work_adaptive_forced_probe = true;

			return true;
		}
		++work_adaptive_skips_since_probe;
		return false;
	}

	void work_adaptive_record_run(const RR1BudgetWork &work, ui tested_vertices,
		ui removed_vertices, ui candidate_count
	)
	{
		unsigned long long call_work = work_adaptive_saturating_add(work.word_ops, work.candidate_checks);
		call_work = work_adaptive_saturating_add(call_work, tested_vertices);
		work_adaptive_total_work = work_adaptive_saturating_add(work_adaptive_total_work, call_work);
		work_adaptive_total_removed = work_adaptive_saturating_add(work_adaptive_total_removed, removed_vertices);
		work_adaptive_total_runs = work_adaptive_saturating_add(work_adaptive_total_runs, 1);
		stats.work_adaptive_work_ops = work_adaptive_saturating_add(stats.work_adaptive_work_ops, call_work);
		unsigned long long removed_credit = 0;
		{
			removed_credit = removed_vertices != 0u &&
				candidate_count > std::numeric_limits<unsigned long long>::max() / removed_vertices
					? std::numeric_limits<unsigned long long>::max()
					: (unsigned long long)removed_vertices * candidate_count;
			work_adaptive_removal_benefit = work_adaptive_saturating_add(
				work_adaptive_removal_benefit, removed_credit);
		}
		stats.work_adaptive_removed_credit = work_adaptive_saturating_add(
			stats.work_adaptive_removed_credit, removed_credit);
		if (((removed_vertices != 0u)) || (work_adaptive_has_credit()))
			work_adaptive_probe_interval = 1;
		else if (work_adaptive_forced_probe)
		{
			{ work_adaptive_probe_interval =
					work_adaptive_probe_interval > std::numeric_limits<ui>::max() / 2
						? std::numeric_limits<ui>::max()
						: work_adaptive_probe_interval * 2; }
		}
		work_adaptive_skips_since_probe = 0;
		work_adaptive_forced_probe = false;
		stats.work_adaptive_probe_interval = work_adaptive_probe_interval;

	}

	void adaptive_budget_record_run(long long budget_us, ui removed_vertices)
	{

		++stats.adaptive_budget_run_cnt;

		stats.adaptive_budget_removed_vertices_so_far += removed_vertices;
		stats.adaptive_budget_us_so_far += budget_us;

	}

	static unsigned long long cabp_saturating_value(unsigned __int128 value)
	{
		const unsigned long long limit = std::numeric_limits<unsigned long long>::max();
		return value > limit ? limit : (unsigned long long)value;
	}

	__attribute__((aligned(64)))
	ui rr1_budget_condition2_original(ui S_end, ui R_end, ui level, ui *ids, ui ids_n, ui total_budget, ui *removed, long long *elapsed_us = NULL, long long *policy_elapsed_us = NULL, bool *used_bitset_backend = NULL, RR1BudgetWork *selected_work = NULL, const unsigned char *certificate_mask = NULL, bool *used_csr_bucket_backend = NULL)
	{

		ui csr_max_miss_edges = 0;
		unsigned long long csr_edge_scan_upper = 0;
		bool csr_candidate = (ids_n >= 4096u);
		bool use_csr_bucket = csr_candidate &&
			rr1_budget_csr_bucket_worthwhile(ids_n, ids,
				csr_max_miss_edges, csr_edge_scan_upper);
		(void)csr_edge_scan_upper;

		if (used_bitset_backend != NULL)
			*used_bitset_backend = false;
		if (used_csr_bucket_backend != NULL)
			*used_csr_bucket_backend = false;

		if (use_csr_bucket)
		{
			if (used_csr_bucket_backend != NULL)
				*used_csr_bucket_backend = true;
			Timer budget_timer;

			ui removed_n = selected_work != NULL
				? rr1_budget_condition2_csr_bucket_body<true>(S_end, R_end, level,
					ids, ids_n, total_budget, removed, selected_work,
					certificate_mask, csr_max_miss_edges)
				: rr1_budget_condition2_csr_bucket_body<false>(S_end, R_end, level,
					ids, ids_n, total_budget, removed, NULL,
					certificate_mask, csr_max_miss_edges);
			long long elapsed = budget_timer.elapsed();
			if (elapsed_us != NULL)
				*elapsed_us = elapsed;
			if (policy_elapsed_us != NULL)
				*policy_elapsed_us = elapsed;

			return removed_n;
		}

		if (elapsed_us != NULL)
		{
			Timer budget_timer;

			ui removed_n = selected_work != NULL
				? rr1_budget_condition2_original_body<true>(S_end, R_end, level, ids, ids_n, total_budget, removed, selected_work, certificate_mask)
				: rr1_budget_condition2_original_body<false>(S_end, R_end, level, ids, ids_n, total_budget, removed, NULL, certificate_mask);
			long long elapsed = budget_timer.elapsed();

			if (elapsed_us != NULL)
				*elapsed_us = elapsed;
			if (policy_elapsed_us != NULL)
				*policy_elapsed_us = elapsed;

			return removed_n;
		}
		return selected_work != NULL
			? rr1_budget_condition2_original_body<true>(S_end, R_end, level, ids, ids_n, total_budget, removed, selected_work, certificate_mask)
			: rr1_budget_condition2_original_body<false>(S_end, R_end, level, ids, ids_n, total_budget, removed, NULL, certificate_mask);
	}

	void missing_edge_based_reduction_rule(ui S_end, ui R_end, ui level)
	{

		while (!Qv.empty())
		{
			ui u = Qv.front();
			Qv.pop();
			level_id[u] = n;
		}

		vp.resize(R_end - S_end);
		ui active_n = 0;
		ui max_miss_edges = 0;
		{
			for (ui i = S_end; i < R_end; i++)
			{
				ui v = SR[i];
				if (level_id[v] <= level)
					continue;
				ui miss_edges = S_end - degree_in_S[v];
				if (miss_edges > max_miss_edges)
					max_miss_edges = miss_edges;
				assert(i >= S_end && miss_edges < n);
				vp[active_n].first = v;
				vp[active_n].second = miss_edges;
				++active_n;
			}
		}
		vp.resize(active_n);

		ui *cnt = neighbors;
		for (ui i = 0; i <= max_miss_edges; i++)
			cnt[i] = 0;
		for (ui i = 0; i < vp.size(); i++)
			++cnt[vp[i].second];
		for (ui i = 0; i < max_miss_edges; i++)
			cnt[i + 1] += cnt[i];
		for (ui i = max_miss_edges; i > 0u; i--)
			cnt[i] = cnt[i - 1];
		cnt[0] = 0;
		ui *ids = nonneighbors;
		for (ui i = 0; i < vp.size(); i++)
			ids[cnt[vp[i].second]++] = i;

		ui total_budget = 0;
		for (ui i = 0; i < S_end; i++)
		{
			assert(S_end > degree_in_S[SR[i]]);
			total_budget += S - (S_end - degree_in_S[SR[i]]);
		}

		ui sat_removed_n = rr1_saturated_condition2_original(S_end, R_end, level, buf2);
		rr1_apply_condition2_removals(buf2, sat_removed_n, level);

		ui ids_n = 0;
		for (ui i = 0; i < vp.size(); i++)
		{
			ui idx = ids[i];
			if (level_id[vp[idx].first] > level)
				ids[ids_n++] = idx;
		}

		{

			bool work_adaptive_forced = false;
			ui C_size_before_budget = R_end >= S_end ? R_end - S_end : 0;
			bool run_budget = (work_adaptive_should_run(ids_n, work_adaptive_forced));

			if (run_budget)
			{
				long long budget_us = 0;
				long long policy_budget_us = 0;
				bool used_bitset_backend = false;
				bool used_csr_bucket_backend = false;
				RR1BudgetWork structural_work;
				const unsigned char *certificate_mask = nullptr;
				bool track_budget = adaptive_budget_tracking_enabled();
				ui budget_removed_n = rr1_budget_condition2_original(S_end, R_end, level, ids, ids_n, total_budget, buf2, track_budget ? &budget_us : NULL, track_budget ? &policy_budget_us : NULL, &used_bitset_backend, (&structural_work), certificate_mask, &used_csr_bucket_backend);

				ui actual_budget_removed_n = rr1_apply_condition2_removals(buf2, budget_removed_n, level);
				{ work_adaptive_record_run(structural_work, ids_n, actual_budget_removed_n, C_size_before_budget); }
				long long schedule_budget_us = (budget_us);
				adaptive_budget_record_run(schedule_budget_us, actual_budget_removed_n);

			}
			else
			{

			}
		}
		assert(ids_n < R_end);
	}

	void get_neighbors_and_non_neighbors(ui u, ui idx_start, ui idx_end, ui level, ui &neighbors_n, ui &non_neighbors_n)
	{
		neighbors_n = non_neighbors_n = 0;

		for (ept i = pstart[u]; adjacency_scan_continues(i, pend[u], level); i++)
			if (adjacency_edge_is_visible() && SR_rid[edges[i]] < idx_end)
				vis[edges[i]] = 1;
		for (ui i = idx_start; i < idx_end; i++)
			if (SR[i] != u)
			{
				if (vis[SR[i]])
					neighbors[neighbors_n++] = SR[i];
				else
					nonneighbors[non_neighbors_n++] = SR[i];
			}
		for (ept i = pstart[u]; adjacency_scan_continues(i, pend[u], level); i++)
			if (adjacency_edge_is_visible())
				vis[edges[i]] = 0;
	}

	bool move_u_to_S_with_prune(ui u, ui &S_end, ui &R_end, ui level)
	{
		assert(SR_rid[u] >= S_end && SR_rid[u] < R_end && SR[SR_rid[u]] == u);
		assert(degree_in_S[u] + S > S_end);
#ifndef NDEBUG
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
#endif
		if (SR_rid[u] != S_end)
			swap_pos(S_end, SR_rid[u]);
		++S_end;

		ui neighbors_n = 0, nonneighbors_n = 0;
		get_neighbors_and_non_neighbors(u, 0, R_end, level, neighbors_n, nonneighbors_n);
		assert(neighbors_n + nonneighbors_n == R_end - 1);
		for (ui i = 0; i < neighbors_n; i++)
			++degree_in_S[neighbors[i]];

		while (!Qv.empty())
		{
			ui u = Qv.front();
			Qv.pop();
			level_id[u] = n;
		}

		for (ui i = 0; i < nonneighbors_n; i++)
		{
			ui v = nonneighbors[i];
			assert(SR_rid[v] < R_end);
			if (SR_rid[v] >= S_end)
			{
				if (level_id[v] == level)
					continue;
				if (S_end < degree_in_S[v] || S_end < degree_in_S[u])
				{

					fflush(stderr);
				}
				assert(S_end >= degree_in_S[v] && S_end >= degree_in_S[u]);
				if (S_end - degree_in_S[v] >= S || S_end - degree_in_S[u] == S)
				{
					level_id[v] = level;
					Qv.push(v);
				}
			}
			else if (S_end - degree_in_S[v] == S)
			{
				assert(SR_rid[v] < S_end);
				for (ept j = pstart[v]; adjacency_scan_continues(j, pend[v], level); j++)
					if (adjacency_edge_is_visible())
						vis[edges[j]] = 1;
				for (ui j = S_end; j < R_end; j++)
					if (level_id[SR[j]] > level && !vis[SR[j]])
					{
						level_id[SR[j]] = level;
						Qv.push(SR[j]);
					}
				for (ept j = pstart[v]; adjacency_scan_continues(j, pend[v], level); j++)
					if (adjacency_edge_is_visible())
						vis[edges[j]] = 0;
			}
		}
		return remove_vertices_with_prune(S_end, R_end, level);
	}

	bool remove_vertices_with_prune(ui S_end, ui &R_end, ui level)
	{
		while (!Qv.empty())
		{
			ui u = Qv.front();
			Qv.pop();
			assert(SR[SR_rid[u]] == u && SR_rid[u] >= S_end && SR_rid[u] < R_end && R_end && level_id[u] == level);
			--R_end;
			swap_pos(SR_rid[u], R_end);

			bool terminate = false;
			ui neighbors_n = 0;
			if (fallback_uism_active)
				uism_begin_vertex_removal(u);
			for (ept i = pstart[u]; adjacency_scan_continues(i, pend[u], level); i++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				if (SR_rid[edges[i]] < R_end)
				{
					ui w = edges[i];
					neighbors[neighbors_n++] = w;
					if (fallback_uism_active)
					uism_remove_edge_from_active_row(w, uism_reverse_edge[i]);
					assert(degree[w] > 0);
					--degree[w];
					if (degree[w] + S <= optimal_sol_size)
					{
						if (SR_rid[w] < S_end)
							terminate = true;
						else if (level_id[w] > level)
						{
							level_id[w] = level;
							Qv.push(w);
						}
					}
				}
			}
			if (terminate)
			{
				if (fallback_uism_active)
					uism_restore_last_removed_vertex(u);
				else
					for (ui i = 0; i < neighbors_n; i++)
						++degree[neighbors[i]];
				level_id[u] = n;
				++R_end;
				return false;
			}
		}

		return true;
	}

	bool delete_vertices_based_on_dist(ui S_end, ui &R_end, ui level)
	{
#ifndef _REDUCTION_RULE_
		return true;
#endif
		assert(2 * S > optimal_sol_size);
		ui dist_limit = 2 * S - optimal_sol_size;
		assert(S_end > 0);
		ui index = S_end - 1;
		while (true)
		{
			vector<ui> dist(R_end, n);
			queue<ui> q;
			ui u = SR[index];
			assert(SR_rid[u] < S_end);
			dist[index] = 0;
			q.push(u);
			while (!q.empty())
			{
				ui current = q.front();
				assert(SR_rid[current] < R_end);
				q.pop();
				for (ui i = pstart[current]; adjacency_scan_continues(i, pend[current], level); ++i)
				{
					if (!adjacency_edge_is_visible())
						continue;
					ui neighbor = edges[i];
					ui neighbor_rid = SR_rid[neighbor];
					if (neighbor_rid < R_end && dist[neighbor_rid] == n)
					{
						assert(SR_rid[neighbor] < R_end && dist[SR_rid[current]] != n);
						dist[neighbor_rid] = dist[SR_rid[current]] + 1;
						assert(dist[neighbor_rid] <= dist_limit);
						if (dist[neighbor_rid] < dist_limit)
							q.push(neighbor);
					}
				}
			}

			for (ui i = 0; i < R_end; ++i)
			{
				if (dist[i] > dist_limit)
				{
					if (i < S_end)
						return false;
					assert(i >= S_end);
					assert(level_id[SR[i]] > level);
					level_id[SR[i]] = level;
					Qv.push(SR[i]);
				}
			}

			if (Qv.empty())
				return true;
			if (!remove_vertices_with_prune(S_end, R_end, level))
				return false;

			if (index > 0u)
				index--;
			else
				index = S_end - 1;
		}
	}

	void restore_SR(ui &S_end, ui &R_end, ui old_S_end, ui old_R_end, ui level)
	{
		Timer restore_timer;
		while (!Qv.empty())
		{
			ui u = Qv.front();
			Qv.pop();
			assert(level_id[u] == level);
			assert(SR_rid[u] < R_end);
			level_id[u] = n;
		}

		for (; R_end < old_R_end; R_end++)
		{
			ui u = SR[R_end];
			assert(level_id[u] == level && SR_rid[u] == R_end);
			level_id[u] = n;

			if (fallback_uism_active)
			{
				uism_restore_last_removed_vertex(u);
				// A removed vertex does not receive degree_in_S updates while it is
				// outside R.  Reconstruct its selected-neighbor count from the restored
				// active prefix; this is touched-row work and avoids a global repair.
				degree_in_S[u] = 0;
				for (ept i = pstart[u]; i < pend[u]; ++i)
					if (SR_rid[edges[i]] < S_end)
						++degree_in_S[u];
			}
			else
			{
				degree[u] = degree_in_S[u] = 0;
				for (ept i = pstart[u]; adjacency_scan_continues(i, pend[u], level); i++)
				{
					if (!adjacency_edge_is_visible())
						continue;
					ui w = edges[i];
					assert(SR[SR_rid[w]] == w);
					if (SR_rid[w] < R_end)
					{
						++degree[w];
						++degree[u];
					}
					if (SR_rid[w] < S_end)
						++degree_in_S[u];
				}
			}
		}

		for (; S_end > old_S_end; S_end--)
		{
			ui u = SR[S_end - 1];
			assert(SR_rid[u] == S_end - 1);

			for (ept i = pstart[u]; adjacency_scan_continues(i, pend[u], level); i++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				ui w = edges[i];
				if (SR_rid[w] < R_end)
					--degree_in_S[w];
			}
		}

	}

	bool remove_u_from_S_with_prune(ui &S_end, ui &R_end, ui level)
	{
		assert(S_end && R_end);
		ui u = SR[S_end - 1];
		--S_end;
		--R_end;
		swap_pos(S_end, R_end);
		level_id[u] = level;

		bool terminate = false;
		if (fallback_uism_active)
			uism_begin_vertex_removal(u);
		for (ept i = pstart[u]; adjacency_scan_continues(i, pend[u], level); i++)
		{
			if (!adjacency_edge_is_visible())
				continue;
			if (SR_rid[edges[i]] < R_end)
			{
				ui v = edges[i];
				if (fallback_uism_active)
					uism_remove_edge_from_active_row(v, uism_reverse_edge[i]);
				assert(degree_in_S[v] > 0 && degree[v] > 0 && degree[v] <= R_end);
				--degree_in_S[v];
				--degree[v];
				if (degree[v] + S <= optimal_sol_size)
				{
					if (SR_rid[v] < S_end)
						terminate = true;
					else
					{
						assert(level_id[v] > level);
						level_id[v] = level;
						Qv.push(v);
					}
				}
			}
		}
		if (terminate)
			return false;
		return true;
	}

	bool collect_removable_vertices(ui S_end, ui R_end, ui level)
	{
		for (ui i = 0; i < S_end; i++)
			if (degree[SR[i]] + S <= optimal_sol_size)
				return false;

		for (ui i = S_end; i < R_end; i++)
			if (level_id[SR[i]] > level)
			{
				ui v = SR[i];
				assert(S_end >= degree_in_S[v]);
				if (S_end - degree_in_S[v] >= S || degree[v] + S <= optimal_sol_size)
				{
					level_id[v] = level;
					Qv.push(v);
					continue;
				}
			}

		return true;
	}

	void swap_pos(ui i, ui j)
	{
		swap(SR[i], SR[j]);
		SR_rid[SR[i]] = i;
		SR_rid[SR[j]] = j;
	}

	ui choose_branch_vertex(ui S_end, ui R_end, ui level)
	{
		ui v = n;
#ifdef _QUERY_DECOMPOSITION_
		assert(UB_size > S);
		ui k_max = UB_size - S;
		if (k_max <= tau)
		{
			for (ept i = pstart[SR[0]]; adjacency_scan_continues(i, pend[SR[0]], level); i++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				if (S_end <= SR_rid[edges[i]] && SR_rid[edges[i]] < R_end)
				{
					v = edges[i];
					break;
				}
			}

			if (v != n)
				return v;
		}
#endif

		v = n;
		ui min_deg = n;
		for (ui i = 0; i < R_end; i++)
			if (degree[SR[i]] < min_deg)
			{
				v = SR[i];
				min_deg = degree[SR[i]];
			}
		assert(v != n);

		if (SR_rid[v] < S_end)
		{
			ui t_min_deg = n;
			ui branching_vertex = n;
			for (ept i = pstart[v]; adjacency_scan_continues(i, pend[v], level); i++)
			{
				if (!adjacency_edge_is_visible())
					continue;
				if (SR_rid[edges[i]] < R_end)
					vis[edges[i]] = 1;
			}
			for (ui i = S_end; i < R_end; i++)
				if (SR[i] != v)
					if (!vis[SR[i]] && degree[SR[i]] < t_min_deg)
					{
						branching_vertex = SR[i];
						t_min_deg = degree[SR[i]];
					}

			for (ept i = pstart[v]; adjacency_scan_continues(i, pend[v], level); i++)
				if (adjacency_edge_is_visible())
					vis[edges[i]] = 0;
			v = branching_vertex;
		}

		assert(v != n && SR_rid[v] >= S_end && SR_rid[v] < R_end);
		return v;
	}
};
#endif
