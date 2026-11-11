#ifndef _MBBPS_MATRIX_
#define _MBBPS_MATRIX_

#include "Utility.h"
#include "Timer.h"
#include "CapacityBound.h"
#include <climits>
#include "ARCSCSConfig.h"
#include <cstring>

class MBBPS_matrix
{
public:
private:
	ui n;
	ui capacity;

	char *matrix;
	long long matrix_size;

	ui *degree;
	ui *degree_in_S;

	ui S;
	ui *best_solution;
	ui optimal_sol_size;
	ui _size_UB_;

	ui *neighbors;
	ui *nonneighbors;

	ui *SR;
	ui *SR_rid;
	queue<ui> Qv;
	ui *level_id;

	vector<pair<ui, ui>> vp;

	ARCWorkLedger work_ledger;
	unsigned long long pair_ledger_runs;
	unsigned long long pair_ledger_skips;
	unsigned long long pair_probe_interval;
	ui pair_last_candidate_count;
	unsigned long long triple_ledger_runs;
	unsigned long long triple_ledger_skips;
	unsigned long long triple_probe_interval;

	bool use_packed_only_adjacency;
	bool use_matrix_rr1_bucket_bitset;
	ui bitset_words;
	vector<unsigned long long> adj_bits;
	vector<unsigned long long> activeR_bits;
	vector<unsigned long long> activeS_bits;
	vector<unsigned long long> reached_bits;
	vector<unsigned long long> frontier_bits;
	vector<unsigned long long> scratch_bits;
	struct DegreeTrailEntry
	{
		ui vertex;
		ui old_degree;
		unsigned long long old_epoch;
	};
	struct DegreeTrailCheckpoint
	{
		size_t trail_size;
		unsigned long long epoch;
		unsigned long long parent_epoch;
		bool active;

		DegreeTrailCheckpoint() : trail_size(0), epoch(0), parent_epoch(0), active(false) {}
	};
	struct BatchedDegreeInvariantViolation
	{
		ui vertex;
		ui degree;
		ui loss;
		ui exact_after_wave;
		ui level;
	};
	struct DegreeInSInvariantViolation
	{
		ui vertex;
		ui degree_in_S;
		ui S_end;
		ui level;
	};
	bool use_matrix_state_trail;
	bool use_matrix_batched_degree_loss;

	vector<DegreeTrailEntry> degree_trail;
	vector<unsigned long long> degree_epoch;
	unsigned long long current_degree_epoch;
	unsigned long long next_degree_epoch;
	vector<ui> loss_count;
	vector<unsigned long long> loss_epoch;
	vector<ui> loss_touched;
	vector<unsigned long long> removed_wave_bits;
	vector<ui> removed_wave_vertices;
	vector<ui> wave_original_rid;
	vector<unsigned long long> rr1_bucket_future_bits;
	vector<unsigned long long> rr1_bucket_kept_bits;
	vector<ui> rr1_bucket_future_count;
	vector<ui> rr1_bucket_kept_count;
	vector<ui> rr1_bucket_word_offsets;
	vector<ui> rr1_bucket_word_ids;
	vector<unsigned long long> wave_rid_epoch;
	unsigned long long next_loss_epoch;
	// Query-local immutable state.  The matrix solver is reused for every S trial of the same query,
	// so none of these containers may alias the search scratch arrays above.
	vector<ui> base_degree;
	vector<ui> local_pstart;
	vector<ui> local_edges;
	vector<pair<ui, ui>> prepared_edges;
	vector<ui> cached_core;
	vector<ui> cached_peel_sequence;
	bool graph_prepared;

	unsigned long long search_node_limit;
	unsigned long long search_nodes_visited;
	bool search_node_limit_exhausted;
	struct SearchNodeBudgetExhausted {};

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
	MBBPS_matrix()
	{
		n = 0;
		capacity = 0;
		matrix = nullptr;
		matrix_size = 0;

		degree = degree_in_S = nullptr;

		best_solution = nullptr;
		S = optimal_sol_size = _size_UB_ = 0;

		neighbors = nonneighbors = nullptr;

		SR = SR_rid = nullptr;
		level_id = nullptr;

		pair_ledger_runs = pair_ledger_skips = triple_ledger_runs = triple_ledger_skips = 0;
		pair_probe_interval = triple_probe_interval = 1;
		pair_last_candidate_count = std::numeric_limits<ui>::max();

		use_packed_only_adjacency = false;
		use_matrix_rr1_bucket_bitset = false;
		use_matrix_state_trail = false;
		use_matrix_batched_degree_loss = false;

		bitset_words = 0;
		current_degree_epoch = 0;
		next_degree_epoch = 1;
		next_loss_epoch = 1;
		graph_prepared = false;

		search_node_limit = 0;
		search_nodes_visited = 0;
		search_node_limit_exhausted = false;

	}

	~MBBPS_matrix()
	{
		if (matrix != NULL)
		{
			delete[] matrix;
			matrix = NULL;
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
		if (level_id != NULL)
		{
			delete[] level_id;
			level_id = NULL;
		}
	}

	void allocateMemory(ui n)
	{
		if (n <= 0u)
			return;
		if (matrix != nullptr || degree != nullptr || degree_in_S != nullptr)
		{
			fprintf(stderr, "MBBPS_matrix::allocateMemory may only be called once per solver\n");
			exit(1);
		}
		capacity = n;

		matrix_size = 1;
		matrix = new char[matrix_size];
		degree = new ui[n];
		degree_in_S = new ui[n];
		best_solution = new ui[n];
		SR = new ui[n];
		SR_rid = new ui[n];
		neighbors = new ui[n];
		nonneighbors = new ui[n];
		level_id = new ui[n];
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

	void set_use_matrix_capacity_set_branch(ui min_D)
	{
		if (min_D == 0u)
		{
			fprintf(stderr, "MBBPS_matrix capacity set-branch min D must be positive\n");
			exit(1);
		}

	}

	void set_pair_capacity_bound(ui max_words)
	{
		if (max_words == 0u)
		{
			fprintf(stderr, "MBBPS_matrix pair-capacity bound max words must be positive\n");
			exit(1);
		}

	}

	void set_adaptive_triple_capacity_bound(ui max_dp_states)
	{
		if (max_dp_states == 0u)
		{
			fprintf(stderr, "MBBPS_matrix triple-capacity bound max DP states must be positive\n");
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

	void set_packed_only_adjacency(bool enabled)
	{
		if (graph_prepared)
		{
			fprintf(stderr, "MBBPS_matrix packed-only mode cannot change after load_graph\n");
			exit(1);
		}

		use_packed_only_adjacency = enabled;
	}

	void set_use_matrix_rr1_bucket_bitset(bool enabled)
	{
		if (graph_prepared && enabled != use_matrix_rr1_bucket_bitset)
		{
			fprintf(stderr, "MBBPS_matrix RR1 bucket-bitset mode cannot change after load_graph\n");
			exit(1);
		}
		use_matrix_rr1_bucket_bitset = enabled;
	}

	void set_use_matrix_state_trail(bool enabled)
	{
		if (graph_prepared && enabled != use_matrix_state_trail)
		{
			fprintf(stderr, "MBBPS_matrix state-trail mode cannot change after load_graph\n");
			exit(1);
		}
		use_matrix_state_trail = enabled;
	}

	void set_use_matrix_batched_degree_loss(bool enabled, ui alpha)
	{
		if ((graph_prepared) && ((enabled != use_matrix_batched_degree_loss) || (alpha != 1u)))
		{
			fprintf(stderr, "MBBPS_matrix batched degree-loss mode cannot change after load_graph\n");
			exit(1);
		}
		if (alpha == 0u)
		{
			fprintf(stderr, "MBBPS_matrix batched degree-loss alpha must be positive\n");
			exit(1);
		}
		use_matrix_batched_degree_loss = enabled;

	}

	inline bool matrix_bitset_search_kernels_enabled() const
	{
		return true;
	}

	inline unsigned long long bit_mask(ui v) const
	{
		return 1ULL << (v & 63);
	}

	inline char bit_test(const vector<unsigned long long> &bits, ui v) const
	{
		return (bits[v >> 6] & bit_mask(v)) != static_cast<unsigned long long>(0);
	}

	inline char adjacent(ui u, ui v) const
	{
		if (!use_packed_only_adjacency)
			return matrix[(size_t)u * n + v];
		return (adj_bits[(size_t)u * bitset_words + (v >> 6)] & bit_mask(v)) != static_cast<unsigned long long>(0);
	}

	struct AdjacencyRowView
	{
		const MBBPS_matrix *owner;
		ui u;

		AdjacencyRowView(const MBBPS_matrix *owner_, ui u_) : owner(owner_), u(u_) {}
		char operator[](ui v) const { return owner->adjacent(u, v); }
	};

	bool collect_capacity_b1_branch_set(ui S_end, ui R_end, ui pivot, ui &watch_u, vector<ui> &D)
	{

		ui best_D = 0;
		watch_u = n;
		for (ui i = 0; i < S_end; ++i)
		{
			ui u = SR[i];
			ui deficit = S_end - degree_in_S[u];
			assert(deficit <= S);
			ui b = S - deficit;
			if (b != 1u)
				continue;
			ui candidate_neighbors = degree[u] - degree_in_S[u];
			assert(R_end - S_end >= candidate_neighbors);
			ui D_size = (R_end - S_end) - candidate_neighbors;
			const bool structurally_eligible = (D_size != 0u);
			if (structurally_eligible && D_size > best_D)
			{
				best_D = D_size;
				watch_u = u;
			}
		}
		if (watch_u == n)
			return false;

		AdjacencyRowView watch_matrix(this, watch_u);
		if (watch_matrix[pivot])
		{

			return false;
		}

		D.clear();
		D.reserve(best_D);
		D.push_back(pivot);
		for (ui i = S_end; i < R_end; ++i)
		{
			ui v = SR[i];
			if (v != pivot && !watch_matrix[v])
				D.push_back(v);
		}
		assert(D.size() == best_D);
		{
			unsigned long long affected_edges = 0;
			for (ui v : D)
				affected_edges += degree[v];
			const unsigned long long set_branch_work =
				(unsigned long long)D.size() + affected_edges;
			const unsigned long long binary_branch_work =
				2ull * (unsigned long long)(R_end - S_end);
			const bool more_than_binary_arms = D.size() > 2u;
			const bool majority_constraint =
				2ull * (unsigned long long)D.size() >
				(unsigned long long)(R_end - S_end);
			if (!more_than_binary_arms ||
				(set_branch_work > binary_branch_work && !majority_constraint))
				return false;
		}
		return true;
	}

	void capacity_b1_set_branch(ui &S_end, ui &R_end, ui level, const vector<ui> &D)
	{

		for (ui v : D)
		{
			if (SR_rid[v] < S_end || SR_rid[v] >= R_end || level_id[v] <= level)
			{

				continue;
			}

			ui arm_old_S_end = S_end;
			ui arm_old_R_end = R_end;
			ui arm_pre_best = optimal_sol_size;
			DegreeTrailCheckpoint include_degree_state = begin_degree_trail_scope();
			bool include_succeed;
			{ include_succeed = move_u_to_S_with_prune(v, S_end, R_end, level) && delete_vertices_based_on_dist(S_end, R_end, level); }

			if (include_succeed)
				BB_search(S_end, R_end, level + 1, false);
			if (optimal_sol_size >= _size_UB_)
				return;

			bool include_moved_v_to_S = (S_end == arm_old_S_end + 1 && SR[S_end - 1] == v);
			if (include_moved_v_to_S)
				restore_SR_and_edges(S_end, R_end, S_end, arm_old_R_end, level, include_degree_state);
			else
			{
				rollback_degree_trail(include_degree_state);
				assert(S_end == arm_old_S_end && R_end == arm_old_R_end && SR_rid[v] >= S_end && SR_rid[v] < R_end);
			}

			assert(Qv.empty());
			bool exclude_succeed;
			if (include_moved_v_to_S)
			{
				{
					exclude_succeed = remove_u_from_S_with_prune(S_end, R_end, level);
					if (exclude_succeed && optimal_sol_size > arm_pre_best)
						exclude_succeed = collect_removable_vertices_and_edges(S_end, R_end, level);
					if (exclude_succeed)
						exclude_succeed = remove_vertices_and_edges_with_prune(S_end, R_end, level);
				}
			}
			else
			{
				{
					assert(level_id[v] > level);
					level_id[v] = level;
					Qv.push(v);
					exclude_succeed = remove_vertices_and_edges_with_prune(S_end, R_end, level);
				}
			}
			if (!exclude_succeed)
				return;
			assert(S_end == arm_old_S_end && R_end < arm_old_R_end);
		}

		BB_search(S_end, R_end, level + 1, false);
	}

	inline void bit_set(vector<unsigned long long> &bits, ui v)
	{
		bits[v >> 6] |= bit_mask(v);
	}

	inline void bit_clear(vector<unsigned long long> &bits, ui v)
	{
		bits[v >> 6] &= ~bit_mask(v);
	}

	DegreeTrailCheckpoint begin_degree_trail_scope()
	{
		DegreeTrailCheckpoint checkpoint;
		if (!use_matrix_state_trail)
			return checkpoint;
		if (next_degree_epoch == static_cast<unsigned long long>(0))
		{
			fprintf(stderr, "MBBPS_matrix degree-trail epoch overflow\n");
			exit(1);
		}
		checkpoint.trail_size = degree_trail.size();
		checkpoint.parent_epoch = current_degree_epoch;
		checkpoint.epoch = next_degree_epoch++;
		checkpoint.active = true;
		current_degree_epoch = checkpoint.epoch;

		return checkpoint;
	}

	inline void decrement_degree_by(ui v, ui delta)
	{
		assert(delta > 0);
		// level_id[v] < n means that v has already been committed to the
		// current deletion queue.  Its transient degree is no longer used by
		// branching or pruning and the legacy implementation allowed its
		// unsigned counter to wrap until the enclosing restore rebuilt it.
		// Live vertices, however, must always retain an exact nonnegative degree.
		assert(degree[v] >= delta || level_id[v] < n);
		if (use_matrix_state_trail && current_degree_epoch != static_cast<unsigned long long>(0))
		{
			if (degree_epoch[v] != current_degree_epoch)
			{
				DegreeTrailEntry entry = {v, degree[v], degree_epoch[v]};
				degree_trail.push_back(entry);
				degree_epoch[v] = current_degree_epoch;

			}
		}
		degree[v] -= delta;
	}

	inline void decrement_degree(ui v)
	{
		decrement_degree_by(v, 1);
	}

	void rollback_degree_trail(const DegreeTrailCheckpoint &checkpoint)
	{
		if (!use_matrix_state_trail)
			return;
		assert(checkpoint.active);
		assert(current_degree_epoch == checkpoint.epoch);
		assert(degree_trail.size() >= checkpoint.trail_size);

		unsigned long long restored = 0;
		while (degree_trail.size() > checkpoint.trail_size)
		{
			const DegreeTrailEntry entry = degree_trail.back();
			degree_trail.pop_back();
			degree[entry.vertex] = entry.old_degree;
			degree_epoch[entry.vertex] = entry.old_epoch;
			++restored;
		}
		current_degree_epoch = checkpoint.parent_epoch;

	}

	void discard_degree_trail()
	{
		degree_trail.clear();
		current_degree_epoch = 0;
	}

	void build_active_bits(ui S_end, ui R_end)
	{

		fill(activeR_bits.begin(), activeR_bits.end(), 0);
		fill(activeS_bits.begin(), activeS_bits.end(), 0);
		for (ui i = 0; i < R_end; ++i)
			bit_set(activeR_bits, SR[i]);
		for (ui i = 0; i < S_end; ++i)
			bit_set(activeS_bits, SR[i]);
	}

	void assert_incremental_active_bits(ui S_end, ui R_end) const
	{
#ifndef NDEBUG
		if (!use_matrix_state_trail)
			return;
		for (ui v = 0; v < n; ++v)
		{
			bool in_R = SR_rid[v] < R_end;
			bool in_S = SR_rid[v] < S_end;
			if (in_R)
				assert(SR[SR_rid[v]] == v);
			assert((bit_test(activeR_bits, v) != 0) == in_R);
			assert((bit_test(activeS_bits, v) != 0) == in_S);
		}
#else
		(void)S_end;
		(void)R_end;
#endif
	}

	template <typename Func>
	void for_each_set_bit(const vector<unsigned long long> &bits, Func fn) const
	{
		for (ui w = 0; w < bitset_words; ++w)
		{
			unsigned long long x = bits[w];
			while (x)
			{
				ui b = __builtin_ctzll(x);
				ui v = (w << 6) + b;
				if (v < n)
					fn(v);
				x &= x - 1;
			}
		}
	}

	void load_graph(ui _n, const vector<pair<ui, ui>> &vp)
	{
		if (_n == 0u || _n > capacity || matrix == nullptr)
		{
			fprintf(stderr, "MBBPS_matrix::load_graph invalid size/capacity: n=%u capacity=%u\n", _n, capacity);
			exit(1);
		}
		n = _n;
		graph_prepared = false;

		if ((use_matrix_batched_degree_loss) && ((!use_matrix_state_trail)))
		{
			fprintf(stderr, "MBBPS_matrix batched degree loss requires matrix bitset and state-trail modes\n");
			exit(1);
		}

		if (!use_packed_only_adjacency && ((long long)n) * n > matrix_size)
		{
			do
			{
				matrix_size *= 2;
			} while (((long long)n) * n > matrix_size);
			delete[] matrix;
			matrix = new char[matrix_size];
		}

		if (!use_packed_only_adjacency)
			memset(matrix, 0, sizeof(char) * ((long long)n) * n);
		base_degree.assign(n, 0);
		degree_epoch.assign(n, 0);
		degree_trail.clear();
		degree_trail.reserve(vp.size());
		current_degree_epoch = 0;
		next_degree_epoch = 1;
		loss_count.assign(n, 0);
		loss_epoch.assign(n, 0);
		wave_original_rid.assign(n, 0);
		wave_rid_epoch.assign(n, 0);
		loss_touched.clear();
		loss_touched.reserve(n);
		removed_wave_vertices.clear();
		removed_wave_vertices.reserve(n);
		next_loss_epoch = 1;
		prepared_edges.clear();
		prepared_edges.reserve(vp.size());
		{
			bitset_words = (n + 63) >> 6;
			adj_bits.assign((size_t)n * bitset_words, 0);
			activeR_bits.assign(bitset_words, 0);
			activeS_bits.assign(bitset_words, 0);
			reached_bits.assign(bitset_words, 0);
			frontier_bits.assign(bitset_words, 0);
			scratch_bits.assign(bitset_words, 0);
			removed_wave_bits.assign(bitset_words, 0);
		}
		unsigned long long duplicate_edges = 0;
		unsigned long long self_loops = 0;
		for (ui i = 0; i < vp.size(); i++)
		{
			assert(vp[i].first < n && vp[i].second < n);
			ui a = vp[i].first, b = vp[i].second;
			if (a == b)
			{
				++self_loops;
				continue;
			}
			if (adjacent(a, b))
			{
				++duplicate_edges;
				continue;
			}

			if (!use_packed_only_adjacency)
				matrix[(size_t)a * n + b] = matrix[(size_t)b * n + a] = 1;
			++base_degree[a];
			++base_degree[b];
			prepared_edges.push_back(make_pair(a, b));
			{
				adj_bits[(size_t)a * bitset_words + (b >> 6)] |= bit_mask(b);
				adj_bits[(size_t)b * bitset_words + (a >> 6)] |= bit_mask(a);
			}
		}

		// Build a compact immutable CSR from exactly the same accepted simple
		// edges as the byte matrix and packed bit rows.
		local_pstart.assign(n + 1, 0);
		for (const auto &edge : prepared_edges)
		{
			++local_pstart[edge.first + 1];
			++local_pstart[edge.second + 1];
		}
		for (ui i = 1; i <= n; ++i)
			local_pstart[i] += local_pstart[i - 1];
		local_edges.assign(local_pstart[n], 0);
		vector<ui> cursor(local_pstart.begin(), local_pstart.end());
		for (const auto &edge : prepared_edges)
		{
			local_edges[cursor[edge.first]++] = edge.second;
			local_edges[cursor[edge.second]++] = edge.first;
		}

		build_static_core();
		graph_prepared = true;

	}

	void find_feasible(ui S_, ui size_UB_, vector<ui> &feasible_solution, bool must_include_0)
	{
		if (!graph_prepared)
		{
			fprintf(stderr, "MBBPS_matrix::find_feasible called before load_graph\n");
			exit(1);
		}

		search_nodes_visited = 0;
		search_node_limit_exhausted = false;

		S = S_;
		_size_UB_ = size_UB_;

		optimal_sol_size = feasible_solution.size();
		ui R_end;

		initialization(R_end, must_include_0);

		try
		{
			if (R_end && optimal_sol_size < _size_UB_)
				BB_search(0, R_end, 1, must_include_0);
		}
		catch (const SearchNodeBudgetExhausted &)
		{
			search_node_limit_exhausted = true;
		}
		catch (const BatchedDegreeInvariantViolation &violation)
		{

			// The wave has already changed SR/active bits when the invariant is detected.
			// Reinitializing from the immutable prepared graph is safer than attempting
			// a partial in-place repair. Keep any valid incumbent found before the restart,
			// but disable WB-DLP for the remainder of this query.
			use_matrix_batched_degree_loss = false;
			use_matrix_state_trail = false;
			discard_degree_trail();
			initialization(R_end, must_include_0);
			if (R_end && optimal_sol_size < _size_UB_)
				BB_search(0, R_end, 1, must_include_0);
		}
		catch (const DegreeInSInvariantViolation &violation)
		{

			use_matrix_batched_degree_loss = false;
			use_matrix_state_trail = false;
			discard_degree_trail();
			initialization(R_end, must_include_0);
			if (R_end && optimal_sol_size < _size_UB_)
				BB_search(0, R_end, 1, must_include_0);
		}

		if (use_matrix_state_trail && optimal_sol_size < _size_UB_ &&
			!search_node_limit_exhausted)
		{
			assert(current_degree_epoch == 0);
			assert(degree_trail.empty());
		}
		// Reaching the requested UB intentionally short-circuits recursive
		// restores.  The next trial rebuilds root state, so discard any dirty
		// scope metadata here rather than carrying epochs across S trials.
		discard_degree_trail();
		if (optimal_sol_size > feasible_solution.size())
		{
			feasible_solution.clear();
			for (int i = 0; static_cast<ui>(i) < optimal_sol_size; i++)
				feasible_solution.push_back(best_solution[i]);
		}
	}

private:
	// Compute the local core numbers once from the immutable CSR.  A lazy
	// min-heap preserves the old minimum-degree/vertex-id tie rule while
	// reducing the former quadratic scan to sparse O((n+m) log n) work.
	void build_static_core()
	{
		cached_core.assign(n, 0);
		cached_peel_sequence.assign(n, 0);
		vector<ui> work_degree = base_degree;
		vector<char> removed(n, 0);
		using HeapEntry = pair<ui, ui>;
		priority_queue<HeapEntry, vector<HeapEntry>, greater<HeapEntry>> heap;
		for (ui u = 0; u < n; ++u)
			heap.push(make_pair(work_degree[u], u));

		ui max_core = 0;
		ui peeled = 0;
		while (!heap.empty() && peeled < n)
		{
			ui key = heap.top().first;
			ui u = heap.top().second;
			heap.pop();
			if (removed[u] || key != work_degree[u])
				continue;

			removed[u] = 1;
			if (key > max_core)
				max_core = key;
			cached_core[u] = max_core;
			cached_peel_sequence[peeled++] = u;
			for (ui pos = local_pstart[u]; pos < local_pstart[u + 1]; ++pos)
			{
				ui v = local_edges[pos];
				if (!removed[v])
				{
					assert(work_degree[v] > 0);
					--work_degree[v];
					heap.push(make_pair(work_degree[v], v));
				}
			}
		}
		assert(peeled == n);
	}

	void initialization(ui &R_end, bool must_include_0)
	{
		assert(graph_prepared && cached_core.size() == n);
		while (!Qv.empty())
			Qv.pop();

		memset(degree, 0, sizeof(ui) * n);
		memset(degree_in_S, 0, sizeof(ui) * n);
		if (use_matrix_state_trail)
		{
			fill(degree_epoch.begin(), degree_epoch.end(), 0);
			degree_trail.clear();
			current_degree_epoch = 0;
			next_degree_epoch = 1;
		}
		for (ui i = 0; i < n; ++i)
		{
			SR_rid[i] = n;
			level_id[i] = 0;
		}
		{
			fill(activeR_bits.begin(), activeR_bits.end(), 0);
			fill(activeS_bits.begin(), activeS_bits.end(), 0);
			fill(reached_bits.begin(), reached_bits.end(), 0);
			fill(frontier_bits.begin(), frontier_bits.end(), 0);
			fill(scratch_bits.begin(), scratch_bits.end(), 0);
		}

		R_end = 0;
		for (ui i = 0; i < n; i++)
			if (cached_core[i] + S > optimal_sol_size)
			{
				SR[R_end] = i;
				SR_rid[i] = R_end;
				++R_end;
			}

		if ((must_include_0 && SR_rid[0] == n) || optimal_sol_size >= _size_UB_)
		{
			R_end = 0;
			return;
		}

		for (const auto &edge : prepared_edges)
		{
			ui u = edge.first, v = edge.second;
			if (SR_rid[u] < R_end && SR_rid[v] < R_end)
			{
				++degree[u];
				++degree[v];
			}
		}

		for (ui i = 0; i < R_end; i++)
			level_id[SR[i]] = n;

		if (use_matrix_state_trail)
			build_active_bits(0, R_end);

		if (!remove_vertices_and_edges_with_prune(0, R_end, 0))
		{
			R_end = 0;
			if (use_matrix_state_trail)
			{
				fill(activeR_bits.begin(), activeR_bits.end(), 0);
				fill(activeS_bits.begin(), activeS_bits.end(), 0);
			}
		}
		assert_incremental_active_bits(0, R_end);
		// Root reductions are committed. Search checkpoints start from this
		// already-reduced degree state.
		discard_degree_trail();
	}

	void store_solution(ui size, bool is_R_end)
	{
		if (size <= optimal_sol_size)
		{
			printf("!!! the solution to store is no larger than the current optimal solution!");
			return;
		}

		if (is_R_end)
		{
			vector<bool> visited(size, false);
			function<void(int)> dfs = [&](int vertex)
			{
				visited[vertex] = true;
				for (int i = 0; static_cast<ui>(i) < size; ++i)
					if (adjacent(SR[vertex], SR[i]) && !visited[i])
						dfs(i);
			};

			dfs(0);

			vector<ui> t_solution;
			for (int i = 0; static_cast<ui>(i) < size; i++)
				if (visited[i])
					t_solution.push_back(SR[i]);

			// R can be feasible before it has been reduced to the requested UB.
			// Retain a connected query-containing induced subgraph of size UB by
			// repeatedly deleting a non-query DFS leaf.  Vertex deletion preserves
			// the S-plex inequality because degree and required degree fall together.
			while (t_solution.size() > _size_UB_)
			{
				vector<int> order;
				vector<char> seen(t_solution.size(), 0);
				vector<int> stack(1, 0);
				seen[0] = 1;
				while (!stack.empty())
				{
					int u = stack.back();
					stack.pop_back();
					order.push_back(u);
					for (int v = (int)t_solution.size() - 1; v >= 0; --v)
						if (!seen[v] && adjacent(t_solution[u], t_solution[v]))
						{
							seen[v] = 1;
							stack.push_back(v);
						}
				}
				assert(order.size() == t_solution.size());
				assert(order.back() != 0);
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
					if (adjacent(SR[vertex], SR[i]) && !visited[i])
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
				optimal_sol_size = size;
				for (ui i = 0; i < optimal_sol_size; i++)
					best_solution[i] = SR[i];
			}
		}
		assert(optimal_sol_size <= _size_UB_);

	}

	bool is_desired_feasible_sol(ui R_end)
	{
		for (ui i = 0; i < R_end; i++)
			if (degree[SR[i]] + S < R_end)
				return false;
		return true;
	}

	// Exact relaxation of two selected-vertex non-neighbor capacities.
	//
	// For selected u and v, partition C into candidates adjacent to both
	// (c00), non-adjacent only to u (c10), non-adjacent only to v (c01),
	// and non-adjacent to both (c11).  Ignoring all other constraints, the
	// maximum number that can be added is
	//
	// c00 + a + b + min(c11, bu-a, bv-b),
	//
	// where a=min(c10,bu), b=min(c01,bv), and bu/bv are the remaining
	// non-neighbor capacities of u/v.  This is an upper bound on every
	// feasible descendant, so pruning cannot remove an improving solution.
	bool adaptive_triple_capacity_bound_prunes(ui S_end,
											 ui best_u, ui best_v, ui best_w,
											 ui pair_node_ub)
	{
		(void)pair_node_ub; // Checked by the bound invariant.
		if ((best_w == n) || (S_end < 3u))
			return false;

		ui budgets[3] = {
			S + degree_in_S[best_u] - S_end,
			S + degree_in_S[best_v] - S_end,
			S + degree_in_S[best_w] - S_end};
		const unsigned long long dp_state_work =
			(unsigned long long)(budgets[0] + 1ull) *
			(unsigned long long)(budgets[1] + 1ull) *
			(unsigned long long)(budgets[2] + 1ull);
		if (!ledger_probe_due(dp_state_work, work_ledger.dp_state_credit,
				triple_ledger_runs, triple_ledger_skips, triple_probe_interval))
		{

			return false;
		}
		{ ledger_probe_started(dp_state_work, work_ledger.dp_state_credit,
				triple_ledger_runs, triple_ledger_skips); }

		Timer bound_timer;

		ui counts[8] = {0, 0, 0, 0, 0, 0, 0, 0};
#ifndef NDEBUG
		ui active_candidate_count = 0;
#endif
		const unsigned long long *rows[3] = {
			&adj_bits[(size_t)best_u * bitset_words],
			&adj_bits[(size_t)best_v * bitset_words],
			&adj_bits[(size_t)best_w * bitset_words]};
		for (ui word = 0; word < bitset_words; ++word)
		{
			unsigned long long candidates = activeR_bits[word] & ~activeS_bits[word];
#ifndef NDEBUG
			active_candidate_count += __builtin_popcountll(candidates);
#endif
			for (ui mask = 0; mask < 8u; ++mask)
			{
				unsigned long long atom = candidates;
				for (ui row = 0; row < 3u; ++row)
					atom &= (mask & (1u << row)) ? ~rows[row][word] : rows[row][word];
				counts[mask] += __builtin_popcountll(atom);
			}
		}

#ifndef NDEBUG
		ui classified = 0;
		for (ui mask = 0; mask < 8u; ++mask)
			classified += counts[mask];
		assert(classified == active_candidate_count);
#endif
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

		{ ledger_probe_finished(hit, result.dp_states,
				work_ledger.dp_state_credit, triple_ledger_runs,
				triple_probe_interval); }

		return (hit);
	}

	// AQER residual-capacity certificate.
	//
	// Let b(v)=S+deg_S(v)-|S| be the remaining number of non-neighbors that
	// a selected vertex v can tolerate in every feasible descendant.  For a
	// selected subset T, every feasible extension X must satisfy
	//
	//   sum_{x in X} |T \\ N(x)| <= sum_{v in T} b(v).
	//
	// Relaxing the individual capacities to this one aggregate capacity gives
	// a safe cardinality upper bound: take candidate vertices in increasing
	// order of their number of misses into T until the aggregate budget is
	// exhausted.  A violation certifies that the whole branch cannot improve
	// the incumbent.  Pair/three-vertex bounds are tried first; this certificate
	// is reserved for their near-miss nodes and uses one global work cap.

	bool pair_capacity_bound_prunes(ui S_end, ui R_end)
	{
		if ((S_end < 2u) || (R_end <= S_end))
			return false;
		// A miss is comparable only within the same active-candidate regime.
		// Changing C resets the exponential probe interval without a tuned window.
		const ui current_candidate_count = R_end - S_end;
		if (current_candidate_count != pair_last_candidate_count)
		{
			pair_last_candidate_count = current_candidate_count;
			pair_probe_interval = 1;
			pair_ledger_skips = 0;
		}
		// Production probes use native packed-word work. The first eligible
		// node is sampled; later misses back off 1,2,4,... while hits credit
		// one avoided active-candidate word scan.
		const bool pair_work_skip = (!ledger_probe_due(bitset_words, work_ledger.word_op_credit,
				pair_ledger_runs, pair_ledger_skips, pair_probe_interval));
		if (pair_work_skip)
		{

			return false;
		}
		{ ledger_probe_started(bitset_words, work_ledger.word_op_credit,
				pair_ledger_runs, pair_ledger_skips); }

		Timer bound_timer;
		// Stateless packed mode intentionally does not maintain activeR/S across
		// recursive mutations.  HECUB still consumes the same immutable packed
		// adjacency, but rebuilds the current active masks from SR at each probe.

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

		ui budget_u = S + degree_in_S[best_u] - S_end;
		ui budget_v = S + degree_in_S[best_v] - S_end;
		ui neighbors_u = degree[best_u] - degree_in_S[best_u];
		ui neighbors_v = degree[best_v] - degree_in_S[best_v];
		ui common_neighbors = 0;
		const unsigned long long *u_bits = &adj_bits[(size_t)best_u * bitset_words];
		const unsigned long long *v_bits = &adj_bits[(size_t)best_v * bitset_words];
		for (ui word = 0; word < bitset_words; ++word)
		{
			unsigned long long candidates = activeR_bits[word] & ~activeS_bits[word];
			common_neighbors += __builtin_popcountll(u_bits[word] & v_bits[word] & candidates);
		}

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

		{
			const unsigned long long avoided_word_ops =
				((unsigned long long)C_size + 63ull) >> 6;
			ledger_probe_finished(hit, avoided_word_ops,
				work_ledger.word_op_credit, pair_ledger_runs,
				pair_probe_interval);
		}

		bool triple_prunes = false;
		if (!hit && node_ub == optimal_sol_size + 1)
			triple_prunes = adaptive_triple_capacity_bound_prunes(
				S_end, best_u, best_v, best_w, node_ub);
		bool residual_prunes = false;

		return ((hit)) || triple_prunes || residual_prunes;
	}

	void BB_search(ui S_end, ui R_end, ui level, bool choose_zero)
	{
		if (search_node_limit != static_cast<unsigned long long>(0) && search_nodes_visited >= search_node_limit)
			throw SearchNodeBudgetExhausted();
		++search_nodes_visited;

		if (S_end > optimal_sol_size)
			store_solution(S_end, false);
		if (R_end > optimal_sol_size && is_desired_feasible_sol(R_end))
			store_solution(R_end, true);
		if (R_end <= optimal_sol_size + 1 || optimal_sol_size >= _size_UB_)
			return;

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(t_matrix[SR[j]]);
			}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif

		ui old_S_end = S_end, old_R_end = R_end;
		DegreeTrailCheckpoint old_degree_state = begin_degree_trail_scope();
		assert(Qv.empty());
		if (choose_zero && SR_rid[0] < R_end)
		{
			bool succeed = move_u_to_S_with_prune(0, S_end, R_end, level);
			if (succeed)
				succeed = delete_vertices_based_on_dist(S_end, R_end, level);
			if (!succeed)
			{
				restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
				return;
			}
		}

		// Try the cheap two-constraint certificate before RR1.  On proof
		// nodes this can avoid sorting and scanning the full candidate set.
		if (pair_capacity_bound_prunes(S_end, R_end))
		{
			restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
			return;
		}

#ifdef _REDUCTION_RULE_
		if (S_end >= 2u)
		{
			{ missing_edge_based_reduction_rule(S_end, R_end, level); }
			bool rr1_succeed;
			{ rr1_succeed = remove_vertices_and_edges_with_prune(S_end, R_end, level); }
			if (!rr1_succeed)
			{
				restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
				return;
			}
		}
#endif

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(t_matrix[SR[j]]);
			}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif

		for (ui i = 0; i < S_end; i++)
		{
			ui u = SR[i];
			if (degree[u] == optimal_sol_size - S + 1)
			{

				for (ui j = S_end; j < R_end; ++j)
				{
					ui w = SR[j];
					if (adjacent(u, w))
					{
						bool succeed = move_u_to_S_with_prune(w, S_end, R_end, level);
						if (succeed)
							succeed = delete_vertices_based_on_dist(S_end, R_end, level);
						if (!succeed)
						{

							restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
							return;
						}
					}
				}
			}
		}

		if (S_end > optimal_sol_size)
			store_solution(S_end, false);
		if (R_end > optimal_sol_size && is_desired_feasible_sol(R_end))
			store_solution(R_end, true);
		if (R_end <= optimal_sol_size + 1 || optimal_sol_size >= _size_UB_)
		{
			restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
			return;
		}

		if (pair_capacity_bound_prunes(S_end, R_end))
		{
			restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
			return;
		}

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(t_matrix[SR[j]]);
			}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(t_matrix[SR[j]]);
			}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif

		ui u;
		{ u = choose_branch_vertex(S_end, R_end); }
		if (degree[u] + S <= optimal_sol_size || degree[u] + S <= S_end)
		{
			restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
			return;
		}
		ui capacity_watch_u;
		vector<ui> capacity_D;
		if (collect_capacity_b1_branch_set(S_end, R_end, u, capacity_watch_u, capacity_D))
		{
			capacity_b1_set_branch(S_end, R_end, level, capacity_D);
			if (optimal_sol_size >= _size_UB_)
				return;
			restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);
			return;
		}

		ui pre_best_solution_size = optimal_sol_size, t_old_S_end = S_end, t_old_R_end = R_end;
		DegreeTrailCheckpoint include_degree_state = begin_degree_trail_scope();

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(t_matrix[SR[j]]);
			}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif
		bool include_succeed;
		{
			include_succeed = move_u_to_S_with_prune(u, S_end, R_end, level);
			if (include_succeed)
			{
				if (pair_capacity_bound_prunes(S_end, R_end))
					include_succeed = false;
				else
					include_succeed = delete_vertices_based_on_dist(S_end, R_end, level);
			}
		}

		if (include_succeed)
		{
#ifndef NDEBUG
			for (ui i = 0; i < R_end; i++)
			{
				ui d1 = 0, d2 = 0;
				for (ui j = 0; j < S_end; j++)
					if (adjacent(SR[i], SR[j]))
						++d1;
				d2 = d1;
				for (ui j = S_end; j < R_end; j++)
					if (adjacent(SR[i], SR[j]))
						++d2;
				assert(d1 == degree_in_S[SR[i]]);
				assert(d2 == degree[SR[i]]);
			}
			for (ui i = 0; i < S_end; i++)
				assert(degree_in_S[SR[i]] + S >= S_end);
			for (ui i = S_end; i < R_end; i++)
				assert(degree_in_S[SR[i]] + S > S_end);
			for (ui i = 0; i < S_end; i++)
				if (degree_in_S[SR[i]] + S == S_end)
				{
					AdjacencyRowView t_matrix(this, SR[i]);
					for (ui j = S_end; j < R_end; j++)
						assert(t_matrix[SR[j]]);
				}
			for (ui i = 0; i < R_end; i++)
				assert(level_id[SR[i]] > level);
#endif
			BB_search(S_end, R_end, level + 1, false);
		}

		if (optimal_sol_size >= _size_UB_)
		{

			return;
		}
		bool include_moved_u_to_S = (S_end == t_old_S_end + 1 && SR[S_end - 1] == u);
		if (include_moved_u_to_S)
			restore_SR_and_edges(S_end, R_end, S_end, t_old_R_end, level, include_degree_state);
		else
		{
			rollback_degree_trail(include_degree_state);
			assert(S_end == t_old_S_end && R_end == t_old_R_end && SR_rid[u] >= S_end && SR_rid[u] < R_end);
		}

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif

		assert(Qv.empty());
		bool succeed;
		if (include_moved_u_to_S)
		{
			{
				succeed = remove_u_from_S_with_prune(S_end, R_end, level);
				if (succeed && optimal_sol_size > pre_best_solution_size)
					succeed = collect_removable_vertices_and_edges(S_end, R_end, level);
				if (succeed)
					succeed = remove_vertices_and_edges_with_prune(S_end, R_end, level);
			}
		}
		else
		{
			{
				assert(level_id[u] > level);
				level_id[u] = level;
				Qv.push(u);
				succeed = remove_vertices_and_edges_with_prune(S_end, R_end, level);
			}
		}

#ifndef NDEBUG
		if (succeed)
		{
			for (ui i = 0; i < R_end; i++)
			{
				ui d1 = 0, d2 = 0;
				for (ui j = 0; j < S_end; j++)
					if (adjacent(SR[i], SR[j]))
						++d1;
				d2 = d1;
				for (ui j = S_end; j < R_end; j++)
					if (adjacent(SR[i], SR[j]))
						++d2;
				assert(d1 == degree_in_S[SR[i]]);
				assert(d2 == degree[SR[i]]);
			}
			for (ui i = 0; i < S_end; i++)
				assert(degree_in_S[SR[i]] + S >= S_end);
			for (ui i = S_end; i < R_end; i++)
				assert(degree_in_S[SR[i]] + S > S_end);
			for (ui i = 0; i < S_end; i++)
				if (degree_in_S[SR[i]] + S == S_end)
				{
					AdjacencyRowView t_matrix(this, SR[i]);
					for (ui j = S_end; j < R_end; j++)
						assert(t_matrix[SR[j]]);
				}
			for (ui i = 0; i < R_end; i++)
				assert(level_id[SR[i]] > level);
		}
#endif

		if (succeed)
		{
#ifndef NDEBUG
			for (ui i = 0; i < R_end; i++)
			{
				ui d1 = 0, d2 = 0;
				for (ui j = 0; j < S_end; j++)
					if (adjacent(SR[i], SR[j]))
						++d1;
				d2 = d1;
				for (ui j = S_end; j < R_end; j++)
					if (adjacent(SR[i], SR[j]))
						++d2;
				assert(d1 == degree_in_S[SR[i]]);
				assert(d2 == degree[SR[i]]);
			}
			for (ui i = 0; i < S_end; i++)
				assert(degree_in_S[SR[i]] + S >= S_end);
			for (ui i = S_end; i < R_end; i++)
				assert(degree_in_S[SR[i]] + S > S_end);
			for (ui i = 0; i < S_end; i++)
				if (degree_in_S[SR[i]] + S == S_end)
				{
					AdjacencyRowView t_matrix(this, SR[i]);
					for (ui j = S_end; j < R_end; j++)
						assert(t_matrix[SR[j]]);
				}
			for (ui i = 0; i < R_end; i++)
				assert(level_id[SR[i]] > level);
#endif

			BB_search(S_end, R_end, level + 1, false);
		}

		if (optimal_sol_size >= _size_UB_)
			return;
		assert(S_end >= old_S_end && R_end <= old_R_end);

		restore_SR_and_edges(S_end, R_end, old_S_end, old_R_end, level, old_degree_state);

#ifndef NDEBUG
		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(t_matrix[SR[j]]);
			}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
#endif
	}

	inline bool matrix_rr1_bucket_bitset_stack_enabled() const
	{
		// WB-DLP may be conservatively disabled for a large sparse/high-slack
		// graph while the active-set kernels and State Trail remain valid.  This
		// RR1 backend belongs to that retained UISM state, not to Wave itself.
		return use_matrix_rr1_bucket_bitset &&
			matrix_bitset_search_kernels_enabled() &&
			use_matrix_state_trail;
	}

	bool matrix_rr1_bucket_bitset_worthwhile(ui candidate_n, ui max_miss_edges) const
	{
		if (candidate_n < 1024u || bitset_words == 0u)
			return false;

		const unsigned __int128 bucket_n =
			(unsigned __int128)max_miss_edges + 1;
		const unsigned __int128 bucket_words =
			bucket_n * (unsigned __int128)bitset_words;
		const unsigned __int128 scratch_bytes =
			2 * bucket_words * sizeof(unsigned long long) +
			2 * bucket_n * sizeof(ui) +
			(bucket_n + 1) * sizeof(ui) +
			(unsigned __int128)candidate_n * sizeof(ui);
		const unsigned __int128 scratch_limit =
			(unsigned __int128)ARCSCSMemoryLimits::auxiliary_bytes;
		if (scratch_bytes > scratch_limit)
			return false;

		// Every candidate occupies one (bucket,word) pair, hence this is a safe
		// upper bound without constructing the backend.  Require a conservative
		// 2x structural advantage so ordinary/small Matrix states stay on their
		// original scalar loop.
		const unsigned __int128 occupied_upper =
			std::min<unsigned __int128>(candidate_n, bucket_words);
		const unsigned __int128 bitset_work =
			2 * bucket_words + candidate_n +
			(unsigned __int128)candidate_n * (bucket_n + occupied_upper);
		const unsigned __int128 scalar_work =
			(unsigned __int128)candidate_n * candidate_n;
		return 2 * bitset_work < scalar_work;
	}

	__attribute__((noinline))
	void matrix_rr1_condition2_bucket_bitset(
		ui S_end, ui level, ui *ids, ui ids_n,
		ui total_budget, ui max_miss_edges)
	{

		const ui bucket_n = max_miss_edges + 1;
		const size_t bucket_words = (size_t)bucket_n * bitset_words;
		rr1_bucket_future_bits.assign(bucket_words, 0);
		rr1_bucket_kept_bits.assign(bucket_words, 0);
		rr1_bucket_future_count.assign(bucket_n, 0);
		rr1_bucket_kept_count.assign(bucket_n, 0);
		rr1_bucket_word_offsets.assign(bucket_n + 1, 0);
		rr1_bucket_word_ids.clear();
		if (rr1_bucket_word_ids.capacity() < ids_n)
			rr1_bucket_word_ids.reserve(ids_n);

#ifndef NDEBUG
		ui previous_miss = 0;
#endif
		for (ui i = 0; i < ids_n; ++i)
		{
			const ui idx = ids[i];
			const ui v = vp[idx].first;
			const ui miss_edges = vp[idx].second;
#ifndef NDEBUG
			assert(i == 0 || previous_miss <= miss_edges);
			previous_miss = miss_edges;
#endif
			const ui word = v >> 6;
			unsigned long long *row =
				&rr1_bucket_future_bits[(size_t)miss_edges * bitset_words];
			if (row[word] == static_cast<unsigned long long>(0))
			{
				++rr1_bucket_word_offsets[miss_edges + 1];
				rr1_bucket_word_ids.push_back(word);
			}
			row[word] |= bit_mask(v);
			++rr1_bucket_future_count[miss_edges];
		}
		for (ui d = 0; d < bucket_n; ++d)
			rr1_bucket_word_offsets[d + 1] +=
				rr1_bucket_word_offsets[d];
		assert(rr1_bucket_word_offsets[bucket_n] ==
			rr1_bucket_word_ids.size());

		ui new_n = 0;
		ui removed_n = 0;
		unsigned long long bucket_visits = 0;
		unsigned long long word_ops = 0;
		for (ui i = 0; i < ids_n; ++i)
		{
			const ui idx = ids[i];
			const ui v = vp[idx].first;
			const ui v_miss_edges = vp[idx].second;
			unsigned long long *current_future =
				&rr1_bucket_future_bits[
					(size_t)v_miss_edges * bitset_words];
			current_future[v >> 6] &= ~bit_mask(v);
			assert(rr1_bucket_future_count[v_miss_edges] > 0);
			--rr1_bucket_future_count[v_miss_edges];

			assert(total_budget >= v_miss_edges);
			ui t_budget = total_budget - v_miss_edges;
			ui num = S_end + 1;
			ui v_budget = S - 1 - S_end + degree_in_S[v];
			const unsigned long long *v_bits =
				&adj_bits[(size_t)v * bitset_words];

			for (ui d = 0; d < bucket_n; ++d)
			{
				if (num > optimal_sol_size)
					break;
				if (d != 0u && t_budget < d)
					break;
				const ui bucket_total =
					rr1_bucket_future_count[d] +
					rr1_bucket_kept_count[d];
				if (bucket_total == 0u)
					continue;

				++bucket_visits;
				const ui word_begin = rr1_bucket_word_offsets[d];
				const ui word_end = rr1_bucket_word_offsets[d + 1];
				word_ops += word_end - word_begin;
				const unsigned long long *future_row =
					&rr1_bucket_future_bits[(size_t)d * bitset_words];
				const unsigned long long *kept_row =
					&rr1_bucket_kept_bits[(size_t)d * bitset_words];
				ui adjacent_count = 0;
				for (ui k = word_begin; k < word_end; ++k)
				{
					const ui word = rr1_bucket_word_ids[k];
					adjacent_count += (ui)__builtin_popcountll(
						v_bits[word] &
						(future_row[word] | kept_row[word]));
				}

				const ui nonadjacent_count =
					bucket_total - adjacent_count;
				const ui nonadjacent_includable =
					std::min(nonadjacent_count, v_budget);
				const ui includable =
					adjacent_count + nonadjacent_includable;
				if (includable == 0u)
					continue;

				if (d == 0u)
				{
					num += includable;
					v_budget -= nonadjacent_includable;
					continue;
				}

				const ui budget_limited = t_budget / d;
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
			{
				level_id[v] = level;
				Qv.push(v);
				++removed_n;

			}
			else
			{
				ids[new_n++] = idx;
				unsigned long long *current_kept =
					&rr1_bucket_kept_bits[
						(size_t)v_miss_edges * bitset_words];
				current_kept[v >> 6] |= bit_mask(v);
				++rr1_bucket_kept_count[v_miss_edges];
			}
		}

	}

	void missing_edge_based_reduction_rule(ui S_end, ui R_end, ui level)
	{

		vp.resize(R_end - S_end);
		ui max_miss_edges = 0;
		{
			for (ui i = S_end; i < R_end; i++)
			{
				ui v = SR[i];
				if (degree_in_S[v] > S_end)
				{
					if (use_matrix_state_trail)
					{
						DegreeInSInvariantViolation violation = {
							v, degree_in_S[v], S_end, level};
						throw violation;
					}

					degree_in_S[v] = 0;
					AdjacencyRowView v_matrix(this, v);
					for (ui j = 0; j < S_end; ++j)
						if (v_matrix[SR[j]])
							++degree_in_S[v];

				}
				ui miss_edges = S_end - degree_in_S[v];
				if (miss_edges > max_miss_edges)
					max_miss_edges = miss_edges;
				vp[i - S_end].first = v;
				vp[i - S_end].second = miss_edges;
			}
		}

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
			total_budget += S - S_end + degree_in_S[SR[i]];

		ui new_n = 0;
		while (!Qv.empty())
			Qv.pop();
		const bool rr1_bitset_eligible =
			matrix_rr1_bucket_bitset_stack_enabled() &&
			vp.size() >= 1024u &&
			S_end + 1 <= optimal_sol_size;
		const bool use_rr1_bucket_bitset =
			rr1_bitset_eligible &&
			matrix_rr1_bucket_bitset_worthwhile(
				(ui)vp.size(), max_miss_edges);

		if (use_rr1_bucket_bitset)
		{
			matrix_rr1_condition2_bucket_bitset(
				S_end, level, ids, (ui)vp.size(),
				total_budget, max_miss_edges);
			return;
		}
		for (ui i = 0; i < vp.size(); i++)
		{
			ui idx = ids[i], v = vp[ids[i]].first;
			ui t_budget = total_budget - vp[idx].second;
			AdjacencyRowView t_matrix(this, v);

			ui num = S_end + 1;
			{
				ui j = 0, v_budget = S - 1 - S_end + degree_in_S[v];
				while (true)
				{
					if (j == new_n)
						j = i + 1;
					if (j >= vp.size() || num > optimal_sol_size || num + vp.size() - j <= optimal_sol_size)
						break;
					ui u = vp[ids[j]].first, miss_edges = vp[ids[j]].second;
					if (t_budget < miss_edges)
						break;
					if (t_matrix[u])
					{
						t_budget -= miss_edges;
						++num;
					}
					else if (v_budget > 0u)
					{
						--v_budget;
						t_budget -= miss_edges;
						++num;
					}
					++j;
				}
			}

			if (num <= optimal_sol_size)
			{
				{
					level_id[v] = level;
					Qv.push(v);
				}
			}
			else
				ids[new_n++] = ids[i];
		}
	}

	void get_neighbors_and_nonneighbors(ui u, ui R_end, ui &neighbors_n, ui &nonneighbors_n)
	{
		neighbors_n = 0;
		nonneighbors_n = 0;
		AdjacencyRowView t_matrix(this, u);
		for (ui i = 0; i < R_end; i++)
			if (SR[i] != u)
			{
				if (t_matrix[SR[i]])
					neighbors[neighbors_n++] = SR[i];
				else
					nonneighbors[nonneighbors_n++] = SR[i];
			}
	}

	bool move_u_to_S_with_prune(ui u, ui &S_end, ui &R_end, ui level)
	{

		assert(SR_rid[u] >= S_end && SR_rid[u] < R_end && SR[SR_rid[u]] == u);
		if (degree_in_S[u] + S <= S_end)
		{

			return false;
		}
#ifndef NDEBUG

		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);

#endif

		if (SR_rid[u] != S_end)
			swap_pos(S_end, SR_rid[u]);
		++S_end;
		if (use_matrix_state_trail)
			bit_set(activeS_bits, u);

		ui neighbors_n = 0, nonneighbors_n = 0;

		get_neighbors_and_nonneighbors(u, R_end, neighbors_n, nonneighbors_n);

		assert(neighbors_n + nonneighbors_n == R_end - 1);

		for (ui i = 0; i < neighbors_n; i++)
			++degree_in_S[neighbors[i]];

#ifndef NDEBUG

		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);

#endif

		while (!Qv.empty())
			Qv.pop();

		for (ui i = 0; i < nonneighbors_n; i++)
		{
			ui v = nonneighbors[i];
			if (SR_rid[v] >= S_end)
			{

				if (level_id[v] == level)
					continue;
				if (S_end - degree_in_S[v] >= S || S_end - degree_in_S[u] == S)
				{
					level_id[v] = level;
					Qv.push(v);
				}
			}

			else if (S_end - degree_in_S[v] == S)
			{

				AdjacencyRowView tt_matrix(this, v);

				for (ui j = S_end; j < R_end; j++)
					if (level_id[SR[j]] > level && !tt_matrix[SR[j]])
					{
						level_id[SR[j]] = level;
						Qv.push(SR[j]);
					}
			}
		}

#ifndef NDEBUG

		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(level_id[SR[j]] == level || t_matrix[SR[j]]);
			}

#endif

		bool succeed = remove_vertices_and_edges_with_prune(S_end, R_end, level);

		return succeed;
	}

	bool remove_vertices_and_edges_with_prune(ui S_end, ui &R_end, ui level)
	{
		{ return remove_vertices_and_edges_with_prune_bitset(S_end, R_end, level); }

	}

	bool remove_vertices_and_edges_with_prune_batched(ui S_end, ui &R_end, ui level)
	{
		assert(matrix_bitset_search_kernels_enabled() && use_matrix_state_trail && use_matrix_batched_degree_loss);
		assert_incremental_active_bits(S_end, R_end);

		while (!Qv.empty())
		{
			if (next_loss_epoch == static_cast<unsigned long long>(0))
			{
				fill(loss_epoch.begin(), loss_epoch.end(), 0);
				fill(wave_rid_epoch.begin(), wave_rid_epoch.end(), 0);
				next_loss_epoch = 1;
			}
			const unsigned long long wave_epoch = next_loss_epoch++;
			loss_touched.clear();
			removed_wave_vertices.clear();
			unsigned long long forward_scan_work = 0;

			// Drain exactly the vertices already scheduled for this wave.  Boundary
			// swaps and active-set clears retain their original queue order.
			while (!Qv.empty())
			{
				ui u = Qv.front();
				Qv.pop();
				assert(SR[SR_rid[u]] == u);
				assert(SR_rid[u] >= S_end && SR_rid[u] < R_end);
				ui last_vertex = SR[R_end - 1];
				if (last_vertex != u && wave_rid_epoch[last_vertex] != wave_epoch)
				{
					wave_rid_epoch[last_vertex] = wave_epoch;
					wave_original_rid[last_vertex] = R_end - 1;
				}
				--R_end;
				swap_pos(SR_rid[u], R_end);
				bit_clear(activeR_bits, u);
				bit_set(removed_wave_bits, u);
				removed_wave_vertices.push_back(u);
				const unsigned long long local_degree =
					local_pstart[u + 1] - local_pstart[u];
				forward_scan_work += std::min(local_degree,
					(unsigned long long)bitset_words);
			}

			auto record_loss = [&](ui v) {
				assert(bit_test(activeR_bits, v));
				if (loss_epoch[v] != wave_epoch)
				{
					loss_epoch[v] = wave_epoch;
					loss_count[v] = 0;
					loss_touched.push_back(v);
				}
				++loss_count[v];
			};

			unsigned long long raw_loss_events = 0;
			const unsigned long long csr_limit =
				(unsigned long long)1 * bitset_words;
			// A large deletion wave is cheaper to propagate in the transposed
			// direction: scan the surviving rows and popcount their adjacency to
			// removed_wave_bits.  Select it only when that requires strictly fewer
			// row-word visits than the forward CSR/bitset estimate.  Both directions
			// compute the same exact degree loss; the common SR-rank sort below keeps
			// the subsequent queue and search trajectory unchanged.

			const unsigned long long reverse_scan_work =
				(unsigned long long)R_end * bitset_words;
			const bool use_reverse_wave =
				reverse_scan_work < forward_scan_work;
			if (use_reverse_wave)
			{
				for (ui i = 0; i < R_end; ++i)
				{
					const ui v = SR[i];
					const unsigned long long *v_bits =
						&adj_bits[(size_t)v * bitset_words];
					ui loss = 0;
					for (ui word = 0; word < bitset_words; ++word)
						loss += __builtin_popcountll(
							v_bits[word] & removed_wave_bits[word]);
					if (loss != 0u)
					{
						loss_epoch[v] = wave_epoch;
						loss_count[v] = loss;
						loss_touched.push_back(v);
						raw_loss_events += loss;
					}
				}

			}
			else for (ui u : removed_wave_vertices)
			{
				const ui local_degree = local_pstart[u + 1] - local_pstart[u];
				if (local_degree <= csr_limit)
				{

					for (ui pos = local_pstart[u]; pos < local_pstart[u + 1]; ++pos)
					{
						ui v = local_edges[pos];
						if (bit_test(activeR_bits, v))
						{
							record_loss(v);
							++raw_loss_events;
						}
					}
				}
				else
				{

					const unsigned long long *u_bits = &adj_bits[(size_t)u * bitset_words];
					for (ui word = 0; word < bitset_words; ++word)
					{
						unsigned long long x = u_bits[word] & activeR_bits[word];
						while (x)
						{
							ui v = (word << 6) + __builtin_ctzll(x);
							assert(v < n);
							record_loss(v);
							++raw_loss_events;
							x &= x - 1;
						}
					}
				}
			}

			// Applying one aggregate delta per survivor is the only semantic change.
			// Threshold-triggered vertices are then scheduled in current SR order.
			sort(loss_touched.begin(), loss_touched.end(), [&](ui a, ui b) {
				ui a_rid = wave_rid_epoch[a] == wave_epoch ? wave_original_rid[a] : SR_rid[a];
				ui b_rid = wave_rid_epoch[b] == wave_epoch ? wave_original_rid[b] : SR_rid[b];
				return a_rid < b_rid;
			});
			for (ui v : loss_touched)
			{
				if (degree[v] < loss_count[v] && level_id[v] > level)
				{
					ui exact_after_wave = 0;
					for (ui pos = local_pstart[v]; pos < local_pstart[v + 1]; ++pos)
						if (bit_test(activeR_bits, local_edges[pos]))
							++exact_after_wave;
					BatchedDegreeInvariantViolation violation = {
						v, degree[v], loss_count[v], exact_after_wave, level};
					throw violation;
				}
				decrement_degree_by(v, loss_count[v]);
			}

			bool terminate = false;
			for (ui v : loss_touched)
			{
				if (degree[v] + S <= optimal_sol_size)
				{
					if (SR_rid[v] < S_end)
						terminate = true;
					else if (level_id[v] > level)
					{
						level_id[v] = level;
						Qv.push(v);
					}
				}
			}

			for (ui u : removed_wave_vertices)
				bit_clear(removed_wave_bits, u);

			if (terminate)
				return false;
		}
		return true;
	}

	bool remove_vertices_and_edges_with_prune_bitset(ui S_end, ui &R_end, ui level)
	{
		if (use_matrix_batched_degree_loss)
			return remove_vertices_and_edges_with_prune_batched(S_end, R_end, level);
		if (use_matrix_state_trail)
		{

			assert_incremental_active_bits(S_end, R_end);
		}
		else
			build_active_bits(S_end, R_end);
		while (!Qv.empty())
		{
			ui u = Qv.front();
			Qv.pop();
			assert(SR[SR_rid[u]] == u);
			assert(SR_rid[u] >= S_end && SR_rid[u] < R_end);
			--R_end;
			swap_pos(SR_rid[u], R_end);
			bit_clear(activeR_bits, u);

			bool terminate = false;
			ui neighbors_n = 0;
			const ui ordered_local_degree = local_pstart[u + 1] - local_pstart[u];
			const unsigned long long ordered_csr_limit =
				(unsigned long long)1 * bitset_words;
			if (use_matrix_state_trail && ordered_local_degree <= ordered_csr_limit)
			{
				for (ui pos = local_pstart[u]; pos < local_pstart[u + 1]; ++pos)
				{
					ui w = local_edges[pos];
					if (bit_test(activeR_bits, w))
						neighbors[neighbors_n++] = w;
				}

			}
			else
			{
				const unsigned long long *u_bits = &adj_bits[(size_t)u * bitset_words];
				for (ui w = 0; w < bitset_words; ++w)
					scratch_bits[w] = u_bits[w] & activeR_bits[w];
				for_each_set_bit(scratch_bits, [&](ui w) {
					neighbors[neighbors_n++] = w;
				});
			}
			sort(neighbors, neighbors + neighbors_n, [&](ui a, ui b) {
				return SR_rid[a] < SR_rid[b];
			});

			for (ui i = 0; i < neighbors_n; ++i)
			{
				ui w = neighbors[i];
				decrement_degree(w);
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

			if (terminate)
			{
				for (ui i = 0; i < neighbors_n; i++)
					++degree[neighbors[i]];
				level_id[u] = n;
				++R_end;
				bit_set(activeR_bits, u);
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
		{ return delete_vertices_based_on_dist_bitset(S_end, R_end, level); }

	}

	bool delete_vertices_based_on_dist_bitset(ui S_end, ui &R_end, ui level)
	{

		assert(S_end > 0);
		ui index = S_end - 1;

		while (true)
		{

			if (use_matrix_state_trail)
			{

				assert_incremental_active_bits(S_end, R_end);
			}
			else
			{
				build_active_bits(S_end, R_end);
				fill(reached_bits.begin(), reached_bits.end(), 0);
				fill(frontier_bits.begin(), frontier_bits.end(), 0);
			}

			ui u = SR[index];
			assert(SR_rid[u] < S_end);

			unsigned long long frontier_count = 0;
			const unsigned long long *u_bits = &adj_bits[(size_t)u * bitset_words];
			for (ui w = 0; w < bitset_words; ++w)
			{
				frontier_bits[w] = u_bits[w] & activeR_bits[w];
				if (use_matrix_state_trail)
					reached_bits[w] = frontier_bits[w];
				else
					reached_bits[w] |= frontier_bits[w];
				frontier_count += __builtin_popcountll(frontier_bits[w]);
			}
			bit_set(reached_bits, u);

			for_each_set_bit(frontier_bits, [&](ui x) {
				const unsigned long long *x_bits = &adj_bits[(size_t)x * bitset_words];
				for (ui w = 0; w < bitset_words; ++w)
					reached_bits[w] |= x_bits[w] & activeR_bits[w];
			});

			for (ui i = 0; i < R_end; ++i)
			{
				ui v = SR[i];
				if (!bit_test(reached_bits, v))
				{
					if (i < S_end)
					{

						return false;
					}
					assert(i >= S_end && level_id[v] > level);
					level_id[v] = level;
					Qv.push(v);
				}
			}

			if (Qv.empty())
			{

				return true;
			}

			bool remove_succeed = remove_vertices_and_edges_with_prune(S_end, R_end, level);

			if (!remove_succeed)
			{

				return false;
			}

			if (index > 0u)
				index--;
			else
				index = S_end - 1;
		}
	}

	void restore_SR_and_edges(ui &S_end, ui &R_end, ui old_S_end, ui old_R_end, ui level, const DegreeTrailCheckpoint &degree_state)
	{
		(void)level; // Used by restoration invariants.

#ifndef NDEBUG

		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}

#endif

		while (!Qv.empty())
		{
			ui u = Qv.front();
			Qv.pop();
			assert(level_id[u] == level);
			assert(SR_rid[u] < R_end);
			// u was marked for deletion but the enclosing branch failed before
			// u left the active prefix.  Its transient degree_in_S is no longer
			// reliable in either rollback backend, so rebuild it against the
			// tiny S prefix before making u live again.
			degree_in_S[u] = 0;
			AdjacencyRowView u_matrix(this, u);
			for (ui i = 0; i < S_end; ++i)
				if (u_matrix[SR[i]])
					++degree_in_S[u];
			level_id[u] = n;
		}

#ifndef NDEBUG

		for (ui i = 0; i < R_end; i++)
		{
			if (level_id[SR[i]] <= level)
				printf("level_id[%u] = %u, level = %u, n = %u\n", SR[i], level_id[SR[i]], level, n);
			assert(level_id[SR[i]] > level);
		}

#endif

		if (use_matrix_state_trail)
		{

			for (; R_end < old_R_end; R_end++)
			{
				ui u = SR[R_end];
				assert(level_id[u] == level && SR_rid[u] == R_end);
				level_id[u] = n;

				// degree[u] is restored by the epoch checkpoint.  A removed
				// candidate can miss vertices moved into S after its removal,
				// so rebuild only degree_in_S against the at-most-UB S prefix.
				degree_in_S[u] = 0;
				AdjacencyRowView u_matrix(this, u);
				for (ui i = 0; i < S_end; ++i)
					if (u_matrix[SR[i]])
						++degree_in_S[u];
				bit_set(activeR_bits, u);

			}
			rollback_degree_trail(degree_state);

		}
		else {

			build_active_bits(S_end, R_end);
			for (; R_end < old_R_end; R_end++)
			{
				ui u = SR[R_end];
				assert(level_id[u] == level && SR_rid[u] == R_end);
				level_id[u] = n;

				degree[u] = degree_in_S[u] = 0;
				const unsigned long long *u_bits = &adj_bits[(size_t)u * bitset_words];
				for (ui w = 0; w < bitset_words; ++w)
					scratch_bits[w] = u_bits[w] & activeR_bits[w];
				for_each_set_bit(scratch_bits, [&](ui w) {
					++degree[w];
					++degree[u];
					if (bit_test(activeS_bits, w))
						++degree_in_S[u];
				});
				bit_set(activeR_bits, u);

			}

		}

#ifndef NDEBUG

		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}

#endif

		{

			if (!(use_matrix_state_trail)) { if (activeR_bits.empty())
				build_active_bits(S_end, R_end);
			else
			{
				fill(activeS_bits.begin(), activeS_bits.end(), 0);
				for (ui i = 0; i < S_end; ++i)
					bit_set(activeS_bits, SR[i]);
			} }
			for (; S_end > old_S_end; S_end--)
			{
				ui u = SR[S_end - 1];
				assert(SR_rid[u] == S_end - 1);

				if (use_matrix_state_trail)
				{
					for (ui pos = local_pstart[u]; pos < local_pstart[u + 1]; ++pos)
					{
						ui w = local_edges[pos];
						if (bit_test(activeR_bits, w))
						{
							assert(degree_in_S[w] > 0);
							--degree_in_S[w];
						}
					}

				}
				else
				{
					const unsigned long long *u_bits = &adj_bits[(size_t)u * bitset_words];
					for (ui w = 0; w < bitset_words; ++w)
						scratch_bits[w] = u_bits[w] & activeR_bits[w];
					for_each_set_bit(scratch_bits, [&](ui w) {
						--degree_in_S[w];
					});
				}
				bit_clear(activeS_bits, u);

			}

		}

#ifndef NDEBUG

		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}

#endif

#ifndef NDEBUG

		for (ui i = 0; i < R_end; i++)
		{
			ui d1 = 0, d2 = 0;
			for (ui j = 0; j < S_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d1;
			d2 = d1;
			for (ui j = S_end; j < R_end; j++)
				if (adjacent(SR[i], SR[j]))
					++d2;
			assert(d1 == degree_in_S[SR[i]]);
			assert(d2 == degree[SR[i]]);
		}
		for (ui i = 0; i < S_end; i++)
			assert(degree_in_S[SR[i]] + S >= S_end);
		for (ui i = S_end; i < R_end; i++)
			assert(old_S_end == S_end || degree_in_S[SR[i]] + S > S_end);
		for (ui i = 0; i < S_end; i++)
			if (degree_in_S[SR[i]] + S == S_end)
			{
				AdjacencyRowView t_matrix(this, SR[i]);
				for (ui j = S_end; j < R_end; j++)
					assert(old_S_end == S_end || t_matrix[SR[j]]);
			}
		for (ui i = 0; i < R_end; i++)
			assert(level_id[SR[i]] > level);
		assert_incremental_active_bits(S_end, R_end);

#endif

	}

	bool remove_u_from_S_with_prune(ui &S_end, ui &R_end, ui level)
	{
		assert(S_end);
		ui u = SR[S_end - 1];
		--S_end;
		--R_end;
		swap_pos(S_end, R_end);
		level_id[u] = level;
		if (use_matrix_state_trail)
		{
			bit_clear(activeS_bits, u);
			bit_clear(activeR_bits, u);
		}

		bool terminate = false;
		ui neighbors_n = 0;
		AdjacencyRowView t_matrix(this, u);
		for (ui i = 0; i < R_end; i++)
			if (t_matrix[SR[i]])
				neighbors[neighbors_n++] = SR[i];
		for (ui i = 0; i < neighbors_n; i++)
		{
			ui v = neighbors[i];
			--degree_in_S[v];
			decrement_degree(v);
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

		if (terminate)
			return false;

		return true;
	}

	bool collect_removable_vertices_and_edges(ui S_end, ui R_end, ui level)
	{
		for (ui i = 0; i < S_end; i++)
			if (degree[SR[i]] + S <= optimal_sol_size)
				return false;

		for (ui i = S_end; i < R_end; i++)
			if (level_id[SR[i]] > level)
			{
				ui v = SR[i];
				if (S_end - degree_in_S[v] >= S || degree[v] + S <= optimal_sol_size)
				{
					level_id[v] = level;
					Qv.push(v);
					continue;
				}
				AdjacencyRowView t_matrix(this, v);
				for (ui j = 0; j < S_end; j++)
				{
					if (S_end - degree_in_S[SR[j]] == S && !t_matrix[SR[j]])
					{
						level_id[v] = level;
						Qv.push(v);
						break;
					}
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

	ui choose_branch_vertex(ui S_end, ui R_end)
	{
		ui v = n;
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
			AdjacencyRowView t_matrix(this, v);
			for (ui i = S_end; i < R_end; i++)
				if (!t_matrix[SR[i]] && degree[SR[i]] < t_min_deg)
				{
					v = SR[i];
					t_min_deg = degree[SR[i]];
				}
		}

		assert(v != n && SR_rid[v] >= S_end && SR_rid[v] < R_end);
		return v;
	}
};
#endif
