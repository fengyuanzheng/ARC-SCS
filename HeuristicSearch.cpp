#include "Graph.h"
#include "CapacityBound.h"

using namespace std;

void Graph::SCS_heu_star(int QID, int LB_size, int UB_size, vector<ui> &heu_solution, int &k_min, int k_max, ui *core)
{
	vector<ui> my_solution;
	ui k_min_heu = 0;
	my_heu(my_solution, k_min_heu, k_max, QID, LB_size, UB_size, core);

	if (k_min_heu > static_cast<ui>(k_min))
	{
		k_min = k_min_heu;
		heu_solution = my_solution;
	}
}

int Graph::size_aware_support_upper_bound(int QID, int UB_size,
	int incumbent_k, int original_upper, ui *core,
	unsigned long long &edge_work, bool &exact) const
{
	edge_work = 0;
	exact = false;
	if ((QID < 0) || ((ui)QID >= n) || (UB_size <= 0) || (incumbent_k >= original_upper))
		return original_upper;

	const int max_required_support =
		std::max(0, 2 * original_upper - UB_size);
	if (max_required_support == 0)
	{
		// For k<=U/2 the support condition reduces to the existing core bound.
		exact = true;
		return original_upper;
	}

	vector<ui> query_neighbors;
	query_neighbors.reserve((size_t)(pstart[QID + 1] - pstart[QID]));
	for (ept pos = pstart[QID]; pos < pstart[QID + 1]; ++pos)
	{

		++edge_work;
		const ui v = edges[pos];
		if (v < n && v != (ui)QID)
			query_neighbors.push_back(v);
	}
	std::sort(query_neighbors.begin(), query_neighbors.end());
	query_neighbors.erase(std::unique(query_neighbors.begin(),
		query_neighbors.end()), query_neighbors.end());

	struct QueryEdgeSupport
	{
		ui vertex;
		ui capped_support;
	};
	vector<QueryEdgeSupport> supports;
	supports.reserve(query_neighbors.size());
	for (ui u : query_neighbors)
	{
		if ((int)core[u] <= incumbent_k)
			continue;
		const int vertex_upper = std::min<int>(original_upper, core[u]);
		const ui required_cap = (ui)std::max(0, 2 * vertex_upper - UB_size);
		ui support = 0;
		if (required_cap > 0u)
		{
			for (ept pos = pstart[u]; pos < pstart[u + 1]; ++pos)
			{

				++edge_work;
				if (std::binary_search(query_neighbors.begin(),
					query_neighbors.end(), edges[pos]) && ++support >= required_cap)
					break;
			}
		}
		supports.push_back({u, support});
	}

	int tightened_upper = incumbent_k;
	for (int k = incumbent_k + 1; k <= original_upper; ++k)
	{
		const ui required_support = (ui)std::max(0, 2 * k - UB_size);
		ui eligible = 0;
		for (const QueryEdgeSupport &entry : supports)
			if ((int)core[entry.vertex] >= k &&
				entry.capped_support >= required_support)
				++eligible;
		if ((int)eligible >= k)
			tightened_upper = k;
	}
	exact = true;
	return tightened_upper;
}

// Index-Guided Budgeted Monotone Multi-Start Heuristic (IGBMMH).
//
// Algorithm 5 remains the incumbent producer.  This independent beam search
// seeks a feasible community with minimum degree strictly above that incumbent.
// Core numbers loaded from the query-independent index provide a necessary
// target-k filter.  The result is committed only when it is a verified strict
// improvement, hence the effective lower bound is monotone.
void Graph::budgeted_monotone_multistart_refine(int QID, int LB_size, int UB_size, vector<ui> &heu_solution, int &k_min, int &k_max, ui *core)
{

	const int original_k = k_min;
	int best_k = k_min;
	vector<ui> best_solution = heu_solution;

	const int original_upper = k_max;
	int support_upper = k_max;
	int search_upper = k_max;
	unsigned long long support_upper_edge_work = 0;

	bool support_upper_exact = false;

	ARCWorkLedger heuristic_work;
	auto consume_edge_work = [&]() -> bool {

		++heuristic_work.edge_scan_credit;
		return true;
	};
	auto consume_state_work = [&]() -> bool {

		++heuristic_work.dp_state_credit;
		return true;
	};

	if (!index_loaded)
	{

		return;
	}
	if (QID < 0 || (ui)QID >= n || UB_size < LB_size || UB_size > 15 ||
		k_min >= k_max)
	{

		return;
	}

	{

		support_upper = size_aware_support_upper_bound(QID, UB_size,
			original_k, original_upper, core, support_upper_edge_work,
			support_upper_exact);
		if (support_upper_exact &&
			(support_upper < original_k || support_upper > original_upper))
		{

			support_upper_exact = false;
			support_upper = original_upper;
		}
		if (support_upper_exact)
		{
			search_upper = support_upper;

			if (k_min >= search_upper)
			{
				k_max = search_upper;

				return;
		}
	}
	}

	const ui target_k = (ui)search_upper;
	if (core[QID] < target_k)
	{

		return;
	}

	struct LocalCandidate
	{
		ui vertex;
		ui core_value;
		ui graph_degree;
		ui local_support;
		bool query_neighbor;
	};

	vector<LocalCandidate> query_neighbors;
	query_neighbors.reserve(std::min<ui>(
		(ui)(pstart[QID + 1] - pstart[QID]),
		63u * 4u));
	for (ept pos = pstart[QID]; pos < pstart[QID + 1]; ++pos)
	{
		if (!consume_edge_work())
			break;
		const ui v = edges[pos];
		if (v < n && core[v] >= target_k)
			query_neighbors.push_back({v, core[v],
				(ui)(pstart[v + 1] - pstart[v]), 0u, true});
	}
	if (query_neighbors.size() < target_k)
	{

		return;
	}
	sort(query_neighbors.begin(), query_neighbors.end(),
		[](const LocalCandidate &a, const LocalCandidate &b) {
			if (a.core_value != b.core_value)
				return a.core_value > b.core_value;
			if (a.graph_degree != b.graph_degree)
				return a.graph_degree > b.graph_degree;
			return a.vertex < b.vertex;
		});

	const ui pool_cap = std::min<ui>(
		63u, 63u);
	const ui effective_beam_width = (std::max<ui>(1u, std::min<ui>(pool_cap, target_k)));
	const ui anchor_cap = std::min<ui>((ui)query_neighbors.size(),
		std::max<ui>(target_k,
			std::min<ui>(pool_cap / 2u,
				target_k + effective_beam_width)));

	vector<LocalCandidate> pool;
	pool.reserve(pool_cap);
	unordered_set<ui> seen;
	seen.reserve(pool_cap * 4u);
	seen.insert((ui)QID);
	for (ui i = 0; i < anchor_cap && pool.size() < pool_cap; ++i)
		if (seen.insert(query_neighbors[i].vertex).second)
			pool.push_back(query_neighbors[i]);

	// Add a bounded two-hop shell around the strongest query-neighbor anchors.
	// These vertices let the new path repair degree deficits in a way that the
	// one-seed greedy order of Algorithm 5 cannot express.
	for (ui anchor = 0; anchor < anchor_cap && pool.size() < pool_cap; ++anchor)
	{
		const ui u = query_neighbors[anchor].vertex;
		for (ept pos = pstart[u]; pos < pstart[u + 1] &&
			pool.size() < pool_cap; ++pos)
		{
			if (!consume_edge_work())
				break;
			const ui v = edges[pos];
			if (v >= n || core[v] < target_k || !seen.insert(v).second)
				continue;
			pool.push_back({v, core[v],
				(ui)(pstart[v + 1] - pstart[v]), 0u, false});
		}

	}

	if (pool.size() < target_k)
	{

		return;
	}

	unordered_map<ui, ui> local_id;
	local_id.reserve(pool.size() * 2u);
	for (ui i = 0; i < pool.size(); ++i)
		local_id[pool[i].vertex] = i;

	vector<unsigned long long> local_adjacency(pool.size(), 0ull);
	for (ui i = 0; i < pool.size(); ++i)
	{
		for (ept pos = pstart[pool[i].vertex];
			pos < pstart[pool[i].vertex + 1]; ++pos)
		{
			if (!consume_edge_work())
				break;
			auto found = local_id.find(edges[pos]);
			if (found != local_id.end() && found->second != i)
				local_adjacency[i] |= 1ull << found->second;
		}
		pool[i].local_support =
			(ui)__builtin_popcountll(local_adjacency[i]);

	}

	struct BeamState
	{
		unsigned long long mask;
		vector<unsigned char> degree;
		ui query_degree;
		ui min_degree;
		ui deficit;
		ui internal_edges;
		unsigned long long core_sum;
	};

	BeamState initial;
	initial.mask = 0ull;
	initial.degree.assign(pool.size(), 0);
	initial.query_degree = 0;
	initial.min_degree = 0;
	initial.deficit = target_k;
	initial.internal_edges = 0;
	initial.core_sum = core[QID];
	vector<BeamState> beam(1, initial);

	auto better_state = [](const BeamState &a, const BeamState &b) {
		if (a.min_degree != b.min_degree)
			return a.min_degree > b.min_degree;
		if (a.deficit != b.deficit)
			return a.deficit < b.deficit;
		if (a.query_degree != b.query_degree)
			return a.query_degree > b.query_degree;
		if (a.internal_edges != b.internal_edges)
			return a.internal_edges > b.internal_edges;
		if (a.core_sum != b.core_sum)
			return a.core_sum > b.core_sum;
		return a.mask < b.mask;
	};

	for (ui depth = 0; depth + 1u < (ui)UB_size && !beam.empty(); ++depth)
	{
		vector<BeamState> next_beam;
		next_beam.reserve(beam.size() * pool.size());
		unordered_set<unsigned long long> layer_masks;
		layer_masks.reserve(beam.size() * pool.size() * 2u);

		for (const BeamState &state : beam)
		{

			for (ui candidate = 0; candidate < pool.size(); ++candidate)
			{
				const unsigned long long candidate_bit = 1ull << candidate;
				if (state.mask & candidate_bit)
					continue;
				if (!consume_state_work())
					break;

				const unsigned long long neighbor_bits =
					state.mask & local_adjacency[candidate];
				const ui connections =
					(ui)__builtin_popcountll(neighbor_bits) +
					(pool[candidate].query_neighbor ? 1u : 0u);
				if (connections == 0u)
					continue;

				BeamState next = state;
				next.mask |= candidate_bit;
				next.degree[candidate] = (unsigned char)connections;
				next.query_degree += pool[candidate].query_neighbor ? 1u : 0u;
				next.internal_edges += connections;
				next.core_sum += pool[candidate].core_value;

				unsigned long long bits = neighbor_bits;
				while (bits)
				{
					const ui neighbor = (ui)__builtin_ctzll(bits);
					++next.degree[neighbor];
					bits &= bits - 1ull;
				}

				next.min_degree = next.query_degree;
				next.deficit = next.query_degree < target_k ?
					target_k - next.query_degree : 0u;
				bits = next.mask;
				while (bits)
				{
					const ui v = (ui)__builtin_ctzll(bits);
					next.min_degree =
						std::min<ui>(next.min_degree, next.degree[v]);
					if (next.degree[v] < target_k)
						next.deficit += target_k - next.degree[v];
					bits &= bits - 1ull;
				}

				if (!layer_masks.insert(next.mask).second)
					continue;

				const ui solution_size =
					1u + (ui)__builtin_popcountll(next.mask);
				if (solution_size >= (ui)LB_size &&
					solution_size <= (ui)UB_size &&
					(int)next.min_degree > best_k)
				{
					best_k = std::min<int>(next.min_degree, search_upper);
					best_solution.clear();
					best_solution.push_back((ui)QID);
					bits = next.mask;
					while (bits)
					{
						const ui v = (ui)__builtin_ctzll(bits);
						best_solution.push_back(pool[v].vertex);
						bits &= bits - 1ull;
					}
					if (best_k >= search_upper)
						break;
				}
				next_beam.push_back(std::move(next));
			}
			if (best_k >= search_upper)
				break;
		}
		if (best_k >= search_upper)
			break;
		sort(next_beam.begin(), next_beam.end(), better_state);
		if (next_beam.size() > effective_beam_width)
			next_beam.resize(effective_beam_width);
		beam.swap(next_beam);
	}

	if ((best_k > original_k) && (best_k >= search_upper))
	{
		k_max = search_upper;
		k_min = best_k;
		heu_solution = best_solution;
		feasible_solution = best_solution;
	}

}

void Graph::my_heu(vector<ui> &heu_solution, ui &k_min, ui k_max, int QID, int LB_size, int UB_size, ui *core)
{

	heu_solution.clear();
	// No lower bound is certified until an actual feasible witness is stored.
	k_min = 0;

	vector<ui> ego_netowrk;
	for (ept i = pstart[QID]; i < pstart[QID + 1]; ++i)
		ego_netowrk.push_back(edges[i]);
	assert(ego_netowrk.size() == pstart[QID + 1] - pstart[QID]);

	vector<ui> t_solution;
	// For upper size bounds at most 15, one persistent 32-bit word
	// per vertex stores a 23-bit seed epoch, one membership bit, a four-bit
	// solution degree, and a four-bit degree into the current solution.  A new
	// seed advances the epoch, so stale words represent the all-zero state.  The
	// same plane is reused across batch queries; larger U values fail open to the
	// original three-array representation.
	const bool epoch_state_active = (UB_size > 0) && UB_size <= 15;
	vector<ui> vis;
	vector<ui> deg;
	vector<ui> deg_in_S;
	bool heuristic_state_workspace_reused = false;
	if (epoch_state_active)
	{
		heuristic_state_workspace_reused = heuristic_epoch_state.size() == n;
		if (!heuristic_state_workspace_reused)
		{
			heuristic_epoch_state.assign(n, 0);
			heuristic_epoch_counter = 0;
		}
	}
	else
	{
		vis.assign(n, 0);
		deg.assign(n, 0);
		deg_in_S.assign(n, 0);
	}
	const ui DEGREE_IN_S_MASK = 15u;
	const ui SOLUTION_DEGREE_SHIFT = 4u;
	const ui SOLUTION_DEGREE_MASK = 15u << SOLUTION_DEGREE_SHIFT;
	const ui IN_SOLUTION_MASK = 1u << 8;
	const ui HEURISTIC_EPOCH_SHIFT = 9u;
	const ui MAX_HEURISTIC_EPOCH = (1u << 23) - 1u;
	ui degree_epoch = 0;
	auto begin_seed_epoch = [&]() {
		if (!epoch_state_active)
			return;
		if (heuristic_epoch_counter == MAX_HEURISTIC_EPOCH)
		{
			std::fill(heuristic_epoch_state.begin(), heuristic_epoch_state.end(), 0u);
			heuristic_epoch_counter = 1;
		}
		else
			++heuristic_epoch_counter;
		degree_epoch = heuristic_epoch_counter;
	};
	auto packed_state_is_current = [&](ui packed) -> bool {
		return (packed >> HEURISTIC_EPOCH_SHIFT) == degree_epoch;
	};
	auto get_deg_in_S = [&](ui v) -> ui {
		if (!epoch_state_active)
			return deg_in_S[v];
		const ui packed = heuristic_epoch_state[v];
		return packed_state_is_current(packed) ? (packed & DEGREE_IN_S_MASK) : 0u;
	};
	auto increment_deg_in_S = [&](ui v) -> ui {
		if (!epoch_state_active)
			return ++deg_in_S[v];
		ui &packed = heuristic_epoch_state[v];
		if (!packed_state_is_current(packed))
		{
			packed = (degree_epoch << HEURISTIC_EPOCH_SHIFT) | 1u;
			return 1u;
		}
		const ui old_degree = packed & DEGREE_IN_S_MASK;
		assert(old_degree < DEGREE_IN_S_MASK);
		packed = (packed & ~DEGREE_IN_S_MASK) | (old_degree + 1u);
		return old_degree + 1u;
	};
	auto in_solution = [&](ui v) -> bool {
		if (!epoch_state_active)
			return vis[v] != 0u;
		const ui packed = heuristic_epoch_state[v];
		return packed_state_is_current(packed) && (packed & IN_SOLUTION_MASK) != 0u;
	};
	auto get_solution_degree = [&](ui v) -> ui {
		if (!epoch_state_active)
			return deg[v];
		const ui packed = heuristic_epoch_state[v];
		if (!packed_state_is_current(packed))
			return 0u;
		return (packed & SOLUTION_DEGREE_MASK) >> SOLUTION_DEGREE_SHIFT;
	};
	auto mark_solution_vertex = [&](ui v, ui initial_degree) {
		if (!epoch_state_active)
		{
			vis[v] = 1;
			deg[v] = initial_degree;
			return;
		}
		assert(initial_degree <= DEGREE_IN_S_MASK);
		ui &packed = heuristic_epoch_state[v];
		const ui degree_in_s = packed_state_is_current(packed) ?
			(packed & DEGREE_IN_S_MASK) : 0u;
		packed = (degree_epoch << HEURISTIC_EPOCH_SHIFT) |
			IN_SOLUTION_MASK | (initial_degree << SOLUTION_DEGREE_SHIFT) |
			degree_in_s;
	};
	auto increment_solution_degree = [&](ui v) -> ui {
		if (!epoch_state_active)
			return ++deg[v];
		ui &packed = heuristic_epoch_state[v];
		assert(packed_state_is_current(packed));
		assert((packed & IN_SOLUTION_MASK) != 0);
		const ui old_degree =
			(packed & SOLUTION_DEGREE_MASK) >> SOLUTION_DEGREE_SHIFT;
		assert(old_degree < DEGREE_IN_S_MASK);
		packed += 1u << SOLUTION_DEGREE_SHIFT;
		return old_degree + 1u;
	};

	ui core_seed_order_warmup_remaining = UB_size > 0 ? 2u * (ui)UB_size : 0u;
	bool core_seed_order_active = false;
	while (!ego_netowrk.empty())
	{
		if ((!core_seed_order_active) && (core_seed_order_warmup_remaining == 0u) && (ego_netowrk.size() > 1u))
		{
			// Preserve a bounded prefix of the original seed order.  Only a
			// query that survives the warmup pays for ordering the remaining
			// seeds.  Stable sorting retains that order inside each core shell.
			std::stable_sort(ego_netowrk.begin(), ego_netowrk.end(),
				[&](ui a, ui b) {
					return core[a] < core[b];
				});
			core_seed_order_active = true;
		}

		if (core_seed_order_warmup_remaining > 0u)
			--core_seed_order_warmup_remaining;
		ui t_u = ego_netowrk.back();
		ego_netowrk.pop_back();
		if (!heu_solution.empty())
		{
			// Every vertex in a subgraph of minimum degree k belongs to the
			// global k-core.  Consequently no solution generated from seed t_u
			// can have minimum degree above min(core(QID), core(t_u), U-1).
			ui seed_upper_bound = core[t_u];
			if (core[QID] < seed_upper_bound)
				seed_upper_bound = core[QID];
			if (k_max < seed_upper_bound)
				seed_upper_bound = k_max;
			if (seed_upper_bound <= k_min)
			{

				continue;
			}
		}

		begin_seed_epoch();

		t_solution.clear();
		priority_queue<pair<ui, ui>> Q;
		assert(Q.empty());
		auto push_frontier = [&](ui v, ui current_degree) {
			if (in_solution(v))
				return;
			Q.push(make_pair(current_degree, v));
		};
		auto frontier_empty = [&]() -> bool {
			return Q.empty();
		};
		auto pop_frontier = [&]() -> ui {
			const ui v = Q.top().second;
			Q.pop();
			return v;
		};

		assert(!in_solution(t_u) && !in_solution(QID) &&
			get_solution_degree(t_u) == 0 && get_solution_degree(QID) == 0);
		t_solution.push_back(QID);
		t_solution.push_back(t_u);
		mark_solution_vertex(t_u, 1);
		mark_solution_vertex(QID, 1);
		for (ui i = pstart[t_u]; i < pstart[t_u + 1]; ++i)
		{
			const ui updated_degree = increment_deg_in_S(edges[i]);
			push_frontier(edges[i], updated_degree);
		}

		for (ui i = pstart[QID]; i < pstart[QID + 1]; ++i)
		{
			const ui updated_degree = increment_deg_in_S(edges[i]);
			push_frontier(edges[i], updated_degree);
		}

		bool can_break = false;
		while (t_solution.size() < static_cast<size_t>(UB_size))
		{

			ui max_deg_in_S = 0;
			ui max_core = 0;
			ui v = n;
			while (true)
			{
				if (frontier_empty())
					break;
				const ui t_v = pop_frontier();
				const ui current_degree = get_deg_in_S(t_v);
				assert(current_degree > 0);
				if (!in_solution(t_v))
				{
					if (current_degree > max_deg_in_S)
					{
						max_deg_in_S = current_degree;
						max_core = core[t_v];
						v = t_v;
					}
					else if (current_degree < max_deg_in_S)
						break;
					else
					{
						if (core[t_v] > max_core)
						{
							assert(max_deg_in_S == current_degree);
							max_core = core[t_v];
							v = t_v;
						}
					}
				}

				if (frontier_empty())
					break;
			}

			if (v == n)
				break;

			assert(v != n && !in_solution(v));

			t_solution.push_back(v);
			mark_solution_vertex(v, 0);

			for (ui i = pstart[v]; i < pstart[v + 1]; i++)
			{
				ui t_v = edges[i];
				const ui updated_degree = increment_deg_in_S(t_v);
				push_frontier(t_v, updated_degree);

				if (in_solution(t_v))
				{
					increment_solution_degree(v);
					increment_solution_degree(t_v);
				}
			}

			assert(t_solution.size() <= static_cast<size_t>(UB_size));
			if (t_solution.size() >= static_cast<size_t>(LB_size))
			{

				ui min_d = n;
				for (ui i = 0; i < t_solution.size(); ++i)
				{
					const ui solution_degree = get_solution_degree(t_solution[i]);
					if (solution_degree < min_d)
						min_d = solution_degree;
				}
				assert(min_d < n);

				if (min_d > k_min)
				{

					k_min = min_d;
					heu_solution = t_solution;
					if (k_min == k_max)
					{
						can_break = true;
						break;
					}
				}
				else if (min_d == k_min && heu_solution.empty())
				{
					// Retain a witness even when it only matches the current bound.
					heu_solution = t_solution;
				}
			}
		}

		if (can_break)
			break;

		assert(t_solution.size() == static_cast<size_t>(UB_size) || can_break ||
			frontier_empty());

		if (!epoch_state_active)
		{
			for (ui i = 0; i < t_solution.size(); ++i)
			{
				ui u = t_solution[i];
				assert(in_solution(u));
				vis[u] = 0;
				deg[u] = 0;
			}
			deg_in_S.assign(n, 0);
		}
	}

	printf("[Heuristic] lower_bound=%d\n", k_min);
}
