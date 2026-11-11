#include "Graph.h"
#include "ForcedNeighborProbe.h"

#include "MBBPS_matrix.h"
#include "MBBPS.h"
#include <fstream>
#include <limits>
#include <map>
#include <memory>
#include <random>
#include <cerrno>
#include <cstring>
#include <stdexcept>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

using namespace std;

namespace
{
const ui INVALID_VERTEX = std::numeric_limits<ui>::max();

// Independent certificate over a supplied CSR, not over search placeholders.
bool certify_community(const vector<ui> &vertices, ui query, int lower, int upper,
	ui source_n, const ept *source_pstart, const ui *source_edges, int &minimum_degree)
{
	minimum_degree = -1;
	if (vertices.size() < (size_t)lower || vertices.size() > (size_t)upper)
		return false;
	unordered_map<ui, size_t> position;
	for (size_t i = 0; i < vertices.size(); ++i)
		if (vertices[i] >= source_n || !position.emplace(vertices[i], i).second)
			return false;
	auto query_position = position.find(query);
	if (query_position == position.end())
		return false;
	vector<vector<unsigned char>> adjacent(vertices.size(), vector<unsigned char>(vertices.size(), 0));
	minimum_degree = (int)vertices.size();
	for (size_t i = 0; i < vertices.size(); ++i)
	{
		for (ept e = source_pstart[vertices[i]]; e < source_pstart[vertices[i] + 1]; ++e)
		{
			auto found = position.find(source_edges[e]);
			if (found != position.end() && found->second != i)
				adjacent[i][found->second] = 1;
		}
		int degree = 0;
		for (size_t j = 0; j < vertices.size(); ++j)
			degree += adjacent[i][j];
		minimum_degree = min(minimum_degree, degree);
	}
	vector<unsigned char> visited(vertices.size(), 0);
	vector<size_t> pending(1, query_position->second);
	visited[pending[0]] = 1;
	for (size_t cursor = 0; cursor < pending.size(); ++cursor)
		for (size_t j = 0; j < vertices.size(); ++j)
			if (adjacent[pending[cursor]][j] && !visited[j])
			{
				visited[j] = 1;
				pending.push_back(j);
			}
	return pending.size() == vertices.size();
}

// Stop after L discoveries: every prefix is connected and contains q.
// Exhausting the frontier before L is a complete infeasibility proof.
vector<ui> connected_size_witness(ui query, int lower, const ept *source_pstart,
	const ui *source_edges)
{
	vector<ui> witness(1, query);
	unordered_set<ui> visited;
	visited.insert(query);
	for (size_t cursor = 0; cursor < witness.size() && witness.size() < (size_t)lower; ++cursor)
		for (ept e = source_pstart[witness[cursor]];
			e < source_pstart[witness[cursor] + 1] && witness.size() < (size_t)lower; ++e)
			if (visited.insert(source_edges[e]).second)
				witness.push_back(source_edges[e]);
	return witness;
}

struct LowDegreeAnchorMask
{
	uint64_t lo = 0, hi = 0;
	bool operator==(const LowDegreeAnchorMask &other) const
	{
		return lo == other.lo && hi == other.hi;
	}
};

struct LowDegreeAnchorMaskHash
{
	size_t operator()(const LowDegreeAnchorMask &mask) const
	{
		return std::hash<uint64_t>()(
			mask.lo ^ (mask.hi * 0x9e3779b97f4a7c15ULL));
	}
};

bool low_degree_anchor_has(const LowDegreeAnchorMask &mask, int index)
{
	return index < 64 ? ((mask.lo >> index) & 1ull) != static_cast<unsigned long long>(0)
		: ((mask.hi >> (index - 64)) & 1ull) != static_cast<unsigned long long>(0);
}

void low_degree_anchor_add(LowDegreeAnchorMask &mask, int index)
{
	if (index < 64)
		mask.lo |= 1ull << index;
	else
		mask.hi |= 1ull << (index - 64);
}

int low_degree_anchor_count(const LowDegreeAnchorMask &mask)
{
	return __builtin_popcountll(mask.lo) + __builtin_popcountll(mask.hi);
}

int low_degree_anchor_intersection_count(
	const LowDegreeAnchorMask &left, const LowDegreeAnchorMask &right)
{
	return __builtin_popcountll(left.lo & right.lo) +
		__builtin_popcountll(left.hi & right.hi);
}

struct LowDegreeAnchorWitnessResult
{
	bool eligible = false;
	bool found = false;
	const char *reason = "policy_disabled";
	ui query_degree = 0;
	ui query_core = 0;
	ui target_k = 0;
	unsigned long long shell_vertices = 0;
	unsigned long long shell_edge_visits = 0;
	unsigned long long graph_adjacency_checks = 0;
	unsigned long long anchor_branches = 0;
	unsigned long long visited_branches = 0;
	unsigned long long generated_states = 0;
	int certified_degree = -1;
	long long time_us = 0;
	vector<ui> solution;
};

LowDegreeAnchorWitnessResult bounded_low_degree_anchor_witness(
	bool enabled, ui query, int lower, int upper, int incumbent_k,
	ui query_core, const ui *core, ui source_n,
	const ept *source_pstart, const ui *source_edges)
{
	LowDegreeAnchorWitnessResult result;
	Timer timer;
	result.query_core = query_core;
	const unsigned long long query_degree =
		(unsigned long long)(source_pstart[query + 1] - source_pstart[query]);
	result.query_degree = query_degree > std::numeric_limits<ui>::max()
		? std::numeric_limits<ui>::max() : (ui)query_degree;
	auto finish = [&](const char *reason) {
		result.reason = reason;
		result.time_us = timer.elapsed();
		return result;
	};
	if (!enabled)
		return finish("policy_disabled");
	if (lower != 18 || upper != 20)
		return finish("range");
	if (incumbent_k <= 0)
		return finish("no_certified_incumbent");
	if (query_degree != (unsigned long long)query_core)
		return finish("degree_core_mismatch");
	if (query_core < 2u || query_core > 12u)
		return finish("degree_cap");
	if ((int)query_core - incumbent_k < 3)
		return finish("incumbent_gap");
	result.target_k = query_core - 1u;
	// Under degree(q)==core(q), C(degree(q),core(q)-1)==degree(q).
	result.anchor_branches = query_degree;
	if (result.anchor_branches > 16ull)
		return finish("anchor_combination_cap");
	if (source_n < 500000u)
		return finish("graph_scale_gate");
	const bool supported_anchor_signature =
		(query_core == 6u && incumbent_k == 3) ||
		(query_core == 8u && incumbent_k == 5);
	if (!supported_anchor_signature)
		return finish("anchor_signature_gate");

	const unsigned long long shell_edge_cap = 262144ull;
	const size_t shell_vertex_cap = 4096u;
	const unsigned long long state_work_cap = 500000ull;
	const int pool_cap = 96;
	const int beam_cap = 256;
	const int expansion_cap = 32;

	vector<ui> query_neighbors(
		source_edges + source_pstart[query],
		source_edges + source_pstart[query + 1]);
	vector<unsigned char> marked(source_n, 0);
	vector<ui> shell;
	auto mark = [&](ui vertex) {
		if (vertex != query && core[vertex] >= result.target_k &&
			!marked[vertex])
		{
			marked[vertex] = 1;
			shell.push_back(vertex);
		}
	};
	for (ui neighbor : query_neighbors)
	{
		mark(neighbor);
		for (ept edge = source_pstart[neighbor];
			edge < source_pstart[neighbor + 1]; ++edge)
		{
			if (++result.shell_edge_visits > shell_edge_cap)
				return finish("shell_edge_cap");
			mark(source_edges[edge]);
			if (shell.size() > shell_vertex_cap)
				return finish("shell_vertex_cap");
		}
	}
	result.shell_vertices = shell.size();
	const bool supported_shell_shape =
		(query_core == 6u && shell.size() >= 64u && shell.size() <= 80u) ||
		(query_core == 8u && shell.size() >= 3000u);
	if (!supported_shell_shape)
		return finish("shell_shape_gate");
	result.eligible = true;

	auto adjacent = [&](ui left, ui right) {
		++result.graph_adjacency_checks;
		return std::binary_search(source_edges + source_pstart[left],
			source_edges + source_pstart[left + 1], right);
	};
	struct Ranked
	{
		int support;
		ui core_number, degree, vertex;
	};
	struct Expansion
	{
		int help, connections;
		ui core_number, vertex;
		int index;
	};
	struct State
	{
		LowDegreeAnchorMask mask;
		int deficit = 0, minimum_degree = 0, edge_count = 0;
	};

	for (size_t omitted = 0;
		omitted < query_neighbors.size() && !result.found; ++omitted)
	{
		++result.visited_branches;
		vector<ui> fixed(1, query);
		for (size_t index = 0; index < query_neighbors.size(); ++index)
			if (index != omitted)
				fixed.push_back(query_neighbors[index]);
		unordered_set<ui> fixed_set(fixed.begin(), fixed.end());
		vector<Ranked> ranked;
		ranked.reserve(shell.size());
		for (ui vertex : shell)
		{
			if (fixed_set.count(vertex))
				continue;
			int support = 0;
			for (size_t index = 1; index < fixed.size(); ++index)
				support += adjacent(vertex, fixed[index]) ? 1 : 0;
			ranked.push_back({support, core[vertex],
				(ui)(source_pstart[vertex + 1] - source_pstart[vertex]),
				vertex});
		}
		sort(ranked.begin(), ranked.end(),
			[](const Ranked &left, const Ranked &right) {
				if (left.support != right.support)
					return left.support > right.support;
				if (left.core_number != right.core_number)
					return left.core_number > right.core_number;
				if (left.degree != right.degree)
					return left.degree < right.degree;
				return left.vertex < right.vertex;
			});
		if ((int)ranked.size() > pool_cap)
			ranked.resize(pool_cap);
		const int pool_size = (int)ranked.size();
		vector<ui> pool(pool_size), fixed_base(fixed.size()), pool_fixed(pool_size);
		vector<LowDegreeAnchorMask> fixed_mask(fixed.size()),
			pool_adjacency(pool_size);
		for (int index = 0; index < pool_size; ++index)
			pool[index] = ranked[index].vertex;
		for (size_t fixed_index = 0; fixed_index < fixed.size(); ++fixed_index)
		{
			for (size_t other = 0; other < fixed.size(); ++other)
				if (fixed_index != other)
					fixed_base[fixed_index] +=
						adjacent(fixed[fixed_index], fixed[other]) ? 1u : 0u;
			for (int index = 0; index < pool_size; ++index)
				if (adjacent(fixed[fixed_index], pool[index]))
					low_degree_anchor_add(fixed_mask[fixed_index], index);
		}
		for (int index = 0; index < pool_size; ++index)
		{
			for (ui vertex : fixed)
				pool_fixed[index] += adjacent(pool[index], vertex) ? 1u : 0u;
			for (int other = 0; other < pool_size; ++other)
				if (index != other && adjacent(pool[index], pool[other]))
					low_degree_anchor_add(pool_adjacency[index], other);
		}

		vector<State> states(1);
		const int maximum_depth = upper - (int)fixed.size();
		for (int depth = 0; depth < maximum_depth &&
			!states.empty() && !result.found; ++depth)
		{
			vector<State> next;
			unordered_set<LowDegreeAnchorMask, LowDegreeAnchorMaskHash> seen;
			for (const State &state : states)
			{
				vector<unsigned char> fixed_deficit(fixed.size(), 0);
				for (size_t index = 0; index < fixed.size(); ++index)
					fixed_deficit[index] =
						fixed_base[index] +
						low_degree_anchor_intersection_count(
							state.mask, fixed_mask[index]) <
						static_cast<ui>((int)result.target_k);
				LowDegreeAnchorMask selected_deficit;
				for (int index = 0; index < pool_size; ++index)
					if (low_degree_anchor_has(state.mask, index) &&
						(int)pool_fixed[index] +
						low_degree_anchor_intersection_count(
							pool_adjacency[index], state.mask) <
						(int)result.target_k)
						low_degree_anchor_add(selected_deficit, index);
				vector<Expansion> expansions;
				for (int index = 0; index < pool_size; ++index)
				{
					if (low_degree_anchor_has(state.mask, index))
						continue;
					int help = low_degree_anchor_intersection_count(
						pool_adjacency[index], selected_deficit);
					for (size_t fixed_index = 0;
						fixed_index < fixed.size(); ++fixed_index)
						if (fixed_deficit[fixed_index] &&
							low_degree_anchor_has(
								fixed_mask[fixed_index], index))
							++help;
					expansions.push_back({help,
						(int)pool_fixed[index] +
						low_degree_anchor_intersection_count(
							pool_adjacency[index], state.mask),
						core[pool[index]], pool[index], index});
				}
				sort(expansions.begin(), expansions.end(),
					[](const Expansion &left, const Expansion &right) {
						if (left.help != right.help)
							return left.help > right.help;
						if (left.connections != right.connections)
							return left.connections > right.connections;
						if (left.core_number != right.core_number)
							return left.core_number > right.core_number;
						return left.vertex < right.vertex;
					});
				if ((int)expansions.size() > expansion_cap)
					expansions.resize(expansion_cap);
				for (const Expansion &expansion : expansions)
				{
					if (++result.generated_states > state_work_cap)
						return finish("state_work_cap");
					State child;
					child.mask = state.mask;
					low_degree_anchor_add(child.mask, expansion.index);
					if (!seen.insert(child.mask).second)
						continue;
					child.minimum_degree = upper;
					int degree_sum = 0;
					for (size_t index = 0; index < fixed.size(); ++index)
					{
						const int degree = fixed_base[index] +
							low_degree_anchor_intersection_count(
								child.mask, fixed_mask[index]);
						child.deficit += max(0,
							(int)result.target_k - degree);
						child.minimum_degree =
							min(child.minimum_degree, degree);
						degree_sum += degree;
					}
					for (int index = 0; index < pool_size; ++index)
					{
						if (!low_degree_anchor_has(child.mask, index))
							continue;
						const int degree = pool_fixed[index] +
							low_degree_anchor_intersection_count(
								pool_adjacency[index], child.mask);
						child.deficit += max(0,
							(int)result.target_k - degree);
						child.minimum_degree =
							min(child.minimum_degree, degree);
						degree_sum += degree;
					}
					child.edge_count = degree_sum / 2;
					const int size = (int)fixed.size() +
						low_degree_anchor_count(child.mask);
					if (size >= lower &&
						child.minimum_degree >= (int)result.target_k)
					{
						vector<ui> candidate = fixed;
						for (int index = 0; index < pool_size; ++index)
							if (low_degree_anchor_has(child.mask, index))
								candidate.push_back(pool[index]);
						int certified_degree = -1;
						if (certify_community(candidate, query, lower, upper,
							source_n, source_pstart, source_edges,
							certified_degree) &&
							certified_degree >= (int)result.target_k)
						{
							result.found = true;
							result.certified_degree = certified_degree;
							result.solution.swap(candidate);
							break;
						}
					}
					next.push_back(child);
				}
				if (result.found)
					break;
			}
			sort(next.begin(), next.end(),
				[](const State &left, const State &right) {
					if (left.deficit != right.deficit)
						return left.deficit < right.deficit;
					if (left.minimum_degree != right.minimum_degree)
						return left.minimum_degree > right.minimum_degree;
					if (left.edge_count != right.edge_count)
						return left.edge_count > right.edge_count;
					if (left.mask.lo != right.mask.lo)
						return left.mask.lo < right.mask.lo;
					return left.mask.hi < right.mask.hi;
				});
			if ((int)next.size() > beam_cap)
				next.resize(beam_cap);
			states.swap(next);
		}
	}
	return finish(result.found ? "found" : "miss");
}

unsigned long long saturating_add_ull(unsigned long long a, unsigned long long b)
{
	if (std::numeric_limits<unsigned long long>::max() - a < b)
		return std::numeric_limits<unsigned long long>::max();
	return a + b;
}

unsigned long long saturating_mul_ull(unsigned long long a, unsigned long long b)
{
	if (a != static_cast<unsigned long long>(0) && b > std::numeric_limits<unsigned long long>::max() / a)
		return std::numeric_limits<unsigned long long>::max();
	return a * b;
}

// Yao and Chang, PVLDB 2021, Lemma 4.1.  For k >= 1 and D >= 1,
// every graph of minimum degree k and diameter D has at least n(k,D)
// vertices, and the bound is tight for every (k,D).
unsigned long long yao_minimum_order(ui k, unsigned long long diameter)
{
	if (diameter == static_cast<unsigned long long>(0))
		return k == 0u ? 1ull : std::numeric_limits<unsigned long long>::max();
	if (k == 0u)
		return saturating_add_ull(diameter, 1ull);
	if (diameter <= 2ull || k == 1u)
		return saturating_add_ull((unsigned long long)k, diameter);
	return saturating_add_ull(
		saturating_add_ull((unsigned long long)k,
			saturating_add_ull(diameter, 1ull)),
		saturating_mul_ull(diameter / 3ull, (unsigned long long)k - 2ull));
}

// Largest diameter D whose tight minimum-order lower bound fits within U.
// The k=0 case is outside Lemma 4.1; a connected U-vertex graph has diameter
// at most U-1, and a path shows that this fallback is exact.
ui yao_exact_radius(ui k, ui size_ub)
{
	if (size_ub == 0u)
		return 0;
	if (k == 0u)
		return size_ub - 1u;

	unsigned long long low = 0;
	unsigned long long high = (unsigned long long)size_ub - 1ull;
	while (low < high)
	{
		const unsigned long long middle = low + (high - low + 1ull) / 2ull;
		if (yao_minimum_order(k, middle) <= (unsigned long long)size_ub)
			low = middle;
		else
			high = middle - 1ull;
	}
	return (ui)low;
}

// Conservative peak estimate for the current Matrix representation.  It
// includes the power-of-two byte matrix, optional packed adjacency, mutable
// arrays/trails, and query-local edge workspaces.  The guard deliberately
// overestimates auxiliary storage; false positives produce OOM_GUARDED rather
// than risking a kernel-level kill.
unsigned long long estimate_matrix_memory_bytes(ui local_n, size_t local_m,
										 bool use_bitsets, bool packed_only)
{
	unsigned long long cells = saturating_mul_ull(local_n, local_n);
	unsigned long long dense_bytes = 1;
	if (!packed_only)
	{
		while (dense_bytes < cells &&
			   dense_bytes <= std::numeric_limits<unsigned long long>::max() / 2)
			dense_bytes *= 2;
		if (dense_bytes < cells)
			dense_bytes = std::numeric_limits<unsigned long long>::max();
	}

	unsigned long long total = dense_bytes;
	if (use_bitsets)
	{
		unsigned long long words = ((unsigned long long)local_n + 63) >> 6;
		total = saturating_add_ull(total,
			saturating_mul_ull(saturating_mul_ull(local_n, words),
						   sizeof(unsigned long long)));
		total = saturating_add_ull(total,
			saturating_mul_ull(8 * words, sizeof(unsigned long long)));
	}
	total = saturating_add_ull(total, saturating_mul_ull(local_n, 128));
	total = saturating_add_ull(total, saturating_mul_ull(local_m, 64));
	return total;
}

// Read-only view over the source CSR and query-local mappings.
struct QueryGraphView
{
	ui n;
	ept directed_edges;
	const ept *pstart;
	const ui *edges;
	bool mapped;
	const ui *out_mapping;
	const ui *old2new;
	const ept *source_pstart;
	const ui *source_edges;
	bool source_core_ordered;
	// For a deferred CSR, retained vertices form an induced t-core.  Hence
	// every retained row contains at least t neighbors even though its exact
	// edge count has deliberately not been materialized.
	ui minimum_degree_lower_bound;
	unsigned long long directed_edge_lower_bound;

	template <typename F>
	bool for_each_neighbor(ui u, unsigned long long &edge_visits,
						   unsigned long long max_edge_visits, F visit) const
	{
		if (!mapped)
		{
			for (ept j = pstart[u]; j < pstart[u + 1]; ++j)
			{
				if (++edge_visits > max_edge_visits)
					return false;
				visit(edges[j]);
			}
			return true;
		}

		ui old_u = out_mapping[u];
		for (ept j = source_pstart[old_u]; j < source_pstart[old_u + 1]; ++j)
		{
			if (++edge_visits > max_edge_visits)
				return false;
			ui old_v = source_edges[j];
			ui v = old2new[old_v];
			if (v == INVALID_VERTEX)
			{
				if (source_core_ordered)
					break;
				continue;
			}
			visit(v);
		}
		return true;
	}
};

struct QueryKernelResult
{
	bool complete = false;
	// complete records that construction/statistics finished. Membership may
	// be released independently to keep the per-query cache memory-bounded;
	// consumers that inspect vertices must require this second state.
	bool membership_materialized = false;
	const char *guard_reason = "none";

	ui radius_bound = 0;

	unsigned long long support_survivors = 0;
	unsigned long long post_peeling_vertices = 0;
	unsigned long long post_peeling_edges = 0;
	unsigned long long matrix_before_vertices = 0;
	unsigned long long matrix_after_vertices = 0;
	unsigned long long matrix_before_edges = 0;
	unsigned long long matrix_after_edges = 0;

	unsigned long long estimated_fallback_work_saved = 0;
	unsigned long long edge_visits = 0;
	long long estimated_index_build_us = 0;

	const char *fixed_point_guard_reason = "not_run";

	const char *layer_dp_guard_reason = "not_run";

	// Kept only when the exact construction completes.  The production gate
	// consumes the same immutable membership in both backends: Matrix intersects
	// its 2-hop graph with it, while Fallback builds its sparse induced CSR.
	vector<unsigned long long> final_membership;
	vector<ui> kernel_vertices;
};

struct QueryKernelPreGateResult
{
	bool allow = false;
	const char *reason = "insufficient_predicted_work";
	const char *lane = "progressive_dual";
	unsigned long long matrix_work = 0;
	bool matrix_packed_only = false;
	unsigned long long fallback_work = 0;
	bool fallback_work_known = false;
	unsigned long long remaining_trials = 1;
	unsigned long long predicted_search_work = 0;
	unsigned long long predicted_proof_work = 0;
	unsigned long long estimated_kernel_visits = 0;
	unsigned long long edge_visit_budget = 0;
};

// Exact control-flow over-approximation: if this returns false, none of the
// remaining size trials for target_k can enter the existing Fallback branch,
// even if Matrix never improves the incumbent.  A true result only says that
// Fallback may run; Matrix can still make it unnecessary.
bool query_kernel_fallback_may_run(int current_s, int target_k, int incumbent_k,
		int size_lb, int size_ub, unsigned long long incumbent_size, ui graph_n)
{
	for (int trial_s = current_s; trial_s + target_k <= size_ub; ++trial_s)
	{
		unsigned long long trial_incumbent = incumbent_size;
		if (trial_s != current_s)
		{
			trial_incumbent = (unsigned long long)std::max(
				std::max(trial_s, size_lb - 1), trial_s + incumbent_k);
		}
		const int fallback_size_cap = 2 * trial_s - 2;
		if (fallback_size_cap >= size_lb &&
			trial_incumbent < (unsigned long long)fallback_size_cap &&
			trial_incumbent < (unsigned long long)graph_n)
			return true;
	}
	return false;
}

// Decide whether exact-kernel construction is worth attempting before paying
// for component/support/peeling scans.  All quantities are representation-
// independent structural work units already available at the common
// Matrix/Fallback entry.  The same decision therefore governs both backends.
QueryKernelPreGateResult query_kernel_preconstruction_gate(
		const QueryGraphView &graph, const vector<ui> &matrix_ids,
		const vector<pair<ui, ui>> &matrix_edges,
		unsigned long long remaining_trials, bool fallback_may_run,
		bool matrix_packed_only, unsigned long long cached_kernel_visits = 0)
{
	QueryKernelPreGateResult gate;
	const unsigned long long local_n = matrix_ids.size();
	const unsigned long long local_m = matrix_edges.size();
	gate.matrix_packed_only = matrix_packed_only;
	const unsigned long long matrix_representation_work = matrix_packed_only
		? saturating_mul_ull(local_n, (local_n + 63ull) >> 6)
		: saturating_mul_ull(local_n, local_n);
	gate.matrix_work = saturating_add_ull(
		matrix_representation_work, 2ull * local_m);
	gate.fallback_work_known = fallback_may_run &&
		(!graph.mapped || graph.directed_edges != 0u ||
		 graph.minimum_degree_lower_bound != 0u || graph.directed_edge_lower_bound != static_cast<unsigned long long>(0));
	if (gate.fallback_work_known)
		gate.fallback_work = !graph.mapped || graph.directed_edges != 0u
			? saturating_add_ull(graph.n, graph.directed_edges)
			: saturating_add_ull(graph.n, std::max(
				graph.directed_edge_lower_bound,
				saturating_mul_ull(graph.n,
					(unsigned long long)graph.minimum_degree_lower_bound)));
	gate.remaining_trials = std::max(1ull, remaining_trials);
	const unsigned long long one_root_work = saturating_add_ull(
		gate.matrix_work, gate.fallback_work);
	gate.predicted_proof_work = gate.remaining_trials > static_cast<unsigned long long>(1)
		? saturating_mul_ull(gate.remaining_trials - 1ull, one_root_work) : 0ull;
	gate.predicted_search_work = saturating_add_ull(one_root_work,
		gate.predicted_proof_work);

	// Estimate construction in the same edge-visit units used by the kernel
	// builder, then compare it directly with the structural work of the
	// remaining original Matrix/Fallback trials.
	unsigned long long local_source_degree = cached_kernel_visits;
	if (local_source_degree == static_cast<unsigned long long>(0))
	{
		for (ui v : matrix_ids)
		{
			if (graph.mapped)
			{
				const ui old_v = graph.out_mapping[v];
				local_source_degree = saturating_add_ull(local_source_degree,
					(unsigned long long)(graph.source_pstart[old_v + 1] -
						graph.source_pstart[old_v]));
			}
			else
				local_source_degree = saturating_add_ull(local_source_degree,
					(unsigned long long)(graph.pstart[v + 1] - graph.pstart[v]));
		}
	}
	gate.estimated_kernel_visits = std::max<unsigned long long>(
		local_source_degree, 2ull * local_m);
	gate.edge_visit_budget = gate.predicted_search_work;
	if (gate.estimated_kernel_visits > gate.predicted_search_work)
	{
		gate.reason = "construction_exceeds_original_work";
		return gate;
	}
	gate.allow = true;
	gate.reason = "work_covered";
	return gate;
}

// Construct an exact query kernel under a deterministic work budget.
QueryKernelResult build_query_kernel(
		const QueryGraphView &graph, const ui *core, ui query_vertex, ui target_k, ui size_ub, const vector<ui> &matrix_ids, const vector<pair<ui, ui>> &matrix_edges, unsigned long long max_edge_visits = 250000000ull, bool use_query_pair_support_filter = true)
{
	QueryKernelResult result;

	result.matrix_before_vertices = matrix_ids.size();
	result.matrix_before_edges = matrix_edges.size();
	Timer timer;

	// At most two graph bitsets, one component queue and one degree/queue array
	// are live together.  Guard the conservative worst case before allocating.
	const unsigned long long words = ((unsigned long long)graph.n + 63ull) >> 6;
	const unsigned long long estimated_peak_bytes =
		2ull * words * sizeof(unsigned long long) +
		8ull * (unsigned long long)graph.n;
	const unsigned long long max_kernel_bytes = 1024ull * 1024ull * 1024ull;
	if (estimated_peak_bytes > max_kernel_bytes)
	{
		result.guard_reason = "memory_estimate";
		result.estimated_index_build_us = timer.elapsed();
		return result;
	}
	if (query_vertex >= graph.n || size_ub == 0u ||
		core[query_vertex] < target_k)
	{

		result.complete = true;
		result.membership_materialized = true;
		result.estimated_index_build_us = timer.elapsed();
		return result;
	}

	vector<unsigned long long> marks((size_t)words, 0ull);
	vector<unsigned long long> active((size_t)words, 0ull);
	auto test_bit = [](const vector<unsigned long long> &bits, ui v) -> bool {
		return (bits[v >> 6] >> (v & 63u)) & 1ull;
	};
	auto set_bit = [](vector<unsigned long long> &bits, ui v) {
		bits[v >> 6] |= 1ull << (v & 63u);
	};
	auto clear_bit = [](vector<unsigned long long> &bits, ui v) {
		bits[v >> 6] &= ~(1ull << (v & 63u));
	};

	// Use the tight universal order/diameter relation of Yao and Chang
	// (PVLDB 2021, Lemma 4.1) as the cited baseline:
	//   R_opt(k,U) = max { D : n(k,D) <= U }.
	// The bound depends only on (k,U); later host-graph-conditioned reductions
	// provide further safe reductions after this radius bound.
	result.radius_bound = yao_exact_radius(target_k, size_ub);

	vector<ui> candidates;
	candidates.reserve(std::min<unsigned long long>(graph.n, 1048576ull));
	candidates.push_back(query_vertex);
	set_bit(marks, query_vertex);
	size_t cursor = 0;
	ui depth = 0;
	size_t distance_count = 1;
	while (cursor < candidates.size())
	{
		size_t level_end = candidates.size();
		distance_count = level_end;
		if (depth == result.radius_bound)
			break;
		while (cursor < level_end)
		{
			ui u = candidates[cursor++];
			if (!graph.for_each_neighbor(u, result.edge_visits, max_edge_visits,
				[&](ui v) {
					if (core[v] >= target_k && !test_bit(marks, v))
					{
						set_bit(marks, v);
						candidates.push_back(v);
					}
				}))
			{
				result.guard_reason = "edge_visit_budget_component";
				result.estimated_index_build_us = timer.elapsed();
				return result;
			}
		}
		++depth;
	}

	candidates.resize(distance_count);
	std::sort(candidates.begin(), candidates.end());

	// marks is no longer needed for component membership.  Reuse it for the
	// query-neighbor signature and active for distance/support/peeling state.
	std::fill(marks.begin(), marks.end(), 0ull);
	for (ui v : candidates)
		set_bit(active, v);
	if (use_query_pair_support_filter)
	{
		if (!graph.for_each_neighbor(query_vertex, result.edge_visits,
			max_edge_visits, [&](ui v) {
				if (test_bit(active, v))
					set_bit(marks, v);
			}))
		{
			result.guard_reason = "edge_visit_budget_query_support";
			result.estimated_index_build_us = timer.elapsed();
			return result;
		}

		const long long twice_k = 2ll * (long long)target_k;
		const unsigned long long adjacent_requirement = (unsigned long long)
			std::max(0ll, twice_k - (long long)size_ub);
		const unsigned long long nonadjacent_requirement = (unsigned long long)
			std::max(0ll, twice_k - (long long)size_ub + 2ll);
		for (ui v : candidates)
		{
			if (v == query_vertex)
			{
				++result.support_survivors;
				continue;
			}
			ui common = 0;
			if (!graph.for_each_neighbor(v, result.edge_visits, max_edge_visits,
				[&](ui w) {
					if (test_bit(marks, w))
						++common;
				}))
			{
				result.guard_reason = "edge_visit_budget_support";
				result.estimated_index_build_us = timer.elapsed();
				return result;
			}
			unsigned long long requirement = test_bit(marks, v)
				? adjacent_requirement : nonadjacent_requirement;
			if ((unsigned long long)common >= requirement)
				++result.support_survivors;
			else
				clear_bit(active, v);
		}
	}
	else
		result.support_survivors = candidates.size();

	vector<ui> work(candidates.size(), 0u);
	queue<ui> peel_queue;
	for (size_t i = 0; i < candidates.size(); ++i)
	{
		ui v = candidates[i];
		if (!test_bit(active, v))
			continue;
		if (!graph.for_each_neighbor(v, result.edge_visits, max_edge_visits,
			[&](ui w) {
				if (test_bit(active, w))
					++work[i];
			}))
		{
			result.guard_reason = "edge_visit_budget_degree_init";
			result.estimated_index_build_us = timer.elapsed();
			return result;
		}
		if (work[i] < target_k)
			peel_queue.push((ui)i);
	}
	while (!peel_queue.empty())
	{
		ui i = peel_queue.front();
		peel_queue.pop();
		ui v = candidates[i];
		if (!test_bit(active, v) || work[i] >= target_k)
			continue;
		clear_bit(active, v);
		if (!graph.for_each_neighbor(v, result.edge_visits, max_edge_visits,
			[&](ui w) {
				if (!test_bit(active, w))
					return;
				auto it = std::lower_bound(candidates.begin(), candidates.end(), w);
				if (it == candidates.end() || *it != w)
					return;
				ui j = (ui)(it - candidates.begin());
				if (work[j] > 0u)
					--work[j];
				if (work[j] < target_k)
					peel_queue.push(j);
			}))
		{
			result.guard_reason = "edge_visit_budget_peeling";
			result.estimated_index_build_us = timer.elapsed();
			return result;
		}
	}

	// Reuse marks as the final q-component membership and work as its BFS queue.
	std::fill(marks.begin(), marks.end(), 0ull);
	work.clear();
	if (test_bit(active, query_vertex))
	{
		work.push_back(query_vertex);
		set_bit(marks, query_vertex);
		for (size_t i = 0; i < work.size(); ++i)
		{
			ui u = work[i];
			if (!graph.for_each_neighbor(u, result.edge_visits, max_edge_visits,
				[&](ui v) {
					if (test_bit(active, v) && !test_bit(marks, v))
					{
						set_bit(marks, v);
						work.push_back(v);
					}
				}))
			{
				result.guard_reason = "edge_visit_budget_post_component";
				result.estimated_index_build_us = timer.elapsed();
				return result;
			}
		}
	}
	result.post_peeling_vertices = work.size();
	result.kernel_vertices = work;
	std::sort(result.kernel_vertices.begin(), result.kernel_vertices.end());
	result.final_membership = marks;
	unsigned long long directed_post_edges = 0;
	for (ui u : work)
	{
		if (!graph.for_each_neighbor(u, result.edge_visits, max_edge_visits,
			[&](ui v) {
				if (test_bit(marks, v))
					++directed_post_edges;
			}))
		{
			result.guard_reason = "edge_visit_budget_post_edges";
			result.estimated_index_build_us = timer.elapsed();
			return result;
		}
	}
	result.post_peeling_edges = directed_post_edges / 2ull;

	for (ui v : matrix_ids)
		if (test_bit(marks, v))
			++result.matrix_after_vertices;
	for (const auto &edge : matrix_edges)
		if (test_bit(marks, matrix_ids[edge.first]) &&
			test_bit(marks, matrix_ids[edge.second]))
			++result.matrix_after_edges;

	// One root vertex visit plus one visit per directed CSR entry.  This is a
	// representation-independent proxy, not a prediction in microseconds.
	// A deferred query CSR intentionally stores directed_edges=0 to avoid a
	// whole-graph counting pass.  Do not publish a misleading Fallback saving
	// estimate in that case; the production gate currently does not consume it.
	const bool fallback_before_work_known = !graph.mapped || graph.directed_edges != 0u ||
		graph.minimum_degree_lower_bound != 0u || graph.directed_edge_lower_bound != static_cast<unsigned long long>(0);
	unsigned long long fallback_before_work = 0;
	if (fallback_before_work_known)
		fallback_before_work = !graph.mapped || graph.directed_edges != 0u
			? saturating_add_ull(graph.n, graph.directed_edges)
			: saturating_add_ull(graph.n, std::max(
				graph.directed_edge_lower_bound,
				saturating_mul_ull(graph.n,
					(unsigned long long)graph.minimum_degree_lower_bound)));
	unsigned long long fallback_after_work =
		saturating_add_ull(result.post_peeling_vertices, 2ull * result.post_peeling_edges);
	result.estimated_fallback_work_saved = fallback_before_work_known &&
		fallback_before_work > fallback_after_work
		? fallback_before_work - fallback_after_work : 0ull;
	result.complete = true;
	result.membership_materialized = true;
	result.estimated_index_build_us = timer.elapsed();

	return result;
}

bool query_kernel_contains(const QueryKernelResult &kernel, ui v)
{
	if (!kernel.membership_materialized)
		throw std::logic_error("query kernel membership is not materialized");
	return v < kernel.final_membership.size() * 64ull &&
		((kernel.final_membership[v >> 6] >> (v & 63u)) & 1ull);
}

struct CardinalitySpectrumAQERResult
{
	bool complete = false;
	bool forced_vertices_evaluated = false;
	bool qecc_evaluated = false;
	bool spectrum_comparison_complete = false;
	const char *guard_reason = "not_run";
	ui exact_size = 0;
	unsigned long long exact_kernel_vertices = 0;
	unsigned long long exact_kernel_edges = 0;
	unsigned long long spectrum_removed_from_u_kernel = 0;
	unsigned long long q_neighbors = 0;
	unsigned long long q_nonneighbors = 0;
	unsigned long long feasible_partitions = 0;
	bool spectrum_infeasible = false;
	bool qecc_infeasible = false;
	unsigned long long forced_removed_vertices = 0;
	unsigned long long forced_removed_q_neighbors = 0;
	unsigned long long forced_removed_q_nonneighbors = 0;
	unsigned long long edge_visits = 0;
	unsigned long long exact_kernel_build_edge_visits = 0;
	long long exact_kernel_build_us = 0;
	long long time_us = 0;
};

enum CardinalitySpectrumAQERCertificate
{
	CARDINALITY_SPECTRUM_AQER_NONE = 0,
	CARDINALITY_SPECTRUM_AQER_SPECTRUM_INFEASIBLE = 1,
	CARDINALITY_SPECTRUM_AQER_QECC_INFEASIBLE = 2
};

enum CardinalitySpectrumAQERProductionMode
{
	CARDINALITY_SPECTRUM_AQER_PRODUCTION_DISABLED = 0,
	CARDINALITY_SPECTRUM_AQER_PRODUCTION_SPECTRUM = 1,
	CARDINALITY_SPECTRUM_AQER_PRODUCTION_QECC = 2
};

CardinalitySpectrumAQERCertificate cardinality_spectrum_aqer_certificate(
	int production_mode, const CardinalitySpectrumAQERResult &result)
{
	// Fail open whenever construction or the capacity scan was guarded.
	if (production_mode == CARDINALITY_SPECTRUM_AQER_PRODUCTION_DISABLED ||
		!result.complete)
		return CARDINALITY_SPECTRUM_AQER_NONE;
	if ((production_mode & CARDINALITY_SPECTRUM_AQER_PRODUCTION_SPECTRUM) &&
		result.spectrum_infeasible)
		return CARDINALITY_SPECTRUM_AQER_SPECTRUM_INFEASIBLE;
	if ((production_mode & CARDINALITY_SPECTRUM_AQER_PRODUCTION_QECC) &&
		result.qecc_infeasible)
		return CARDINALITY_SPECTRUM_AQER_QECC_INFEASIBLE;
	return CARDINALITY_SPECTRUM_AQER_NONE;
}

unsigned long long capped_top_sum(const vector<ui> &sorted_values,
	ui count, ui cap)
{
	unsigned long long sum = 0;
	const ui limit = std::min<ui>(count, (ui)sorted_values.size());
	for (ui i = 0; i < limit; ++i)
		sum += std::min(sorted_values[i], cap);
	return sum;
}

unsigned long long capped_top_sum_with_forced(
	const vector<pair<ui, ui>> &sorted_values, ui forced_index,
	ui count, ui cap)
{
	if (count <= 1u)
		return 0;
	unsigned long long sum = 0;
	ui taken = 0;
	for (const auto &entry : sorted_values)
	{
		if (entry.second == forced_index)
			continue;
		sum += std::min(entry.first, cap);
		if (++taken == count - 1u)
			break;
	}
	return sum;
}

// Optimistic maximum number of internal edges in a selected block.  The
// degree top-sum and the complete-graph cap are both relaxations, so failure
// under this capacity is a strict infeasibility certificate.
unsigned long long internal_edge_capacity(const vector<ui> &sorted_degrees,
	unsigned long long total_edges, ui selected)
{
	if (selected < 2u)
		return 0;
	return std::min({total_edges,
		(unsigned long long)selected * (selected - 1ull) / 2ull,
		capped_top_sum(sorted_degrees, selected, selected - 1u) / 2ull});
}

unsigned long long forced_internal_edge_capacity(
	const vector<pair<ui, ui>> &sorted_degrees, ui forced_index,
	ui forced_degree, unsigned long long total_edges, ui selected)
{
	if (selected < 2u)
		return 0;
	const ui cap = selected - 1u;
	const unsigned long long degree_sum = std::min(forced_degree, cap) +
		capped_top_sum_with_forced(sorted_degrees, forced_index,
			selected, cap);
	return std::min({total_edges,
		(unsigned long long)selected * (selected - 1ull) / 2ull,
		degree_sum / 2ull});
}

unsigned long long cross_edge_capacity(const vector<ui> &sorted_left,
	const vector<ui> &sorted_right, unsigned long long total_edges,
	ui left_selected, ui right_selected)
{
	if (left_selected == 0u || right_selected == 0u)
		return 0;
	return std::min({total_edges,
		(unsigned long long)left_selected * right_selected,
		capped_top_sum(sorted_left, left_selected, right_selected),
		capped_top_sum(sorted_right, right_selected, left_selected)});
}

unsigned long long forced_cross_edge_capacity(
	const vector<pair<ui, ui>> &sorted_forced_side, ui forced_index,
	ui forced_degree, const vector<ui> &sorted_other_side,
	unsigned long long total_edges, ui forced_side_selected,
	ui other_side_selected)
{
	if (forced_side_selected == 0u || other_side_selected == 0u)
		return 0;
	const unsigned long long forced_side_sum =
		std::min(forced_degree, other_side_selected) +
		capped_top_sum_with_forced(sorted_forced_side, forced_index,
			forced_side_selected, other_side_selected);
	return std::min({total_edges,
		(unsigned long long)forced_side_selected * other_side_selected,
		forced_side_sum,
		capped_top_sum(sorted_other_side, other_side_selected,
			forced_side_selected)});
}

bool query_ego_capacities_feasible(ui target_k, ui exact_size,
	ui q_selected, ui z_selected, unsigned long long q_internal_capacity,
	unsigned long long z_internal_capacity,
	unsigned long long cross_capacity)
{
	if (q_selected < target_k ||
		(unsigned long long)q_selected + z_selected + 1ull != exact_size)
		return false;
	const unsigned long long adjacent_support = exact_size >= 2ull * target_k
		? 0ull : 2ull * target_k - exact_size;
	const unsigned long long nonadjacent_support =
		exact_size >= 2ull * target_k + 2ull
		? 0ull : 2ull * target_k + 2ull - exact_size;
	const unsigned long long q_neighbor_degree_demand =
		target_k == 0u ? 0ull : target_k - 1ull;
	return 2ull * q_internal_capacity + cross_capacity >=
			(unsigned long long)q_selected * q_neighbor_degree_demand &&
		2ull * z_internal_capacity + cross_capacity >=
			(unsigned long long)z_selected * target_k &&
		2ull * q_internal_capacity >=
			(unsigned long long)q_selected * adjacent_support &&
		cross_capacity >=
			(unsigned long long)z_selected * nonadjacent_support;
}

CardinalitySpectrumAQERResult evaluate_cardinality_spectrum_aqer(
	const QueryGraphView &graph, ui query_vertex, ui target_k,
	ui exact_size, const QueryKernelResult &u_kernel,
	const QueryKernelResult &exact_kernel,
	unsigned long long max_edge_visits,
	unsigned long long max_auxiliary_bytes,
	bool evaluate_forced_vertices,
	vector<ui> *forced_removed_output = nullptr,
	bool evaluate_query_ego_capacity = true)
{
	CardinalitySpectrumAQERResult result;
	result.exact_size = exact_size;
	result.guard_reason = "none";
	Timer timer;
	if (!exact_kernel.complete)
	{
		result.guard_reason = exact_kernel.guard_reason;
		result.time_us = timer.elapsed();
		return result;
	}
	result.exact_kernel_vertices = exact_kernel.post_peeling_vertices;
	result.exact_kernel_edges = exact_kernel.post_peeling_edges;
	if (u_kernel.complete)
	{
		result.spectrum_comparison_complete = true;
		result.spectrum_removed_from_u_kernel =
			u_kernel.post_peeling_vertices > exact_kernel.post_peeling_vertices
			? u_kernel.post_peeling_vertices - exact_kernel.post_peeling_vertices : 0ull;
	}
	if (exact_kernel.post_peeling_vertices < exact_size)
	{
		result.spectrum_infeasible = true;
		result.complete = true;
		result.guard_reason = "exact_kernel_below_target_size";
		result.time_us = timer.elapsed();
		return result;
	}
	if (!evaluate_query_ego_capacity)
	{
		result.complete = true;
		result.guard_reason = "qecc_disabled";
		result.time_us = timer.elapsed();
		return result;
	}
	if (!exact_kernel.membership_materialized)
	{
		result.guard_reason = "exact_kernel_membership_unavailable";
		result.time_us = timer.elapsed();
		return result;
	}
	result.qecc_evaluated = true;

	const vector<ui> &vertices = exact_kernel.kernel_vertices;
	const unsigned long long estimated_auxiliary_bytes =
		saturating_mul_ull(vertices.size(),
			evaluate_forced_vertices ? 112ull : 64ull);
	if (estimated_auxiliary_bytes > max_auxiliary_bytes)
	{
		result.guard_reason = "auxiliary_memory_estimate";
		result.time_us = timer.elapsed();
		return result;
	}
	std::unordered_map<ui, ui> position;
	position.reserve(vertices.size() * 2ull + 1ull);
	for (ui i = 0; i < vertices.size(); ++i)
		position[vertices[i]] = i;
	vector<unsigned char> block(vertices.size(), 0u);
	if (!query_kernel_contains(exact_kernel, query_vertex))
	{
		result.spectrum_infeasible = true;
		result.complete = true;
		result.guard_reason = "query_not_in_exact_kernel";
		result.time_us = timer.elapsed();
		return result;
	}
	if (!graph.for_each_neighbor(query_vertex, result.edge_visits,
		max_edge_visits, [&](ui v) {
			const auto found = position.find(v);
			if (found != position.end())
				block[found->second] = 1u;
		}))
	{
		result.guard_reason = "query_row_budget";
		result.time_us = timer.elapsed();
		return result;
	}
	for (ui i = 0; i < vertices.size(); ++i)
	{
		if (vertices[i] == query_vertex)
			continue;
		if (block[i] == 1u)
			++result.q_neighbors;
		else
		{
			block[i] = 2u;
			++result.q_nonneighbors;
		}
	}

	vector<ui> same_degree(vertices.size(), 0u);
	vector<ui> cross_degree(vertices.size(), 0u);
	unsigned long long q_internal_edges = 0;
	unsigned long long z_internal_edges = 0;
	unsigned long long cross_edges = 0;
	for (ui i = 0; i < vertices.size(); ++i)
	{
		if (block[i] == 0u)
			continue;
		const ui u = vertices[i];
		if (!graph.for_each_neighbor(u, result.edge_visits,
			max_edge_visits, [&](ui v) {
				const auto found = position.find(v);
				if (found == position.end())
					return;
				const ui j = found->second;
				if (block[j] == 0u)
					return;
				if (block[j] == block[i])
					++same_degree[i];
				else
					++cross_degree[i];
				if (u >= v)
					return;
				if (block[i] == 1u && block[j] == 1u)
					++q_internal_edges;
				else if (block[i] == 2u && block[j] == 2u)
					++z_internal_edges;
				else
					++cross_edges;
			}))
		{
			result.guard_reason = "block_edge_budget";
			result.time_us = timer.elapsed();
			return result;
		}
	}

	vector<ui> q_same, q_cross, z_same, z_cross;
	vector<pair<ui, ui>> q_same_indexed, q_cross_indexed;
	vector<pair<ui, ui>> z_same_indexed, z_cross_indexed;
	q_same.reserve(result.q_neighbors);
	q_cross.reserve(result.q_neighbors);
	z_same.reserve(result.q_nonneighbors);
	z_cross.reserve(result.q_nonneighbors);
	for (ui i = 0; i < vertices.size(); ++i)
	{
		if (block[i] == 1u)
		{
			q_same.push_back(same_degree[i]);
			q_cross.push_back(cross_degree[i]);
			if (evaluate_forced_vertices)
			{
				q_same_indexed.push_back(make_pair(same_degree[i], i));
				q_cross_indexed.push_back(make_pair(cross_degree[i], i));
			}
		}
		else if (block[i] == 2u)
		{
			z_same.push_back(same_degree[i]);
			z_cross.push_back(cross_degree[i]);
			if (evaluate_forced_vertices)
			{
				z_same_indexed.push_back(make_pair(same_degree[i], i));
				z_cross_indexed.push_back(make_pair(cross_degree[i], i));
			}
		}
	}
	auto descending_ui = [](ui a, ui b) { return a > b; };
	auto descending_pair = [](const pair<ui, ui> &a,
		const pair<ui, ui> &b) {
		return a.first != b.first ? a.first > b.first : a.second < b.second;
	};
	std::sort(q_same.begin(), q_same.end(), descending_ui);
	std::sort(q_cross.begin(), q_cross.end(), descending_ui);
	std::sort(z_same.begin(), z_same.end(), descending_ui);
	std::sort(z_cross.begin(), z_cross.end(), descending_ui);
	if (evaluate_forced_vertices)
	{
		std::sort(q_same_indexed.begin(), q_same_indexed.end(), descending_pair);
		std::sort(q_cross_indexed.begin(), q_cross_indexed.end(), descending_pair);
		std::sort(z_same_indexed.begin(), z_same_indexed.end(), descending_pair);
		std::sort(z_cross_indexed.begin(), z_cross_indexed.end(), descending_pair);
	}

	const ui maximum_q_selected = std::min<ui>(
		exact_size > 0u ? exact_size - 1u : 0u, (ui)q_same.size());
	for (ui q_selected = target_k; q_selected <= maximum_q_selected;
		++q_selected)
	{
		const ui z_selected = exact_size - 1u - q_selected;
		if (z_selected > z_same.size())
			continue;
		const unsigned long long q_capacity = internal_edge_capacity(
			q_same, q_internal_edges, q_selected);
		const unsigned long long z_capacity = internal_edge_capacity(
			z_same, z_internal_edges, z_selected);
		const unsigned long long x_capacity = cross_edge_capacity(
			q_cross, z_cross, cross_edges, q_selected, z_selected);
		if (query_ego_capacities_feasible(target_k, exact_size,
			q_selected, z_selected, q_capacity, z_capacity, x_capacity))
			++result.feasible_partitions;
	}
	result.qecc_infeasible = result.feasible_partitions == static_cast<unsigned long long>(0);
	if (result.qecc_infeasible)
	{
		result.complete = true;
		result.time_us = timer.elapsed();
		return result;
	}
	if (!evaluate_forced_vertices)
	{
		result.complete = true;
		result.time_us = timer.elapsed();
		return result;
	}
	result.forced_vertices_evaluated = true;

	for (ui forced = 0; forced < vertices.size(); ++forced)
	{
		if (block[forced] == 0u)
			continue;
		bool conditionally_feasible = false;
		for (ui q_selected = target_k; q_selected <= maximum_q_selected;
			++q_selected)
		{
			const ui z_selected = exact_size - 1u - q_selected;
			if (z_selected > z_same.size() ||
				(block[forced] == 1u && q_selected == 0u) ||
				(block[forced] == 2u && z_selected == 0u))
				continue;
			unsigned long long q_capacity;
			unsigned long long z_capacity;
			unsigned long long x_capacity;
			if (block[forced] == 1u)
			{
				q_capacity = forced_internal_edge_capacity(q_same_indexed,
					forced, same_degree[forced], q_internal_edges, q_selected);
				z_capacity = internal_edge_capacity(z_same, z_internal_edges,
					z_selected);
				x_capacity = forced_cross_edge_capacity(q_cross_indexed,
					forced, cross_degree[forced], z_cross, cross_edges,
					q_selected, z_selected);
			}
			else
			{
				q_capacity = internal_edge_capacity(q_same, q_internal_edges,
					q_selected);
				z_capacity = forced_internal_edge_capacity(z_same_indexed,
					forced, same_degree[forced], z_internal_edges, z_selected);
				x_capacity = forced_cross_edge_capacity(z_cross_indexed,
					forced, cross_degree[forced], q_cross, cross_edges,
					z_selected, q_selected);
			}
			if (query_ego_capacities_feasible(target_k, exact_size,
				q_selected, z_selected, q_capacity, z_capacity, x_capacity))
			{
				conditionally_feasible = true;
				break;
			}
		}
		if (!conditionally_feasible)
		{
			++result.forced_removed_vertices;
			if (block[forced] == 1u)
				++result.forced_removed_q_neighbors;
			else
				++result.forced_removed_q_nonneighbors;
			if (forced_removed_output != nullptr)
				forced_removed_output->push_back(vertices[forced]);
		}
	}
	result.complete = true;
	result.time_us = timer.elapsed();
	return result;
}

struct QueryKernelUseGateResult
{
	bool allow = false;
	const char *reason = "incomplete";
	unsigned long long predicted_saved_work = 0;
	unsigned long long construction_projection_work = 0;
	double matrix_vertex_reduction = 0.0;
	double matrix_edge_reduction = 0.0;
	double fallback_work_reduction = 0.0;
};

// Evaluate an exact query kernel only for the Fallback backend. This
// deliberately excludes Matrix projection work so a tiny two-hop Matrix view
// cannot hide a large all-domain Fallback. The 90% reduction and 2x benefit
// margin are structural cost guards; incomplete or unmaterialized kernels
// always retain the current search path.
QueryKernelUseGateResult query_kernel_fallback_only_gate(
		const QueryKernelResult &kernel,
		const QueryKernelPreGateResult &pre_gate,
		unsigned long long max_runtime_bytes,
		unsigned long long required_vertices)
{
	QueryKernelUseGateResult gate;
	gate.reason = "fallback_incomplete";
	if (!kernel.complete || !kernel.membership_materialized ||
		kernel.post_peeling_vertices < required_vertices ||
		kernel.kernel_vertices.empty() || kernel.final_membership.empty())
		return gate;
	const unsigned long long runtime_bytes = saturating_add_ull(
		saturating_mul_ull(kernel.post_peeling_vertices, 128ull),
		saturating_mul_ull(kernel.post_peeling_edges, 24ull));
	if (runtime_bytes > max_runtime_bytes)
	{
		gate.reason = "fallback_runtime_memory";
		return gate;
	}
	if (!pre_gate.fallback_work_known || pre_gate.fallback_work == static_cast<unsigned long long>(0))
	{
		gate.reason = "fallback_work_unknown";
		return gate;
	}
	gate.fallback_work_reduction =
		(double)kernel.estimated_fallback_work_saved /
		(double)pre_gate.fallback_work;
	if (gate.fallback_work_reduction < 0.90)
	{
		gate.reason = "fallback_reduction_below_90pct";
		return gate;
	}
	const unsigned long long kernel_fallback_work = saturating_add_ull(
		kernel.post_peeling_vertices, 2ull * kernel.post_peeling_edges);
	const unsigned long long original_work = saturating_mul_ull(
		pre_gate.remaining_trials, pre_gate.fallback_work);
	gate.construction_projection_work = saturating_add_ull(
		kernel.edge_visits, saturating_mul_ull(
			pre_gate.remaining_trials, kernel_fallback_work));
	gate.predicted_saved_work = original_work > gate.construction_projection_work
		? original_work - gate.construction_projection_work : 0ull;
	if (gate.construction_projection_work > original_work / 2ull)
	{
		gate.reason = "fallback_benefit_below_2x";
		return gate;
	}
	gate.allow = true;
	gate.reason = "fallback_path_cheaper";
	return gate;
}

// Matrix packed-word work and Fallback CSR work are measured in structural
// operations.  A nonempty shared kernel is materialized only when the same
// membership is predicted to save at least ten times its measured construction
// plus two-backend projection work.  Certificates are handled before this gate.
QueryKernelUseGateResult query_kernel_nonempty_gate(
		const QueryKernelResult &kernel,
		const QueryKernelPreGateResult &pre_gate,
		unsigned long long max_runtime_bytes)
{
	QueryKernelUseGateResult gate;
	if (!kernel.complete || kernel.post_peeling_vertices == static_cast<unsigned long long>(0))
		return gate;
	const unsigned long long runtime_bytes = saturating_add_ull(
		saturating_mul_ull(kernel.post_peeling_vertices, 128ull),
		saturating_mul_ull(kernel.post_peeling_edges, 24ull));
	if (runtime_bytes > max_runtime_bytes)
	{
		gate.reason = "runtime_memory";
		return gate;
	}
	gate.matrix_vertex_reduction = kernel.matrix_before_vertices == static_cast<unsigned long long>(0) ? 0.0 :
		1.0 - (double)kernel.matrix_after_vertices /
			(double)kernel.matrix_before_vertices;
	gate.matrix_edge_reduction = kernel.matrix_before_edges == static_cast<unsigned long long>(0) ? 0.0 :
		1.0 - (double)kernel.matrix_after_edges /
			(double)kernel.matrix_before_edges;
	gate.fallback_work_reduction = pre_gate.fallback_work == static_cast<unsigned long long>(0) ? 0.0 :
		(double)kernel.estimated_fallback_work_saved /
			(double)pre_gate.fallback_work;

	const unsigned long long kernel_words =
		(kernel.post_peeling_vertices + 63ull) >> 6;
	const unsigned long long kernel_matrix_work = saturating_add_ull(
		pre_gate.matrix_packed_only
			? saturating_mul_ull(kernel.post_peeling_vertices, kernel_words)
			: saturating_mul_ull(kernel.post_peeling_vertices,
				kernel.post_peeling_vertices),
		2ull * kernel.post_peeling_edges);
	const unsigned long long kernel_fallback_work = pre_gate.fallback_work_known
		? saturating_add_ull(kernel.post_peeling_vertices,
			2ull * kernel.post_peeling_edges) : 0ull;
	const unsigned long long kernel_trials_work = saturating_mul_ull(
		pre_gate.remaining_trials,
		saturating_add_ull(kernel_matrix_work, kernel_fallback_work));
	gate.construction_projection_work = saturating_add_ull(
		kernel.edge_visits, kernel_trials_work);
	gate.predicted_saved_work = pre_gate.predicted_search_work >
		gate.construction_projection_work
		? pre_gate.predicted_search_work - gate.construction_projection_work : 0ull;
	if (gate.construction_projection_work >= pre_gate.predicted_search_work)
	{
		gate.reason = "kernel_path_not_cheaper";
		return gate;
	}
	gate.allow = true;
	gate.reason = "kernel_path_cheaper";
	return gate;
}

void build_matrix_kernel_graph(const QueryKernelResult &kernel,
		const vector<ui> &full_ids, const vector<pair<ui, ui>> &full_edges,
		vector<ui> &kernel_ids, vector<pair<ui, ui>> &kernel_edges)
{
	if (!kernel.membership_materialized)
		throw std::logic_error("matrix kernel membership is not materialized");
	kernel_ids.clear();
	kernel_edges.clear();
	vector<ui> rid(full_ids.size(), INVALID_VERTEX);
	for (ui i = 0; i < full_ids.size(); ++i)
	{
		if (!query_kernel_contains(kernel, full_ids[i]))
			continue;
		rid[i] = (ui)kernel_ids.size();
		kernel_ids.push_back(full_ids[i]);
	}
	kernel_edges.reserve(kernel.matrix_after_edges);
	for (const auto &edge : full_edges)
		if (rid[edge.first] != INVALID_VERTEX && rid[edge.second] != INVALID_VERTEX)
			kernel_edges.push_back(make_pair(rid[edge.first], rid[edge.second]));
}

void build_fallback_kernel_graph(const QueryGraphView &graph,
		const QueryKernelResult &kernel, vector<ui> &kernel_ids,
		vector<pair<ui, ui>> &kernel_edges, ui query_vertex, ui &kernel_query)
{
	if (!kernel.membership_materialized)
		throw std::logic_error("fallback kernel membership is not materialized");
	kernel_ids = kernel.kernel_vertices;
	kernel_edges.clear();
	kernel_query = INVALID_VERTEX;
	std::unordered_map<ui, ui> rid;
	rid.reserve(kernel_ids.size() * 2ull + 1ull);
	for (ui i = 0; i < kernel_ids.size(); ++i)
	{
		rid[kernel_ids[i]] = i;
		if (kernel_ids[i] == query_vertex)
			kernel_query = i;
	}
	unsigned long long visits = 0;
	for (ui i = 0; i < kernel_ids.size(); ++i)
	{
		ui u = kernel_ids[i];
		graph.for_each_neighbor(u, visits,
			std::numeric_limits<unsigned long long>::max(), [&](ui v) {
				auto it = rid.find(v);
				if (it != rid.end() && i < it->second)
					kernel_edges.push_back(make_pair(i, it->second));
			});
	}
}

}

Graph::Graph(const char *_dir, const int _S)
{
	dir = string(_dir);
	S = _S;
	concise_log_enabled = false;
	n = m = 0;
	original_graph_n = 0;
	original_graph_m = 0;
	graph_fingerprint_ready = false;
	graph_fingerprint_lo = graph_fingerprint_hi = 0;
	pstart = nullptr;
	pend = pend_buf = nullptr;
	edges = nullptr;
	edgelist_pointer = nullptr;
	feasible_solution.clear();
	index_loaded = false;
	index_is_full = true;
	index_core_loaded = false;

	index_core_threshold_bitmap_loaded = false;
	index_core_threshold_max = 0;
	index_core_threshold_words = 0;
	index_core_threshold_bitmap_available = false;
	index_core_threshold_bitmap_offset = 0;
	index_core_threshold_bitmap_bytes = 0;
	index_core_threshold_bitmap_fd = -1;
	index_core_threshold_bitmap_map_base = MAP_FAILED;
	index_core_threshold_bitmap_map_length = 0;
	index_core_threshold_bitmap_mapped_data = nullptr;
	index_core_ordered_adjacency_loaded = false;
	index_core_ordered_adjacency_available = false;
	index_core_ordered_adjacency_offset = 0;
	index_core_ordered_adjacency_bytes = 0;
	index_core_ordered_adjacency_fd = -1;
	index_core_ordered_adjacency_map_base = MAP_FAILED;
	index_core_ordered_adjacency_map_length = 0;
	index_core_ordered_adjacency_mapped_data = nullptr;
	index_peel_loaded = false;
	index_peel_available = false;
	index_peel_load_us = 0;
	index_peel_offset = 0;
	index_peel_bytes = 0;
	index_peel_fd = -1;
	index_peel_map_base = MAP_FAILED;
	index_peel_map_length = 0;
	index_peel_mapped_data = nullptr;

	heuristic_epoch_counter = 0;
}

void Graph::set_concise_log(bool enabled)
{
	concise_log_enabled = enabled;
}

Graph::~Graph()
{
	release_index_core_threshold_bitmap_mapping();
	release_index_core_ordered_adjacency_mapping();
	release_index_peel_mapping();
	if (pstart != nullptr)
	{
		delete[] pstart;
		pstart = nullptr;
	}
	if (pend != nullptr)
	{
		delete[] pend;
		pend = nullptr;
	}
	if (pend_buf != nullptr)
	{
		delete[] pend_buf;
		pend_buf = nullptr;
	}
	if (edges != nullptr)
	{
		delete[] edges;
		edges = nullptr;
	}
	if (edgelist_pointer != nullptr)
	{
		delete[] edgelist_pointer;
		edgelist_pointer = nullptr;
	}
}

// [sizeof(ui)] [n] [m] [degree[0..n-1]] [edges[0..m-1]]

void Graph::readBinFile()
{
	static_assert(true,
		"the binary graph format requires 32-bit integers");
	if (pstart != nullptr || edges != nullptr)
		throw std::logic_error("a Graph instance can load only one graph");

	ifstream in(dir, ios::binary | ios::ate);
	if (!in)
		throw std::runtime_error("cannot open graph: " + dir);
	const std::streamoff file_bytes = in.tellg();
	auto invalid = [&](const char *reason) {
		throw std::runtime_error("invalid binary graph " + dir + ": " + reason);
	};
	if (file_bytes < std::streamoff(3 * sizeof(ui)))
		invalid("truncated header");
	in.seekg(0);
	auto read = [&](void *data, size_t bytes) {
		if (bytes != 0u && !in.read(static_cast<char *>(data),
			static_cast<std::streamsize>(bytes)))
			invalid("truncated or unreadable data");
	};
	ui integer_width = 0, vertex_count = 0, adjacency_count = 0;
	read(&integer_width, sizeof(ui));
	read(&vertex_count, sizeof(ui));
	read(&adjacency_count, sizeof(ui));
	if (integer_width != sizeof(ui))
		invalid("integer width must be 4 bytes");
	if (vertex_count > static_cast<ui>(std::numeric_limits<int>::max()))
		invalid("vertex count exceeds the supported signed-ID range");
	const unsigned long long expected_bytes = sizeof(ui) *
		(3ull + vertex_count + adjacency_count);
	if (static_cast<unsigned long long>(file_bytes) != expected_bytes)
		invalid("file size does not match the header");
	const unsigned long long max_adjacency = vertex_count == 0u ? 0ull :
		static_cast<unsigned long long>(vertex_count) * (vertex_count - 1ull);
	if ((adjacency_count & 1u) != 0u || adjacency_count > max_adjacency)
		invalid("invalid undirected adjacency count");

	// Reuse the degree array as reciprocal-row cursors after building the CSR.
	vector<ui> row_cursor(vertex_count);
	read(row_cursor.data(), sizeof(ui) * row_cursor.size());
	std::unique_ptr<ept[]> offsets(new ept[size_t(vertex_count) + 1]);
	offsets[0] = 0;
	unsigned long long degree_sum = 0;
	for (ui u = 0; u < vertex_count; ++u)
	{
		if (row_cursor[u] >= vertex_count)
			invalid("degree exceeds the simple-graph limit");
		degree_sum += row_cursor[u];
		if (degree_sum > adjacency_count)
			invalid("degree sum exceeds the adjacency count");
		offsets[u + 1] = static_cast<ept>(degree_sum);
	}
	if (degree_sum != adjacency_count)
		invalid("degree sum does not match the adjacency count");
	std::unique_ptr<ui[]> neighbors(new ui[adjacency_count]);
	read(neighbors.get(), sizeof(ui) * size_t(adjacency_count));
	if (in.peek() != std::char_traits<char>::eof() || in.bad())
		invalid("unexpected trailing or unreadable data");
	for (ui u = 0; u < vertex_count; ++u)
	{
		row_cursor[u] = offsets[u];
		for (ept i = offsets[u]; i < offsets[u + 1]; ++i)
		{
			const ui v = neighbors[i];
			if (v >= vertex_count || v == u)
				invalid("invalid neighbor ID or self-loop");
			if (i > offsets[u] && neighbors[i - 1] >= v)
				invalid("adjacency rows must be sorted and contain no duplicates");
		}
	}
	// Processing source vertices in ascending order consumes each reverse row
	// in sorted order, checking reciprocity in O(n+m) time without edge copies.
	for (ui u = 0; u < vertex_count; ++u)
		for (ept i = offsets[u]; i < offsets[u + 1]; ++i)
		{
			const ui v = neighbors[i];
			if (row_cursor[v] >= offsets[v + 1] || neighbors[row_cursor[v]] != u)
				invalid("every undirected edge must have a reciprocal entry");
			++row_cursor[v];
		}

	n = original_graph_n = vertex_count;
	m = original_graph_m = adjacency_count;
	pstart = offsets.release();
	edges = neighbors.release();
	graph_fingerprint_ready = false;
	cout << "[Graph] name=" << get_file_name_without_suffix(dir)
		<< " vertices=" << n << " edges=" << m / 2 << '\n';
	printf("[Graph] status=READY\n");
	fflush(stdout);
}

void Graph::ensure_graph_fingerprint()
{
	if (graph_fingerprint_ready)
		return;
	if (n != original_graph_n || m != original_graph_m)
	{
		fprintf(stderr, "Cannot fingerprint a graph after query-local shrinking.\n");
		exit(1);
	}
	auto mix = [](unsigned long long hash, unsigned long long value,
			unsigned long long prime) {
		value += 0x9e3779b97f4a7c15ull;
		value = (value ^ (value >> 30)) * 0xbf58476d1ce4e5b9ull;
		value = (value ^ (value >> 27)) * 0x94d049bb133111ebull;
		value ^= value >> 31;
		return (hash ^ value) * prime;
	};
	unsigned long long lo = 0xcbf29ce484222325ull;
	unsigned long long hi = 0x84222325cbf29ce4ull;
	lo = mix(lo, n, 0x100000001b3ull);
	hi = mix(hi, n, 0x9e3779b185ebca87ull);
	lo = mix(lo, m, 0x100000001b3ull);
	hi = mix(hi, m, 0x9e3779b185ebca87ull);
	for (ui u = 0; u < n; ++u)
	{
		unsigned long long degree = (unsigned long long)(pstart[u + 1] - pstart[u]);
		unsigned long long tagged = ((unsigned long long)u << 32) ^ degree;
		lo = mix(lo, tagged, 0x100000001b3ull);
		hi = mix(hi, tagged, 0x9e3779b185ebca87ull);
	}
	for (ept i = 0; i < m; ++i)
	{
		unsigned long long tagged = ((unsigned long long)i << 32) ^ edges[i];
		lo = mix(lo, tagged, 0x100000001b3ull);
		hi = mix(hi, tagged, 0x9e3779b185ebca87ull);
	}
	graph_fingerprint_lo = lo;
	graph_fingerprint_hi = hi;
	graph_fingerprint_ready = true;
}

std::string Graph::get_file_name_without_suffix(const std::string &file_path)
{
	size_t last_slash = file_path.find_last_of("/\\");
	size_t last_dot = file_path.find_last_of(".");

	if (last_dot == std::string::npos)
		return file_path.substr(last_slash + 1);

	if (last_slash == std::string::npos)
		return file_path.substr(0, last_dot);

	return file_path.substr(last_slash + 1, last_dot - last_slash - 1);
}

void Graph::ARC_SCS(const Query &query, int &k_min, int &k_max, const ARCSCSConfig &config)
{
	int query_vertex = query.vertex;
	const int LB_size = query.size_lower_bound;
	const int UB_size = query.size_upper_bound;
	const bool use_index = config.use_index;
	const bool preserve_graph = config.preserve_graph;
	const bool use_candidate_index = config.use_candidate_index;

	const unsigned long long matrix_memory_limit_mb = config.memory_limit_mb;

	// ARC-SCS exact kernel. The public entry is ARCSCSSolver::solve_arc_scs().

	last_query_result = QueryResult();
	if (LB_size <= 0 || UB_size < LB_size)
	{
		printf("Invalid size bounds: require 1 <= L <= U, got L=%d U=%d\n",
			LB_size, UB_size);
		last_query_result.core_source = "invalid_bounds";
		return;
	}
	if (query_vertex < 0 || (ui)query_vertex >= n)
	{
		printf("Wrong query vertex %d; valid range is [0, %u].\n",
			query_vertex, n == 0u ? 0u : n - 1);
		last_query_result.core_source = "invalid";
		return;
	}

	// Batch mode keeps the original CSR immutable.  A query-local CSR is
	// created only if core shrink actually removes vertices; heuristic-only
	// queries therefore allocate no graph copy.
	ui saved_n = n;
	ept saved_m = m;
	ept *saved_pstart = pstart;
	ui *saved_edges = edges;
	const ui *readonly_source_edges = saved_edges;
	bool readonly_source_core_ordered = false;
	bool owns_query_graph = false;
	bool query_graph_deferred = false;
	ui query_graph_min_degree_lower_bound = 0;
	unsigned long long query_graph_directed_edge_lower_bound = 0;

	Timer total_timer;

	unsigned long long adaptive_budget_query_removed_so_far = 0;
	unsigned long long work_adaptive_query_work_so_far = 0;
	unsigned long long work_adaptive_query_search_credit_so_far = 0;
	unsigned long long work_adaptive_query_removal_benefit_so_far = 0;
	unsigned long long work_adaptive_query_run_count = 0;
	ui work_adaptive_query_probe_interval = 1;

	bool matrix_memory_guarded = false;
	unsigned long long matrix_estimated_bytes = 0;

	shrink_old2new.clear();
	feasible_solution.clear();
	if (use_index)
	{
		if (!concise_query_log())
		{
			printf("[Index][Query] begin query_id=%d use_candidate_index=%d index_loaded=%d core_loaded=%d peel_loaded=%d\n",
				   query_vertex,
				   use_candidate_index ? 1 : 0,
				   index_loaded ? 1 : 0,
				   index_core_loaded ? 1 : 0,
				   index_peel_loaded ? 1 : 0);
			fflush(stdout);
			if (use_candidate_index && index_loaded && query_vertex >= 0)
			{
				unsigned long long diag_begin = 0, diag_end = 0;
				bool diag_hit = get_index_range((ui)query_vertex, diag_begin, diag_end);
				if (!diag_hit)
				{
					printf("[Index][Query] index miss query_id=%d action=continue_with_non_candidate_index_path\n", query_vertex);
					fflush(stdout);
				}
			}
		}
	}

	char *vis = nullptr;
	ui *peel_sequence = nullptr;
	ui *core = nullptr;
	ui *degree = nullptr;
	bool owns_peel_sequence = false;
	bool owns_core = false;
	ListLinearHeap *heap = nullptr;
	ui core_q = n;
	ui UB = n;
	const char *core_source = "degen";
	// Borrow immutable core/peel index arrays until exact search is known to
	// be necessary.  This removes two graph-sized allocations from
	// heuristic-only queries.

	if (use_index && index_core_loaded && index_core.size() == n)
	{
		core = index_core.data();
		core_q = core[query_vertex];
		if (index_peel_loaded && index_peel_mapped_data != nullptr)
			peel_sequence = const_cast<ui *>(index_peel_mapped_data);
		else if (index_peel_loaded && index_peel_sequence.size() == n)
			peel_sequence = index_peel_sequence.data();
		// A core-only index intentionally leaves peel_sequence null.  Core-based
		// shrinking scans core[] directly and does not reconstruct a graph-wide
		// ordering at query time.

		core_source = "index";
	}
	else
	{
		vis = new char[n];
		peel_sequence = new ui[n];
		core = new ui[n];
		degree = new ui[n];
		owns_peel_sequence = true;
		owns_core = true;
		heap = new ListLinearHeap(n, n - 1);

			UB = degen(n, peel_sequence, core, pstart, edges, degree, vis, heap, core_q, query_vertex);

	}
	k_max = (static_cast<ui>(k_max) > core_q) ? core_q : k_max;

	ui original_q_idx = query_vertex;
	int t_k_min = 0;
	vector<ui> record_solution;
	bool find_feasible_solution = false, find_optimal_solution = false;
	vector<ui> heu_solution;

#ifdef _HEURISTIC_
	// For core(q)<=1 the bounded connected witness below is already exact;
	// avoid a graph-sized greedy workspace just to rediscover that fact.
	if (k_max > 1)
	{

	SCS_heu_star(query_vertex, LB_size, UB_size, heu_solution, t_k_min, k_max, core);

	{

		budgeted_monotone_multistart_refine(query_vertex, LB_size, UB_size, heu_solution, t_k_min, k_max, core);

	}

	}
#endif
	int witnessed_degree = -1;
	if (!certify_community(heu_solution, original_q_idx, LB_size, UB_size,
		saved_n, saved_pstart, saved_edges, witnessed_degree))
	{
		const int witness_size = min(UB_size, max(LB_size, k_max > 0 ? 2 : 1));
		heu_solution = connected_size_witness(original_q_idx, witness_size, saved_pstart, saved_edges);
		if (heu_solution.size() < (size_t)LB_size)
		{
			last_query_result.infeasible = true;
			last_query_result.opt_k = -1;
			last_query_result.core_source = core_source;
			last_query_result.total_us = total_timer.elapsed();
			printf("[Feasibility] component_size=%zu required_size=%d exhausted=1\n", heu_solution.size(), LB_size);
			printf("[Timing] total_us=%s index_load_excluded=%d\n",
				Utility::integer_to_string(last_query_result.total_us).c_str(), use_index ? 1 : 0);
			printf("[Result] status=NO_FEASIBLE min_degree=-1 community_size=0\n[Community] vertices:\n");
			delete heap;
			if (owns_core) delete[] core;
			if (owns_peel_sequence) delete[] peel_sequence;
			delete[] vis;
			delete[] degree;
			return;
		}
		if (!certify_community(heu_solution, original_q_idx, LB_size, UB_size,
			saved_n, saved_pstart, saved_edges, witnessed_degree))
			throw std::logic_error("connected size witness failed its certificate");
		printf("[Feasibility] connected_witness_size=%zu min_degree=%d\n", heu_solution.size(), witnessed_degree);
	}
	// Caller-supplied integers and heuristic placeholders cannot certify a bound.
	t_k_min = witnessed_degree;
	k_min = witnessed_degree;
	const bool anchor_gate_audit =
		std::getenv("ARC_SCS_ANCHOR_GATE_AUDIT") != nullptr;
	LowDegreeAnchorWitnessResult anchor_witness;

	// This witness is deliberately isolated to the single problematic range.
	// Every returned community is certified against the immutable source CSR;
	// a miss or any work cap leaves the existing lower bound and exact path unchanged.
	if ((LB_size == 18) && (UB_size == 20))
	{
		anchor_witness = bounded_low_degree_anchor_witness(
			true, original_q_idx, LB_size, UB_size, k_min, core_q, core,
			saved_n, saved_pstart, saved_edges);

		if (anchor_witness.found &&
			anchor_witness.certified_degree > k_min)
		{
			heu_solution = anchor_witness.solution;
			witnessed_degree = anchor_witness.certified_degree;
			t_k_min = witnessed_degree;
			k_min = witnessed_degree;

		}
	}
	else
	{
		anchor_witness.reason = ("range");
	}
	if (anchor_witness.eligible || anchor_gate_audit)
	{

		fflush(stdout);
	}
	if (anchor_gate_audit)
		throw std::runtime_error("ANCHOR_GATE_AUDIT_COMPLETE");

	bool heu_is_optimal = false;

	if (!heu_solution.empty() && k_min == k_max)
	{

		find_optimal_solution = true;
		heu_is_optimal = true;
	}

	if (!find_optimal_solution)
	{
		// Pure CTBI has no peel fallback. H-CTBI uses a structural source-size
		// gate: above the configured cap it follows the byte-identical IDX9
		// core+peel path. A zero cap disables CTBI only when peel is available.
		const bool ctbi_structural_gate = !index_peel_available ||
			((n <= 4294967295u));
		const bool ctbi_threshold_available = preserve_graph && use_index &&
			ctbi_structural_gate && index_core_threshold_bitmap_available &&
			k_min >= 0 && (ui)k_min <= index_core_threshold_max &&
			index_core_threshold_counts.size() > (size_t)k_min &&
			index_core_threshold_core_sums.size() > (size_t)k_min;
		const bool use_ctbi_shrink = ctbi_threshold_available &&
			ensure_index_core_threshold_bitmap_loaded();

		// CTBI encodes the exact survivor order and never needs peel. Legacy
		// core+peel indexes retain their lazy mmap path unchanged.
		if (!use_ctbi_shrink && use_index && peel_sequence == nullptr && index_peel_available)
		{
			if (!ensure_index_peel_loaded())
				printf("[Index][Peel] unavailable; continuing with the exact core-only path\n");
			else
				peel_sequence = const_cast<ui *>(index_peel_mapped_data);
		}

		// With S=1 and incumbent size k_min+1, the original shrink predicate is
		// exactly core[v] > k_min, which is the CTBI bitmap definition.
		S = 1;
		give_ininital_feasible_sol(S + k_min);
		ui old_size = feasible_solution.size(), pre_n = n;
		query_graph_min_degree_lower_bound = feasible_solution.size() >= (size_t)S
			? (ui)(feasible_solution.size() - (size_t)S + 1ull) : 0u;
		if (!use_ctbi_shrink && preserve_graph && !owns_core)
		{
			ui *mutable_core = new ui[pre_n];
			memcpy(mutable_core, core, sizeof(ui) * pre_n);
			core = mutable_core;
			owns_core = true;
		}
		if (!use_ctbi_shrink && peel_sequence != nullptr && !owns_peel_sequence &&
			(preserve_graph || index_peel_mapped_data != nullptr))
		{
			ui *mutable_peel = new ui[pre_n];
			memcpy(mutable_peel, peel_sequence, sizeof(ui) * pre_n);
			peel_sequence = mutable_peel;
			owns_peel_sequence = true;
		}

		ui survivor_count = 0;
		query_graph_directed_edge_lower_bound = 0;
		if (use_ctbi_shrink)
		{
			const unsigned long long indexed_count =
				index_core_threshold_counts[(size_t)k_min];
			if (indexed_count > pre_n)
			{
				printf("[CTBI] invalid survivor count for threshold=%d\n", k_min);
				exit(1);
			}
			survivor_count = (ui)indexed_count;
			query_graph_directed_edge_lower_bound =
				index_core_threshold_core_sums[(size_t)k_min];
			// COAP pays an extra adjacency stream and changes Matrix numbering.
			// Use it only when either the source is genuinely dense or core
			// shrink removes at least three quarters of the vertices. Both are
			// representation/work boundaries independent of dataset identity.
			const bool dense_source =
				(unsigned long long)saved_m >= 64ull * (unsigned long long)saved_n;
			const bool strong_core_shrink =
				4ull * indexed_count <= (unsigned long long)pre_n;
			const bool coap_gate = dense_source || strong_core_shrink;
			if (coap_gate && index_core_ordered_adjacency_available &&
				ensure_index_core_ordered_adjacency_loaded())
			{
				readonly_source_edges = index_core_ordered_adjacency_mapped_data;
				readonly_source_core_ordered = true;
			}

		}
		else
		{
			for (ui i = 0; i < pre_n; ++i)
				if (core[i] + S > feasible_solution.size())
				{
					++survivor_count;
					query_graph_directed_edge_lower_bound = saturating_add_ull(
						query_graph_directed_edge_lower_bound, core[i]);
				}
		}
		ui *out_mapping = new ui[survivor_count == 0u ? 1 : survivor_count];
		ui *old2new = nullptr;

		if (use_ctbi_shrink)
		{
			// Keep the mapping representation identical to the legacy path. This
			// avoids a persistent touched-list allocation perturbing later batch
			// queries while CTBI still removes the core/peel copies and core scan.
			shrink_old2new.assign(pre_n, INVALID_VERTEX);
			old2new = shrink_old2new.data();
			ui *local_core = survivor_count == pre_n ? nullptr :
				new ui[survivor_count == 0u ? 1 : survivor_count];
			ui cnt = 0;
			const char *bitmap = index_core_threshold_bitmap_mapped_data +
				(size_t)k_min * (size_t)index_core_threshold_words *
				sizeof(unsigned long long);
			for (unsigned long long word_id = 0;
				 word_id < index_core_threshold_words; ++word_id)
			{
				unsigned long long word = 0;
				memcpy(&word, bitmap + (size_t)word_id * sizeof(word), sizeof(word));
				while (word != static_cast<unsigned long long>(0))
				{
					const ui bit = (ui)__builtin_ctzll(word);
					const ui v = (ui)((word_id << 6) + bit);
					word &= word - 1ull;
					if (v >= pre_n)
						continue;
					old2new[v] = cnt;
					out_mapping[cnt] = v;
					if (local_core != nullptr)
						local_core[cnt] = core[v];
					++cnt;
				}
			}
			if (cnt != survivor_count)
			{
				printf("[CTBI] bitmap/count mismatch threshold=%d bitmap=%u header=%u\n",
					k_min, cnt, survivor_count);
				exit(1);
			}
			if (local_core == nullptr)
			{
				pstart = saved_pstart;
				edges = saved_edges;
				owns_query_graph = false;
				query_graph_deferred = false;
			}
			else
			{
				core = local_core;
				owns_core = true;
				n = survivor_count;
				m = 0;
				pstart = saved_pstart;
				edges = saved_edges;
				owns_query_graph = false;
				query_graph_deferred = true;
			}
			const char *ordered_core_source = "index_coap";
			core_source = readonly_source_core_ordered ? ordered_core_source : "index_ctbi";

		}
		else
		{
			shrink_old2new.assign(pre_n, INVALID_VERTEX);
			old2new = shrink_old2new.data();
			if (preserve_graph)
			{
				const bool defer_query_csr = use_index;
				core_shrink_graph_readonly(n, m, peel_sequence, core, out_mapping, old2new,
									 saved_pstart, saved_edges, pstart, edges,
									 owns_query_graph, query_graph_deferred,
									 defer_query_csr, false);
			}
			else
				core_shrink_graph(n, m, peel_sequence, core, out_mapping, nullptr, old2new, pstart, edges, false);
		}

		if (n != pre_n)
		{
			update_query_vertex(n, out_mapping, query_vertex, original_q_idx);
			if (static_cast<ui>(query_vertex) == n)
			{
				printf("Sorry! But the query vertex is deleted from the graph! There is no qualified feasible solution!!\n");
				find_optimal_solution = true;
			}
		}

		if (!find_optimal_solution)
		{
			vector<ui> ids;
			vector<pair<ui, ui>> vp;

			bool extracted_from_index = false;

			if (use_index && use_candidate_index)
			{
				if (query_graph_deferred)
					extracted_from_index = extract_subgraph_from_index_readonly(
						original_q_idx, k_min, out_mapping, saved_pstart, readonly_source_edges,
						readonly_source_core_ordered, ids, vp);
				else
					extracted_from_index = extract_subgraph_from_index(original_q_idx, k_min, ids, vp);
			}
			if (!extracted_from_index)
			{
				if (query_graph_deferred)
					extracted_from_index = extract_subgraph_within_2hops_readonly(
						original_q_idx, out_mapping, saved_pstart, readonly_source_edges,
						readonly_source_core_ordered, ids, vp);
				if (query_graph_deferred && !extracted_from_index)
				{
					materialize_query_csr_from_mapping(saved_n, n, old2new,
						 saved_pstart, readonly_source_edges, readonly_source_core_ordered,
						 pstart, edges, m,
						 owns_query_graph);
					query_graph_deferred = false;
				}
				if (!extracted_from_index)
				{
					ui *local_rid = new ui[n];
					if (vis == nullptr)
						vis = new char[n];
					memset(vis, 0, sizeof(char) * n);
					extract_subgraph_within_2hops(query_vertex, ids, local_rid, vp, vis, pstart, edges);
					delete[] local_rid;
				}
			}

			S = LB_size > k_max ? LB_size - k_max : 1;
			ui initial_size = (S > static_cast<ui>(LB_size - 1)) ? S : LB_size - 1;
			initial_size = (initial_size > S + k_min) ? initial_size : (S + k_min);
			give_ininital_feasible_sol(initial_size);

			// The extracted local graph is immutable throughout all S trials of
			// this query.  Prepare its matrix/bit rows/CSR/core once and rebuild
			// only the mutable root state in find_feasible().
			const unsigned long long dense_matrix_cells =
				saturating_mul_ull((unsigned long long)ids.size(),
							   (unsigned long long)ids.size());
			const bool use_matrix_packed_only =
				(dense_matrix_cells >
					saturating_mul_ull(512,
								   1024ull * 1024ull));
			matrix_estimated_bytes =
				estimate_matrix_memory_bytes((ui)ids.size(), vp.size(),
									 true,
									 use_matrix_packed_only);
			unsigned long long matrix_memory_limit_bytes =
				saturating_mul_ull(matrix_memory_limit_mb, 1024ull * 1024ull);
			if (matrix_estimated_bytes > matrix_memory_limit_bytes)
			{
				matrix_memory_guarded = true;
				printf("[MemoryGuard] status=OOM_GUARDED component=MBBPS_matrix query=%u local_n=%zu local_m=%zu packed_only=%d estimated_bytes=%llu limit_bytes=%llu\n",
					   original_q_idx, ids.size(), vp.size(),
					   use_matrix_packed_only ? 1 : 0, matrix_estimated_bytes,
					   matrix_memory_limit_bytes);
				fflush(stdout);
			}
			else
			{
			MBBPS_matrix MBBPS_solver_m;

			MBBPS_solver_m.set_use_matrix_capacity_set_branch(32);
			MBBPS_solver_m.set_pair_capacity_bound(512);
			MBBPS_solver_m.set_adaptive_triple_capacity_bound(256);
			MBBPS_solver_m.set_automatic_work_ledger();

			MBBPS_solver_m.set_packed_only_adjacency(use_matrix_packed_only);
			MBBPS_solver_m.set_use_matrix_state_trail(true);
			MBBPS_solver_m.set_use_matrix_rr1_bucket_bitset(
				true);
			// Wave batching is valuable on the normal Matrix workload, but a large,
			// sparse, high-slack local graph can turn its reordered propagation
			// closure into a radically larger proof tree. Keep WB-DLP everywhere
			// else and retain the established FIFO propagation only for that
			// structural risk class. The thresholds are representation/work
			// boundaries and do not depend on a dataset or query identifier.
			const bool wbdlp_order_instability_guard =
				(ids.size() >= 2048u) &&
				S >= static_cast<ui>(2 * k_max) &&
				2ull * (unsigned long long)vp.size() <=
					(unsigned long long)S * (unsigned long long)ids.size();
			MBBPS_solver_m.set_use_matrix_batched_degree_loss(
				(!wbdlp_order_instability_guard),
				(ui)1);

			std::map<ui, QueryKernelResult> query_kernel_cache;
			std::map<ui, QueryKernelPreGateResult> query_kernel_pre_gate_cache;
			std::map<ui, bool> query_kernel_credit_recorded;
			std::set<std::pair<int, int>> aqer_witness_commit_misses;
			QueryGraphView query_kernel_graph = {
				n, m, pstart, edges, query_graph_deferred,
				out_mapping, old2new, saved_pstart, readonly_source_edges,
				readonly_source_core_ordered, query_graph_min_degree_lower_bound,
				query_graph_directed_edge_lower_bound};
			const bool query_kernel_production_enabled =
				(ids.size() >= (size_t)LB_size);
			const bool query_kernel_fallback_candidate =
				(ids.size() < (size_t)LB_size);
			const bool query_kernel_construction_enabled =
				query_kernel_production_enabled || query_kernel_fallback_candidate;

			// AQER probes consume branch-node credit in the same unit reported by
			// both exact backends. Production credit comes only from candidate
			// decisions avoided by an exact certificate and unused prior credit.
			ARCWorkLedger aqer_matrix_work;
			ARCWorkLedger aqer_fallback_work;

            bool deferred_neighbor_probe_attempted = false;
    bool wide_range_neighbor_probe_attempted = false;
			bool matrix_graph_prepared = false;
			bool matrix_graph_is_kernel = false;
			ui matrix_graph_target = INVALID_VERTEX;
			if (k_min < k_max)
			{
				assert(!ids.empty());
				MBBPS_solver_m.allocateMemory((ui)ids.size());

			}
			while (k_min < k_max)
			{
				QueryKernelPreGateResult *query_kernel_pre_gate = nullptr;
				if (query_kernel_construction_enabled)
				{
					auto gate_it = query_kernel_pre_gate_cache.find((ui)k_max);
					if (gate_it == query_kernel_pre_gate_cache.end())
					{
						const bool fallback_may_run =
							query_kernel_fallback_may_run(S, k_max, k_min,
								LB_size, UB_size, feasible_solution.size(), n);
						const unsigned long long remaining_trials =
							S + k_max <= static_cast<ui>(UB_size)
							? (unsigned long long)(UB_size - k_max - S + 1) : 1ull;

						QueryKernelPreGateResult gate;
						{
							gate = query_kernel_preconstruction_gate(query_kernel_graph,
								ids, vp, remaining_trials, fallback_may_run,
								use_matrix_packed_only, 0ull);

						}
						if (gate.allow || !concise_query_log())
						{

							fflush(stdout);
						}
						gate_it = query_kernel_pre_gate_cache.insert(
							make_pair((ui)k_max, gate)).first;
					}
					query_kernel_pre_gate = &gate_it->second;
				}
				const bool aqer_witness_commit_retry =
					(aqer_witness_commit_misses.count(std::make_pair(S, k_max)) != 0u);
				const bool aqer_final_trial =
					(S + k_max == static_cast<ui>(UB_size));
				// Final-only must also gate construction, not merely certificate
				// evaluation.  Otherwise every non-final trial pays for an AQER
				// kernel that cannot be consumed by the production rule.
				// Production AQER is a zero-extra-kernel consumer: it may reuse a
				// kernel already admitted by the established dominance gate, but it
				// must not construct a rejected large kernel merely to discover that
				// it exceeds the final 512-vertex cap.  All retained witness events
				// are on dominance-admitted kernels.
				const bool aqer_requires_query_kernel = (aqer_final_trial) && !aqer_witness_commit_retry &&
					query_kernel_pre_gate != nullptr && query_kernel_pre_gate->allow;
				QueryKernelResult *query_kernel = nullptr;
				if ((aqer_requires_query_kernel) || ((query_kernel_construction_enabled) && (query_kernel_pre_gate != nullptr) && (query_kernel_pre_gate->allow)))
				{
					auto cached = query_kernel_cache.find((ui)k_max);
					if (cached == query_kernel_cache.end())
					{
						QueryKernelResult result = build_query_kernel(
							query_kernel_graph, core, query_vertex, (ui)k_max, (ui)UB_size, ids, vp, query_kernel_construction_enabled && query_kernel_pre_gate != nullptr &&
							query_kernel_pre_gate->allow
								? query_kernel_pre_gate->edge_visit_budget : 250000000ull, true);

						cached = query_kernel_cache.insert(make_pair((ui)k_max,
							std::move(result))).first;
					}
					query_kernel = &cached->second;
				}
				const unsigned long long target_required_size = std::max(
					(unsigned long long)LB_size, (unsigned long long)k_max + 1ull);
				const bool kernel_enabled_for_search =
					query_kernel_production_enabled && query_kernel_pre_gate != nullptr &&
					query_kernel_pre_gate->allow;
				const bool kernel_empty_certificate =
					kernel_enabled_for_search && query_kernel != nullptr &&
					query_kernel->complete && query_kernel->post_peeling_vertices == static_cast<unsigned long long>(0);

				const bool kernel_size_infeasible_certificate =
					(kernel_enabled_for_search) && query_kernel != nullptr &&
					query_kernel->complete && query_kernel->post_peeling_vertices > static_cast<unsigned long long>(0) &&
					query_kernel->post_peeling_vertices < target_required_size;
				const bool kernel_infeasible_certificate =
					kernel_empty_certificate || kernel_size_infeasible_certificate;
				const bool kernel_direct_feasible_certificate =
					kernel_enabled_for_search && query_kernel != nullptr &&
					query_kernel->complete && query_kernel->membership_materialized &&
					query_kernel->post_peeling_vertices >= (unsigned long long)LB_size &&
					query_kernel->post_peeling_vertices <= (unsigned long long)UB_size;
				const bool aqer_cardinality_allowed =
					(aqer_final_trial &&
					!aqer_witness_commit_retry);
				const bool cardinality_spectrum_production_enabled =
					(kernel_enabled_for_search) && aqer_cardinality_allowed;
				const int cardinality_spectrum_mode_for_trial =
					cardinality_spectrum_production_enabled &&
					!kernel_infeasible_certificate &&
					!kernel_direct_feasible_certificate
					? (1 |
			2)
					: CARDINALITY_SPECTRUM_AQER_PRODUCTION_DISABLED;
				CardinalitySpectrumAQERResult cardinality_spectrum;
				CardinalitySpectrumAQERCertificate cardinality_certificate =
					CARDINALITY_SPECTRUM_AQER_NONE;
				CardinalitySpectrumAQERCertificate observed_cardinality_certificate =
					CARDINALITY_SPECTRUM_AQER_NONE;
				const bool evaluate_cardinality_spectrum = (query_kernel != nullptr &&
					aqer_cardinality_allowed);
				if (evaluate_cardinality_spectrum)
				{
					const ui exact_h = (ui)(S + k_max);
					// The existing progressive AQER budget targets graph projection,
					// and can be too small even to finish an exact-h certificate.
					// Keep this independently fail-open under the established hard cap.
					const unsigned long long certificate_edge_budget =
						query_kernel_pre_gate != nullptr
							? query_kernel_pre_gate->predicted_search_work
							: query_kernel->edge_visits;
					const unsigned long long certificate_memory_limit_bytes =
						saturating_mul_ull(matrix_memory_limit_mb,
							1024ull * 1024ull);
					QueryKernelResult exact_kernel_storage;
					const QueryKernelResult *exact_kernel = query_kernel;
					unsigned long long qecc_edge_budget = certificate_edge_budget;
					const bool reuse_u_kernel = exact_h == (ui)UB_size &&
						query_kernel->complete;
					if (!reuse_u_kernel)
					{
						const unsigned long long graph_words =
							((unsigned long long)query_kernel_graph.n + 63ull) >> 6;
						const unsigned long long estimated_kernel_peak_bytes =
							saturating_add_ull(2ull * graph_words *
								sizeof(unsigned long long),
								saturating_mul_ull(8ull, query_kernel_graph.n));
						if (estimated_kernel_peak_bytes > certificate_memory_limit_bytes)
							exact_kernel_storage.guard_reason =
								"certificate_memory_estimate";
						else
							exact_kernel_storage = build_query_kernel(
								query_kernel_graph, core, query_vertex, (ui)k_max, exact_h, ids, vp, certificate_edge_budget, true);
						exact_kernel = &exact_kernel_storage;
						qecc_edge_budget = exact_kernel_storage.edge_visits <
							certificate_edge_budget
							? certificate_edge_budget - exact_kernel_storage.edge_visits
							: 0ull;
					}
					const bool evaluate_qecc =
						true;
					cardinality_spectrum = evaluate_cardinality_spectrum_aqer(
						query_kernel_graph, query_vertex, (ui)k_max, exact_h,
						*query_kernel, *exact_kernel, qecc_edge_budget,
						certificate_memory_limit_bytes,
						false, nullptr,
						evaluate_qecc);
					if (!reuse_u_kernel)
					{
						cardinality_spectrum.exact_kernel_build_edge_visits =
							exact_kernel_storage.edge_visits;
						cardinality_spectrum.exact_kernel_build_us =
							exact_kernel_storage.estimated_index_build_us;
					}
					cardinality_certificate = cardinality_spectrum_aqer_certificate(
						cardinality_spectrum_mode_for_trial,
						cardinality_spectrum);
					observed_cardinality_certificate = cardinality_spectrum_aqer_certificate(
						CARDINALITY_SPECTRUM_AQER_PRODUCTION_SPECTRUM |
							((CARDINALITY_SPECTRUM_AQER_PRODUCTION_QECC)),
						cardinality_spectrum);

				}
				const unsigned long long kernel_runtime_limit_bytes =
					saturating_mul_ull(matrix_memory_limit_mb, 1024ull * 1024ull);
				QueryKernelUseGateResult kernel_use_gate;
				if (kernel_enabled_for_search && query_kernel != nullptr &&
					!kernel_infeasible_certificate && !kernel_direct_feasible_certificate)
				{

					kernel_use_gate = (query_kernel_nonempty_gate(*query_kernel,
							*query_kernel_pre_gate, kernel_runtime_limit_bytes));
				}
				// A shared query kernel can reduce the Matrix projection while still
				// expanding the graph handed to the Fallback backend.  On an already
				// small Matrix instance this is a sharp representation discontinuity:
				// the normal Matrix path is cheap, whereas even a bounded Fallback
				// retry can make one B&B node extremely expensive.  Keep all exact
				// empty/size/direct certificates above, and fail open to the established
				// path only for non-certificate kernels that expand such a small local
				// graph.  This is structural and independent of dataset/query identity.
				// Preserve the guard unless the independently estimated Fallback
				// saving is overwhelming. This narrow exception prevents a tiny
				// Matrix projection from hiding a much larger Fallback proof tree.

					// Strict witness-only AQER can reject a certificate and immediately
					// re-enter the same (S,k) trial.  If that certificate was evaluated on
					// a complete kernel whose Fallback reduction is already overwhelming,
					// reuse the paid-for kernel on the retry instead of discarding it and
					// materializing the much larger established graph.  This is structural:
					// no dataset or query identity participates, and incomplete kernels fail
					// open to the established path.
					const bool aqer_retry_reuse_existing_kernel =
						aqer_witness_commit_retry && query_kernel != nullptr &&
						query_kernel->complete && !query_kernel->kernel_vertices.empty() &&
						!query_kernel->final_membership.empty() &&
						query_kernel_pre_gate != nullptr &&
						query_kernel_pre_gate->fallback_work_known &&
						kernel_use_gate.fallback_work_reduction >= 0.90;
					if (aqer_retry_reuse_existing_kernel)
					{
						kernel_use_gate.allow = true;
						kernel_use_gate.reason = "aqer_retry_reuse_existing_kernel";

						fflush(stdout);
					}
					// Missing membership is an unavailable optional optimization, not an
					// empty exact domain. Fail open to the established search path.
					if (kernel_use_gate.allow && query_kernel != nullptr &&
						!query_kernel->membership_materialized)
					{
						kernel_use_gate.allow = false;
						kernel_use_gate.reason = "kernel_membership_unavailable";
					}
					const bool use_kernel_graph = kernel_use_gate.allow;
					QueryKernelUseGateResult fallback_kernel_gate;
					if (query_kernel_fallback_candidate &&
						query_kernel_pre_gate != nullptr &&
						query_kernel_pre_gate->allow && query_kernel != nullptr)
					{
						fallback_kernel_gate = query_kernel_fallback_only_gate(
							*query_kernel, *query_kernel_pre_gate,
							kernel_runtime_limit_bytes, target_required_size);
					}
					const bool use_fallback_only_kernel = fallback_kernel_gate.allow;
					const bool use_fallback_kernel_graph =
						use_kernel_graph || use_fallback_only_kernel;
					const bool fallback_kernel_constructed =
						query_kernel_fallback_candidate && query_kernel != nullptr;

					if (fallback_kernel_constructed)
					{

						fflush(stdout);
					}

				// Keep the base AQER gate/credit trajectory independent of the
				// exact-cardinality certificate.  The latter skips one trial but
				// must not make an otherwise unproductive U-kernel lane look useful.

				const bool preserve_kernel_for_witness_retry =
					(!aqer_witness_commit_retry) &&
					cardinality_certificate != CARDINALITY_SPECTRUM_AQER_NONE &&
						!use_kernel_graph && query_kernel->complete &&
						!query_kernel->kernel_vertices.empty() &&
						!query_kernel->final_membership.empty() &&
					query_kernel_pre_gate != nullptr &&
					query_kernel_pre_gate->fallback_work_known &&
					kernel_use_gate.fallback_work_reduction >= 0.90;
				if (query_kernel != nullptr && !preserve_kernel_for_witness_retry &&
					((!kernel_enabled_for_search && !use_fallback_only_kernel) ||
						 kernel_infeasible_certificate ||
						 (!use_kernel_graph && !use_fallback_only_kernel &&
						  query_kernel->complete)))
				{
					if (!kernel_direct_feasible_certificate)
					{
						vector<unsigned long long>().swap(query_kernel->final_membership);
						vector<ui>().swap(query_kernel->kernel_vertices);
						query_kernel->membership_materialized = false;
					}
				}
				if (kernel_infeasible_certificate)
				{
					// The exact kernel contains every feasible target-k community.
					// Fewer than max(L,k+1) retained vertices therefore proves this
					// target infeasible for every size in [L,U]. The next lower k
					// must restart at its smallest legal size, not only at U:
					// a connected k-community need not extend to size U.
					k_max--;
					S = max(1, LB_size - k_max);
					if (k_min >= k_max)
						continue;
					initial_size = (S > static_cast<ui>(LB_size - 1)) ? S : LB_size - 1;
					initial_size = (initial_size > S + k_min) ? initial_size : S + k_min;
					give_ininital_feasible_sol(initial_size);
					old_size = feasible_solution.size();
					continue;
				}
				// An exact-h certificate closes only the current cardinality.  An
				// h-1 witness proves target_k-1 only after every target_k trial has
				// been closed, which is true here precisely at the final size U.
				const bool target_demotion_complete_branch =
					cardinality_spectrum.exact_size == (ui)UB_size;
				const bool target_demotion_opportunity =
					observed_cardinality_certificate != CARDINALITY_SPECTRUM_AQER_NONE &&
					target_demotion_complete_branch &&
					S + k_max - 1 >= static_cast<ui>(LB_size) &&
					feasible_solution.size() < (size_t)(S + k_max - 1);
				if (observed_cardinality_certificate != CARDINALITY_SPECTRUM_AQER_NONE)
				{

					fflush(stdout);
				}
				const bool target_demotion_probe_active =
					(target_demotion_opportunity) &&
					cardinality_certificate != CARDINALITY_SPECTRUM_AQER_NONE;

				if (cardinality_certificate != CARDINALITY_SPECTRUM_AQER_NONE &&
					!target_demotion_probe_active)
				{
					{
						// A certificate without a constructed k-1 witness is not a
						// production commit in strict witness-only mode.  Re-enter the
						// same (S,k) state with AQER disabled so fallback/CABP follows
						// exactly the established path.
						aqer_witness_commit_misses.insert(
							std::make_pair(S, k_max));

						fflush(stdout);
						continue;
					}
					// This certificate applies only to the current exact order
					// h=S+k.  Advance exactly as an exhausted original trial; do
					// not discard the remaining cardinalities for the same k.

				}
				if (kernel_direct_feasible_certificate)
				{
					// After support filtering and k-peeling, the final q-component is
					// connected, contains q and has minimum degree at least target k.
					// When its size is already inside [L,U], it is an exact witness.
					feasible_solution = query_kernel->kernel_vertices;
					auto query_it = std::find(feasible_solution.begin(),
						feasible_solution.end(), (ui)query_vertex);
					if (query_it == feasible_solution.end())
					{

						vector<ui>().swap(feasible_solution);
						give_ininital_feasible_sol(initial_size);
					}
					else
					{
						std::iter_swap(feasible_solution.begin(), query_it);
						k_min = k_max;
						update_feasible_solution( out_mapping,
							record_solution, find_feasible_solution);
						find_optimal_solution = true;

						break;
					}
				}

				vector<ui> matrix_kernel_ids;
				vector<pair<ui, ui>> matrix_kernel_edges;
				const vector<ui> *trial_matrix_ids = &ids;
				const vector<pair<ui, ui>> *trial_matrix_edges = &vp;
				if (use_kernel_graph)
				{
					build_matrix_kernel_graph(*query_kernel, ids, vp,
						matrix_kernel_ids, matrix_kernel_edges);
					assert(!matrix_kernel_ids.empty() && matrix_kernel_ids[0] == static_cast<ui>(query_vertex));
					trial_matrix_ids = &matrix_kernel_ids;
					trial_matrix_edges = &matrix_kernel_edges;
				}
				if (!matrix_graph_prepared || matrix_graph_is_kernel != use_kernel_graph ||
					(use_kernel_graph && matrix_graph_target != (ui)k_max))
				{

					MBBPS_solver_m.load_graph((ui)trial_matrix_ids->size(), *trial_matrix_edges);

					matrix_graph_prepared = true;
					matrix_graph_is_kernel = use_kernel_graph;
					matrix_graph_target = use_kernel_graph ? (ui)k_max : INVALID_VERTEX;
				}

				old_size = feasible_solution.size();
				vector<ui> target_demotion_incumbent_snapshot;
				if (target_demotion_probe_active)
					target_demotion_incumbent_snapshot = feasible_solution;
				const int search_target_size = target_demotion_probe_active
					? S + k_max - 1 : S + k_max;
				UB = (UB_size > search_target_size) ? search_target_size : UB_size;

				const ui trial_incumbent_bound_size = feasible_solution.size();

				const unsigned long long certificate_skipped_nodes =
					target_demotion_probe_active
						? std::max(1ull,
							trial_matrix_ids->size() > trial_incumbent_bound_size
								? (unsigned long long)trial_matrix_ids->size() -
									trial_incumbent_bound_size
								: 1ull)
						: 0ull;

				const unsigned long long target_demotion_matrix_node_limit =
					target_demotion_probe_active
						? ((saturating_add_ull(certificate_skipped_nodes,
								aqer_matrix_work.bb_node_credit)))
						: 0ull;

				// A small exact kernel can still have an expensive high-slack
				// proof tree. Keep the validated small-range trajectory unchanged;
				// for large-range trials, bound only the optional kernel attempt.
				// Exhaustion below restores the incumbent and retries the complete
				// local graph without a node limit; it is never an infeasibility proof.
				const bool large_slack_kernel_guard = (LB_size > 15) && S >= static_cast<ui>(k_max);
				const unsigned long long kernel_guard_node_limit =
					use_kernel_graph && !target_demotion_probe_active &&
					((large_slack_kernel_guard))
						? 4096ull : 0ull;
                bool wide_range_neighbor_trial = (!wide_range_neighbor_probe_attempted) &&
                    !use_kernel_graph && !use_fallback_kernel_graph &&
                    !target_demotion_probe_active && LB_size >= 20 && UB_size <= 28 &&
                    UB_size - LB_size <= 2 && LB_size >= 2 * k_max && k_max <= 16 &&
                    ((UB_size > 24 && ids.size() > 1024u && ids.size() <= 2048u) ||
                     (k_max >= 9 && ids.size() >= (size_t)LB_size && ids.size() <= 1024u)) &&
                    n >= 4096u &&
                    16ull * n <= 64ull * 1024ull * 1024ull;
                if (wide_range_neighbor_trial) {
                    ui eligible = 0;
                    if (query_graph_deferred) {
                        for(ept e=saved_pstart[original_q_idx];e<saved_pstart[original_q_idx+1];++e){
                            const ui v=old2new[saved_edges[e]];
                            if(v!=INVALID_VERTEX && core[v]>=(ui)k_max)++eligible;
                        }
                    } else {
                        for(ept e=pstart[query_vertex];e<pstart[query_vertex+1];++e)
                            if(core[edges[e]]>=(ui)k_max)++eligible;
                    }
                    wide_range_neighbor_trial = eligible == (ui)k_max && eligible <= 16u;
                }
                // Keep every existing capped/kernel route unchanged. A compact
                // high-slack small window can try the same exact certificate
                // after an unrestricted matrix search has done real branch work.
                bool small_range_neighbor_trial = (!wide_range_neighbor_probe_attempted) &&
                    !use_kernel_graph && !use_fallback_kernel_graph &&
                    !target_demotion_probe_active && target_demotion_matrix_node_limit == static_cast<unsigned long long>(0) &&
                    kernel_guard_node_limit == static_cast<unsigned long long>(0) && LB_size >= 12 && UB_size <= 18 &&
                    UB_size - LB_size == 3 && LB_size >= 2 * k_max &&
                    k_max >= 4 && k_max <= 8 && ids.size() >= 64u && ids.size() <= 512u &&
                    n >= 4096u && 16ull * n <= 64ull * 1024ull * 1024ull;
                if (small_range_neighbor_trial) {
                    ui eligible = 0;
                    if(query_graph_deferred){
                        for(ept e=saved_pstart[original_q_idx];e<saved_pstart[original_q_idx+1];++e){
                            const ui v=old2new[saved_edges[e]];
                            if(v!=INVALID_VERTEX && core[v]>=(ui)k_max)++eligible;
                        }
                    }else{
                        for(ept e=pstart[query_vertex];e<pstart[query_vertex+1];++e)
                            if(core[edges[e]]>=(ui)k_max)++eligible;
                    }
                    // U<=15 already has a fast small-partition fallback. Leave
                    // it intact; only the wider missing partition uses this route.
                    small_range_neighbor_trial = eligible >= (ui)k_max &&
                        (UB_size <= 15 ? (eligible > 16u && eligible <= 24u) : eligible <= 16u);
                }
                const bool matrix_neighbor_trial = wide_range_neighbor_trial || small_range_neighbor_trial;
                vector<ui> wide_range_incumbent_snapshot;
                if(matrix_neighbor_trial)wide_range_incumbent_snapshot=feasible_solution;
				const unsigned long long applied_matrix_node_limit =
					target_demotion_matrix_node_limit != static_cast<unsigned long long>(0)
						? target_demotion_matrix_node_limit : kernel_guard_node_limit;
				vector<ui> kernel_guard_incumbent_snapshot;
				if (kernel_guard_node_limit != static_cast<unsigned long long>(0))
					kernel_guard_incumbent_snapshot = feasible_solution;
				// The slack-relaxation witness is the production proof we want.  Do
				// not first spend a second bounded search on the older h-1 target:
				// its successful cases showed no material aggregate benefit, while
				// every miss duplicated root initialization and B&B work.
				const bool direct_slack_relaxation_probe =
					(target_demotion_probe_active);
				if (target_demotion_probe_active)
				{

					fflush(stdout);
				}

				assert(S + k_max <= static_cast<ui>(UB_size) && S + k_max >= static_cast<ui>(LB_size));
				MBBPS_solver_m.set_search_node_limit(matrix_neighbor_trial ? 4096ull : applied_matrix_node_limit);

				if (!direct_slack_relaxation_probe)
					MBBPS_solver_m.find_feasible(S, UB, feasible_solution, true);
                if(matrix_neighbor_trial && feasible_solution.size() < (size_t)search_target_size){
                    wide_range_neighbor_probe_attempted=true;
                    const bool warmup_exhausted=MBBPS_solver_m.was_search_node_limit_exhausted();
                    if(query_graph_deferred){
                        materialize_query_csr_from_mapping(saved_n,n,old2new,saved_pstart,
                            readonly_source_edges,readonly_source_core_ordered,pstart,edges,m,owns_query_graph);
                        query_graph_deferred=false;
                    }
                    bool exact_resolved=true;
                    int certified_k=k_min;
                    vector<ui> certified_solution;
                    unsigned long long nodes_left=250000ull,edges_left=250000000ull;
                    unsigned long long small_retry_nodes_left=12000000ull,
                        small_retry_edges_left=8000000000ull;
                    for(int target=k_max;target>k_min;--target){
                        arc_forced_neighbor::Probe<ept> probe(n,pstart,edges,core,
                            (ui)query_vertex,LB_size,UB_size,target,
                                small_range_neighbor_trial ? 250000ull : nodes_left,
                                small_range_neighbor_trial ? 250000000ull : edges_left,true,
                                small_range_neighbor_trial ? 62u : 36u);
                        arc_forced_neighbor::Result certificate=probe.run();
                        if(small_range_neighbor_trial && certificate.verdict==arc_forced_neighbor::Unknown &&
                                small_retry_nodes_left && small_retry_edges_left){
                            arc_forced_neighbor::Probe<ept> retry(n,pstart,edges,core,
                                (ui)query_vertex,LB_size,UB_size,target,
                                small_retry_nodes_left,small_retry_edges_left,true,1u);
                            certificate=retry.run();
                            small_retry_nodes_left=certificate.nodes>=small_retry_nodes_left
                                ? 0ull : small_retry_nodes_left-certificate.nodes;
                            small_retry_edges_left=certificate.edge_visits>=small_retry_edges_left
                                ? 0ull : small_retry_edges_left-certificate.edge_visits;

                        }
                        nodes_left=certificate.nodes>=nodes_left?0ull:nodes_left-certificate.nodes;
                        edges_left=certificate.edge_visits>=edges_left?0ull:edges_left-certificate.edge_visits;

                        if(certificate.verdict==arc_forced_neighbor::Unknown){exact_resolved=false;break;}
                        if(certificate.verdict==arc_forced_neighbor::Found){
                            if(!certify_community(certificate.witness,(ui)query_vertex,LB_size,UB_size,
                                    n,pstart,edges,certified_k) || certified_k<target || certified_k>k_max)
                                throw std::logic_error("wide-range witness failed certificate");
                            certified_solution=certificate.witness;break;
                        }
                    }
                    if(exact_resolved){
                        if(!certified_solution.empty()){
                            record_solution=certified_solution;for(ui &v:record_solution)v=out_mapping[v];
                            find_feasible_solution=true;
                        }
                        k_min=k_max=certified_k;find_optimal_solution=true;

                        break;
                    }
                    // Unknown is never an infeasibility proof. Restore the exact
                    // pre-trial incumbent and resume the original complete path.
                    if(warmup_exhausted){
                        feasible_solution.swap(wide_range_incumbent_snapshot);
                        MBBPS_solver_m.load_graph((ui)trial_matrix_ids->size(),*trial_matrix_edges);
                        MBBPS_solver_m.set_search_node_limit(applied_matrix_node_limit);
                        MBBPS_solver_m.find_feasible(S,UB,feasible_solution,true);
                    }
                }

				const bool matrix_probe_budget_exhausted = target_demotion_probe_active &&
					!direct_slack_relaxation_probe &&
					MBBPS_solver_m.was_search_node_limit_exhausted();
				const bool kernel_guard_exhausted = kernel_guard_node_limit != static_cast<unsigned long long>(0) &&
					MBBPS_solver_m.was_search_node_limit_exhausted();
				const unsigned long long matrix_probe_nodes = target_demotion_probe_active
					&& !direct_slack_relaxation_probe
					? MBBPS_solver_m.get_search_nodes_visited() : 0ull;
				if ((target_demotion_probe_active) && (!direct_slack_relaxation_probe))
					aqer_matrix_work.bb_node_credit = matrix_probe_budget_exhausted ? 0ull :
						(target_demotion_matrix_node_limit > matrix_probe_nodes
							? target_demotion_matrix_node_limit - matrix_probe_nodes : 0ull);
				MBBPS_solver_m.set_search_node_limit(0ull);
				if (kernel_guard_exhausted)
				{
					// A bounded kernel miss is not a proof. Restore the exact
					// pre-kernel incumbent and execute the established full-local trial.
					feasible_solution.swap(kernel_guard_incumbent_snapshot);
					MBBPS_solver_m.load_graph((ui)ids.size(), vp);
					trial_matrix_ids = &ids;
					trial_matrix_edges = &vp;
					matrix_graph_prepared = true;
					matrix_graph_is_kernel = false;
					matrix_graph_target = INVALID_VERTEX;
					MBBPS_solver_m.find_feasible(S, UB, feasible_solution, true);

				}

				if (target_demotion_probe_active && !direct_slack_relaxation_probe)
				{

					fflush(stdout);
				}
				if (direct_slack_relaxation_probe)
				{
					// The exact-k certificate closes size U for target k.  On the
					// same (usually much smaller) exact-k kernel, an (S+1)-plex of
					// size U is a connected target-(k-1) witness.  Finding one proves
					// optimality immediately; a bounded miss changes no decision.
					vector<ui> slack_probe_snapshot = feasible_solution;

					MBBPS_solver_m.set_search_node_limit(
						target_demotion_matrix_node_limit);

					MBBPS_solver_m.find_feasible(S + 1, UB_size,
						feasible_solution, true);

					const bool slack_probe_budget_exhausted =
						MBBPS_solver_m.was_search_node_limit_exhausted();
					const unsigned long long slack_probe_nodes =
						MBBPS_solver_m.get_search_nodes_visited();
					{ aqer_matrix_work.bb_node_credit = slack_probe_budget_exhausted ? 0ull :
							(target_demotion_matrix_node_limit > slack_probe_nodes
								? target_demotion_matrix_node_limit - slack_probe_nodes : 0ull); }

					MBBPS_solver_m.set_search_node_limit(0ull);
					const bool slack_witness =
						feasible_solution.size() >= (size_t)UB_size;

					fflush(stdout);
					if (slack_witness)
					{
						for (ui &v : feasible_solution)
							v = (*trial_matrix_ids)[v];
						k_min = k_max = k_max - 1;
						update_feasible_solution( out_mapping,
							record_solution, find_feasible_solution);
						find_optimal_solution = true;

						break;
					}
					feasible_solution.swap(slack_probe_snapshot);
					{
						// Neither Matrix certificate-guided probe produced a proof.
						// Restore the exact pre-probe state and run the established trial;
						// do not perturb fallback/CABP calibration on a non-commit path.
						feasible_solution.swap(target_demotion_incumbent_snapshot);
						aqer_witness_commit_misses.insert(
							std::make_pair(S, k_max));

						fflush(stdout);
						continue;
					}
				}

				if (!target_demotion_probe_active && feasible_solution.size() >= static_cast<size_t>(LB_size) && feasible_solution.size() != k_min + S)
				{
					if (feasible_solution.size() > old_size)
					{
						old_size = feasible_solution.size();
						for (ui j = 0; j < feasible_solution.size(); j++)
							feasible_solution[j] = (*trial_matrix_ids)[feasible_solution[j]];
					}

					if (feasible_solution.size() >= k_max + S)
					{
						k_min = k_max;
						update_feasible_solution( out_mapping, record_solution, find_feasible_solution);
						find_optimal_solution = true;
						printf("We found the optimal community with the parameter S of feasible_solution is S= %d\n", S);
						break;
					}

					int t_size = feasible_solution.size() > static_cast<size_t>(UB_size) ? UB_size : feasible_solution.size();
					int t_k_min = t_size - S, old_k_min = k_min;
					k_min = (k_min < t_k_min) ? t_k_min : k_min;
					if (k_min > old_k_min)
						update_feasible_solution( out_mapping, record_solution, find_feasible_solution);
				}
				if (target_demotion_probe_active && feasible_solution.size() > old_size)
				{
					for (ui j = 0; j < feasible_solution.size(); ++j)
						feasible_solution[j] = (*trial_matrix_ids)[feasible_solution[j]];
				}
				if (target_demotion_probe_active &&
					feasible_solution.size() >= (size_t)search_target_size)
				{
					// Earlier, smaller exact-h trials for target_k have already been
					// exhausted, while the current certificate proves target_k at h
					// impossible.  An h-1 witness therefore establishes target_k-1.
					k_min = k_max = k_max - 1;
					update_feasible_solution( out_mapping,
						record_solution, find_feasible_solution);
					find_optimal_solution = true;

					break;
				}

				bool fallback_probe_budget_exhausted = false;
				unsigned long long fallback_probe_nodes = 0;
				unsigned long long target_demotion_fallback_node_limit = 0;

				if (n > feasible_solution.size() && feasible_solution.size() < 2 * S - 2 && 2 * S - 2 >= static_cast<ui>(LB_size))
				{

					if (query_graph_deferred && !use_fallback_kernel_graph)
					{
						materialize_query_csr_from_mapping(saved_n, n, old2new,
							 saved_pstart, readonly_source_edges, readonly_source_core_ordered,
						 pstart, edges, m,
							 owns_query_graph);
						query_graph_deferred = false;
					}
					vector<ui> fallback_kernel_ids;
					vector<pair<ui, ui>> fallback_kernel_edges;
					ui fallback_query_vertex = (ui)query_vertex;
					if (use_fallback_kernel_graph)
					{
						QueryGraphView kernel_graph = {
							n, m, pstart, edges, query_graph_deferred,
							out_mapping, old2new, saved_pstart, readonly_source_edges,
				readonly_source_core_ordered, query_graph_min_degree_lower_bound,
							query_graph_directed_edge_lower_bound};
						build_fallback_kernel_graph(kernel_graph, *query_kernel,
							fallback_kernel_ids, fallback_kernel_edges,
							(ui)query_vertex, fallback_query_vertex);
						assert(fallback_query_vertex != INVALID_VERTEX);
					}
					if (target_demotion_probe_active)
					{
						const unsigned long long fallback_active_candidates =
							use_fallback_kernel_graph ? fallback_kernel_ids.size() : (unsigned long long)n;
						const unsigned long long fallback_skipped_nodes = std::max(1ull,
							fallback_active_candidates > feasible_solution.size()
								? fallback_active_candidates - feasible_solution.size() : 1ull);
						target_demotion_fallback_node_limit = (saturating_add_ull(fallback_skipped_nodes,
								aqer_fallback_work.bb_node_credit));
					}
					MBBPS MBBPS_solver;

					MBBPS_solver.set_adaptive_triple_capacity_bound(256);
					MBBPS_solver.set_automatic_work_ledger();

					// A compact Matrix state that is large enough for the requested
					// community yet still needs the full-graph fallback marks a sharp
					// backend discontinuity.  In high-S searches, successful budget RR1
					// passes are then worth scheduling more densely.  The 256-vertex cap
					// is a representation boundary, not a dataset/query special case.

					MBBPS_solver.set_work_adaptive_initial_totals(
						work_adaptive_query_work_so_far,
						adaptive_budget_query_removed_so_far,
						work_adaptive_query_search_credit_so_far,
						work_adaptive_query_removal_benefit_so_far,
						work_adaptive_query_run_count,
						work_adaptive_query_probe_interval);

					MBBPS_solver.set_search_node_limit(
						target_demotion_fallback_node_limit);

					MBBPS_solver.allocateMemory(use_fallback_kernel_graph
						? (ui)fallback_kernel_ids.size() : n);
					UB = (2 * S - 2 < UB) ? 2 * S - 2 : UB;
					if (use_fallback_kernel_graph)
						MBBPS_solver.load_graph((ui)fallback_kernel_ids.size(), fallback_kernel_edges);
					else
						MBBPS_solver.load_graph(n, pstart, pstart + 1, edges);
					const ui fallback_incumbent_size = feasible_solution.size();
                    // Preserve quick fallback searches. A bounded warm-up only
                    // triggers the completion probe after actual branch work.
                    bool expanded_neighbor_admission = false;
                    bool nonbinding_lower_neighbor_admission = false;
                    bool forced_neighbor_hub_order = false;
                    bool wide_neighbor_admission = false;
                    bool compact_upper_order = false;
                    bool large_window_neighbor_admission = false;
                    bool large_window_newly_admitted = false;
                    bool large_window_nearly_forced = false;
                    bool deferred_neighbor_eligible =
                        (!deferred_neighbor_probe_attempted) &&
                        !target_demotion_probe_active &&
                        UB_size <= 28 && k_max <= 16 &&
                        (UB_size <= 24 || k_max <= 8 ||
                          (LB_size >= 20 && UB_size - LB_size <= 2 && ids.size() <= 1024u &&
                           !use_fallback_kernel_graph)) &&
                        ids.size() <= 4096u && n >= 4096u &&
                        12ull * n <= 64ull * 1024ull * 1024ull;
                    if (deferred_neighbor_eligible) {
                        ui eligible_neighbors = 0;
                        if (query_graph_deferred) {
                            for (ept e = saved_pstart[original_q_idx]; e < saved_pstart[original_q_idx + 1]; ++e) {
                                const ui local = old2new[saved_edges[e]];
                                if (local != INVALID_VERTEX && core[local] >= (ui)k_max)
                                    ++eligible_neighbors;
                            }
                        } else {
                            for (ept e = pstart[query_vertex]; e < pstart[query_vertex + 1]; ++e)
                                if (core[edges[e]] >= (ui)k_max) ++eligible_neighbors;
                        }
                        // When q forces every eligible neighbor in a tiny matrix,
                        // visit high-degree candidates first in binary branching.
                        forced_neighbor_hub_order = UB_size > 24 &&
                            ids.size() <= 16u && eligible_neighbors == (ui)k_max;
                        // Bound the initial membership partition, rather than
                        // paying for a broad probe on a quick fallback query.
                        unsigned long long initial_partitions = 257ull;
                        if (eligible_neighbors <= 16u) {
                            initial_partitions = 0ull;
                            unsigned long long choices = 1ull;
                            for (ui take = 0; take <= eligible_neighbors; ++take) {
                                if (take >= (ui)k_max && take + 1u <= (ui)UB_size)
                                    initial_partitions += choices;
                                if (take < eligible_neighbors)
                                    choices = choices * (eligible_neighbors - take) / (take + 1u);
                            }
                        }
                        // High slack is where a cheap local trial can hand
                        // off to a much larger proof. A larger packed matrix
                        // is admitted only when q forces every eligible neighbor.
                        deferred_neighbor_eligible = initial_partitions <= 256ull &&
                            (LB_size >= 2 * k_max ||
                             (ids.size() > 512u && eligible_neighbors == (ui)k_max));
                        // Permit one bounded trial on compact, high-slack
                        // kernels with a moderately wider initial partition.
                        expanded_neighbor_admission = !deferred_neighbor_eligible &&
                            LB_size >= 20 && LB_size >= 2 * k_max &&
                            ids.size() <= 256u && eligible_neighbors <= 16u &&
                            initial_partitions <= 4096ull;
                        // A compact small-range proof can enumerate all at most
                        // 2^16 memberships under the existing shared probe budget.
                        const bool small_range_proof_admission = !deferred_neighbor_eligible &&
                            UB_size <= 15 && LB_size >= 2 * k_max &&
                            ids.size() <= 512u && eligible_neighbors <= 16u &&
                            initial_partitions <= 65536ull;
                        // With L <= k+1 the lower bound needs no padding. If q
                        // has only k or k+1 eligible neighbors, its initial
                        // membership partition has at most k+2 <= 10 branches.
                        // Admit this compact low-L gap after the same warm-up;
                        // the exact probe and its existing fallback stay unchanged.
                        nonbinding_lower_neighbor_admission =
                            !deferred_neighbor_eligible &&
                            UB_size >= 15 && UB_size <= 18 &&
                            LB_size <= k_max + 1 && k_max <= 8 &&
                            ids.size() <= 256u &&
                            eligible_neighbors >= (ui)k_max &&
                            eligible_neighbors <= (ui)k_max + 1u;
                        // A narrow size window can still have more than 16
                        // query neighbors. Binary branching keeps the exact trial
                        // bounded without enumerating the full initial partition.
                        wide_neighbor_admission = !deferred_neighbor_eligible &&
                            !expanded_neighbor_admission && !small_range_proof_admission &&
                            !nonbinding_lower_neighbor_admission &&
                            LB_size >= 18 && UB_size <= 24 && UB_size - LB_size <= 2 &&
                            LB_size >= 2 * k_max && ids.size() <= 256u &&
                            (eligible_neighbors > 16u || initial_partitions <= 4096ull) &&
                            eligible_neighbors <= 32u;
                        // In a compact kernel where query neighbors are forced,
                        // try the largest tight-constraint membership first. All
                        // memberships and the existing resource limits remain.
                        compact_upper_order = LB_size >= 20 && UB_size <= 24 &&
                            UB_size - LB_size <= 2 && ids.size() <= 64u &&
                            eligible_neighbors == (ui)k_max;
                        large_window_neighbor_admission = !use_fallback_kernel_graph &&
                            LB_size >= 20 && UB_size <= 28 &&
                            UB_size - LB_size <= 2 && LB_size >= 2 * k_max &&
                            ids.size() <= 1024u && eligible_neighbors <= 16u &&
                            initial_partitions <= 65536ull &&
                            16ull * n <= 64ull * 1024ull * 1024ull;
                        large_window_nearly_forced = large_window_neighbor_admission &&
                            eligible_neighbors <= (ui)k_max + 1u;
                        large_window_newly_admitted = (large_window_neighbor_admission &&
                            !(deferred_neighbor_eligible || expanded_neighbor_admission ||
                              small_range_proof_admission || nonbinding_lower_neighbor_admission ||
                              wide_neighbor_admission)) || (large_window_neighbor_admission &&
                              UB_size > 24 && k_max > 8);
                        deferred_neighbor_eligible =
                            deferred_neighbor_eligible || expanded_neighbor_admission ||
                            small_range_proof_admission || nonbinding_lower_neighbor_admission ||
                            wide_neighbor_admission || large_window_neighbor_admission;
                    }
                    if (deferred_neighbor_eligible)
                        MBBPS_solver.set_search_node_limit(large_window_newly_admitted ?
                            (large_window_nearly_forced ? 4ull : 32ull) :
                            ((UB_size > 24 || expanded_neighbor_admission ||
                              wide_neighbor_admission || compact_upper_order ||
                              (LB_size >= 20 && k_max <= 8 &&
                               ids.size() > 256u && ids.size() <= 512u)) ? 4ull : 32ull));
                    MBBPS_solver.find_feasible(S, UB, feasible_solution, false,
                        fallback_query_vertex, search_target_size);
                    if (deferred_neighbor_eligible &&
                        MBBPS_solver.was_search_node_limit_exhausted() &&
                        feasible_solution.size() < (size_t)search_target_size) {
                        deferred_neighbor_probe_attempted = true;
                        if (query_graph_deferred) {
                            materialize_query_csr_from_mapping(saved_n, n, old2new,
                                saved_pstart, readonly_source_edges, readonly_source_core_ordered,
                                pstart, edges, m, owns_query_graph);
                            query_graph_deferred = false;
                        }
                        bool exact_resolved = true;
                        int certified_k = k_min;
                        int certified_upper = k_max;
                        vector<ui> certified_solution;
                        unsigned long long nodes_left = 250000ull;
                        unsigned long long edges_left = 250000000ull;
                        unsigned long long retry_nodes_left = 250000ull;
                        unsigned long long retry_edges_left = 250000000ull;
                        for (int target = k_max; target > k_min; --target) {
                            Timer completion_timer;
                            arc_forced_neighbor::Probe<ept> probe(n, pstart, edges, core,
                                (ui)query_vertex, LB_size, UB_size, target,
                                nodes_left, edges_left, true, large_window_newly_admitted
                                    ? (certified_upper < k_max ? 34u : 36u)
                                    : (forced_neighbor_hub_order ? 8u :
                                      (compact_upper_order ? 4u :
                                       ((expanded_neighbor_admission || wide_neighbor_admission ||
                                         (nonbinding_lower_neighbor_admission && certified_upper < k_max))
                                            ? 1u : (UB_size > 24 ? 2u : 0u)))));
                            arc_forced_neighbor::Result certificate = probe.run();

                            nodes_left = certificate.nodes >= nodes_left
                                ? 0ull : nodes_left - certificate.nodes;
                            edges_left = certificate.edge_visits >= edges_left
                                ? 0ull : edges_left - certificate.edge_visits;
                            if (large_window_neighbor_admission &&
                                certificate.verdict == arc_forced_neighbor::Unknown) {
                                for (unsigned order : {62u,36u}) {
                                    arc_forced_neighbor::Probe<ept> retry(n,pstart,edges,core,
                                        (ui)query_vertex,LB_size,UB_size,target,
                                        50000ull,50000000ull,true,order);
                                    certificate=retry.run();

                                    if(certificate.verdict != arc_forced_neighbor::Unknown)break;
                                }
                            }
                            // A bounded second ordering is used only after
                            // the existing exact trial returns Unknown. It changes
                            // traversal order, not the feasible set or pruning.
                            if (certificate.verdict == arc_forced_neighbor::Unknown &&
                                LB_size >= 20 && retry_nodes_left && retry_edges_left) {
                                arc_forced_neighbor::Probe<ept> retry(n, pstart, edges, core,
                                    (ui)query_vertex, LB_size, UB_size, target,
                                    retry_nodes_left, retry_edges_left, true, 7u);
                                certificate = retry.run();
                                retry_nodes_left = certificate.nodes >= retry_nodes_left
                                    ? 0ull : retry_nodes_left - certificate.nodes;
                                retry_edges_left = certificate.edge_visits >= retry_edges_left
                                    ? 0ull : retry_edges_left - certificate.edge_visits;

                            }
                            // A higher target was already disproved exactly.
                            // At the remaining certified upper bound, one bounded
                            // large-membership ordering can find a witness without
                            // first proving every smaller cardinality infeasible.
                            if (certificate.verdict == arc_forced_neighbor::Unknown &&
                                certified_upper < k_max && target == certified_upper &&
                                LB_size >= 18 && UB_size <= 24 && UB_size - LB_size <= 2 &&
                                ids.size() <= 512u) {
                                arc_forced_neighbor::Probe<ept> retry(n, pstart, edges, core,
                                    (ui)query_vertex, LB_size, UB_size, target,
                                    1000000ull, 750000000ull, true, 4u);
                                certificate = retry.run();

                            }
                            if (large_window_neighbor_admission &&
                                certificate.verdict == arc_forced_neighbor::Unknown) {
                                arc_forced_neighbor::Probe<ept> retry(n,pstart,edges,core,
                                    (ui)query_vertex,LB_size,UB_size,target,
                                    250000ull,250000000ull,true,36u);
                                certificate=retry.run();

                            }

                            fflush(stdout);
                            if (certificate.verdict == arc_forced_neighbor::Unknown) {
                                exact_resolved = false;
                                break;
                            }
                            if (certificate.verdict == arc_forced_neighbor::Infeasible)
                                certified_upper = target - 1;
                            if (certificate.verdict == arc_forced_neighbor::Found) {
                                if (!certify_community(certificate.witness, (ui)query_vertex,
                                        LB_size, UB_size, n, pstart, edges, certified_k) ||
                                    certified_k < target || certified_k > k_max)
                                    throw std::logic_error("deferred-neighbor witness failed certificate");
                                certified_solution = certificate.witness;
                                break;
                            }
                        }
                        if (exact_resolved) {
                            if (!certified_solution.empty()) {
                                record_solution = certified_solution;
                                for (ui &v : record_solution) v = out_mapping[v];
                                find_feasible_solution = true;
                            }
                            k_min = k_max = certified_k;
                            find_optimal_solution = true;

                            break;
                        }
                        // Unknown at a lower target does not invalidate an exact
                        // infeasibility proof already obtained at a higher target.
                        if ((UB_size <= 15 || nonbinding_lower_neighbor_admission) &&
                            certified_upper < k_max) {
                            if (certified_upper < k_min)
                                throw std::logic_error("probe upper bound contradicts incumbent");
                            k_max = certified_upper;
                            S = max(1, LB_size - k_max);

                            if (k_min >= k_max) continue;
                            initial_size = (S > static_cast<ui>(LB_size - 1)) ? S : LB_size - 1;
                            initial_size = (initial_size > S + k_min) ? initial_size : S + k_min;
                            give_ininital_feasible_sol(initial_size);
                            old_size = feasible_solution.size();
                            continue;
                        }
                        // A capped search is never a proof. Reload the immutable
                        // query CSR after the warm-up exception and rerun the
                        // original unrestricted fallback if the probe is Unknown.
                        MBBPS_solver.set_search_node_limit(0ull);
                        if (use_fallback_kernel_graph)
                            MBBPS_solver.load_graph((ui)fallback_kernel_ids.size(), fallback_kernel_edges);
                        else
                            MBBPS_solver.load_graph(n, pstart, pstart + 1, edges);

                        MBBPS_solver.find_feasible(S, UB, feasible_solution, false,
                            fallback_query_vertex, search_target_size);
                    }

					if (use_fallback_kernel_graph && feasible_solution.size() > fallback_incumbent_size)
						for (ui &v : feasible_solution)
							v = fallback_kernel_ids[v];

					const MBBPS::SearchStats &fallback_stats = MBBPS_solver.get_stats();
					fallback_probe_budget_exhausted =
						target_demotion_probe_active &&
						MBBPS_solver.was_search_node_limit_exhausted();
					fallback_probe_nodes =
						target_demotion_probe_active
							? MBBPS_solver.get_search_nodes_visited() : 0ull;
					if (target_demotion_probe_active)
						aqer_fallback_work.bb_node_credit = fallback_probe_budget_exhausted ? 0ull :
							(target_demotion_fallback_node_limit > fallback_probe_nodes
								? target_demotion_fallback_node_limit - fallback_probe_nodes : 0ull);

					adaptive_budget_query_removed_so_far += fallback_stats.adaptive_budget_removed_vertices_so_far;
					work_adaptive_query_work_so_far += fallback_stats.work_adaptive_work_ops;
					work_adaptive_query_search_credit_so_far += fallback_stats.work_adaptive_search_credit;
					work_adaptive_query_removal_benefit_so_far +=
						fallback_stats.work_adaptive_removed_credit;
					work_adaptive_query_run_count += fallback_stats.adaptive_budget_run_cnt;
					work_adaptive_query_probe_interval = fallback_stats.work_adaptive_probe_interval;

					if (target_demotion_probe_active)
					{

						fflush(stdout);
					}

					if (feasible_solution.size() > 2 * S - 2)
						printf("!!! WA in ARC-SCS!\n");

					if (target_demotion_probe_active)
					{
						if (feasible_solution.size() >= (size_t)search_target_size)
						{
							k_min = k_max = k_max - 1;
							update_feasible_solution( out_mapping,
								record_solution, find_feasible_solution);
							find_optimal_solution = true;

							break;
						}
					}

					if (!target_demotion_probe_active && feasible_solution.size() >= static_cast<size_t>(LB_size) && feasible_solution.size() != k_min + S)
					{
							// A target-minus-one witness is only a lower bound until
							// the final size trial closes the entire allowed interval.
							// AQER may skip earlier k trials, so an incumbent found
							// here must not be mistaken for a global optimality proof.
							if (feasible_solution.size() >= k_max + S ||
								(S + k_max == static_cast<ui>(UB_size) &&
								 feasible_solution.size() >= k_max + S - 1))
						{
							if (feasible_solution.size() >= k_max + S)
								k_min = k_max;
							else
								k_min = k_max = k_max - 1;
							assert(feasible_solution.size() >= k_max + S - 1);
							update_feasible_solution( out_mapping, record_solution, find_feasible_solution);
							find_optimal_solution = true;
							printf("We found the optimal community with the parameter of feasible_solution is S= %d\n", S);
							break;
						}

						int t_size = feasible_solution.size() > static_cast<size_t>(UB_size) ? UB_size : feasible_solution.size();
						int t_k_min = t_size - S, old_k_min = k_min;
						k_min = (k_min < t_k_min) ? t_k_min : k_min;
						if (k_min > old_k_min)
							update_feasible_solution( out_mapping, record_solution, find_feasible_solution);
					}
				}
				if (target_demotion_probe_active)
				{

					const int harvested_k = std::min<int>(
						(int)feasible_solution.size(), UB_size) - S;
					if ((feasible_solution.size() >
							target_demotion_incumbent_snapshot.size()) && (harvested_k > k_min))
					{
						// Every partial result returned by the bounded probe is already a
						// valid connected S-plex containing q.  Even when it misses h-1,
						// its minimum degree |H|-S is a safe global lower bound.  Reuse
						// that work instead of discarding it before the next k trial.
						k_min = harvested_k;
						update_feasible_solution( out_mapping,
							record_solution, find_feasible_solution);

					}
					else
						feasible_solution.swap(target_demotion_incumbent_snapshot);

					fflush(stdout);
					{
						aqer_witness_commit_misses.insert(
							std::make_pair(S, k_max));

						fflush(stdout);
						continue;
					}
				}

				assert(feasible_solution.size() < static_cast<size_t>(UB_size));

				if (S + k_max >= static_cast<ui>(UB_size))
				{
					k_max--;
					S = max(1, LB_size - k_max);
				}
				else
					S++;
				assert(S < static_cast<ui>(UB_size));
				initial_size = (S > static_cast<ui>(LB_size - 1)) ? S : LB_size - 1;
				initial_size = (initial_size > S + k_min) ? initial_size : S + k_min;
				give_ininital_feasible_sol(initial_size);
				old_size = feasible_solution.size();
			}

			}
			}

		delete[] out_mapping;
	}
	delete heap;
	if (owns_core)
		delete[] core;
	if (owns_peel_sequence)
		delete[] peel_sequence;
	delete[] vis;
	delete[] degree;

	if (!find_optimal_solution && !find_feasible_solution)
		heu_is_optimal = true;
	const bool report_heuristic = heu_is_optimal || !find_feasible_solution;
	const vector<ui> &reported_solution = report_heuristic ? heu_solution : record_solution;
	int certified_degree = -1;
	bool valid_result = false;
	if (preserve_graph || shrink_old2new.empty())
		valid_result = certify_community(reported_solution, original_q_idx, LB_size, UB_size,
			saved_n, saved_pstart, saved_edges, certified_degree);
	else if (report_heuristic)
	{
		// The source CSR may have been compacted in the single-query path;
		// this witness was certified before that mutation.
		valid_result = !heu_solution.empty();
		certified_degree = witnessed_degree;
	}
	else
	{
		vector<ui> local_solution;
		for (ui v : reported_solution)
			local_solution.push_back(v < shrink_old2new.size() ? shrink_old2new[v] : INVALID_VERTEX);
		valid_result = certify_community(local_solution, (ui)query_vertex, LB_size, UB_size,
			n, pstart, edges, certified_degree);
	}
	valid_result = valid_result && certified_degree == k_min;
	long long total_us = total_timer.elapsed();

	last_query_result.total_us = total_us;
	last_query_result.opt_k = k_min;
	last_query_result.core_source = matrix_memory_guarded ? "OOM_GUARDED" : core_source;
	last_query_result.success = !matrix_memory_guarded && valid_result;
	if (last_query_result.success)
		last_query_result.vertices = reported_solution;
	if (!valid_result && !matrix_memory_guarded)
		printf("[CorrectnessError] invalid_community_or_degree claimed=%d certified=%d\n", k_min, certified_degree);
	printf("[Timing] total_us=%s index_load_excluded=%d\n",
		Utility::integer_to_string(total_us).c_str(), use_index ? 1 : 0);
	printf("[Result] status=%s min_degree=%d community_size=%zu\n",
		last_query_result.success ? "OPTIMAL" : "FAILED", k_min, reported_solution.size());
	printf("[Community] vertices:");
	for (auto result : reported_solution)
		printf(" %u", result);
	printf("\n");

	if (preserve_graph)
	{
		// Release only an exact query-local CSR.  If no vertex was removed,
		// pstart/edges still borrow the immutable original graph.
		if (owns_query_graph)
		{
			delete[] pstart;
			delete[] edges;
		}
		n = saved_n;
		m = saved_m;
		pstart = saved_pstart;
		edges = saved_edges;
	}
}

ui Graph::degen(ui n, ui *peel_sequence, ui *core, ept *pstart, ui *edges, ui *degree, char *vis, ListLinearHeap *heap, ui &core_q, ui query_vertex)
{
	Timer t;
	ui threshold = (feasible_solution.size() + 1 > S ? feasible_solution.size() + 1 - S : 0);

	for (ui i = 0; i < n; i++)
		degree[i] = pstart[i + 1] - pstart[i];

	ui queue_n = 0, new_size = 0;
	for (ui i = 0; i < n; i++)
		if (degree[i] < threshold)
			peel_sequence[queue_n++] = i;

	for (ui i = 0; i < queue_n; i++)
	{
		ui u = peel_sequence[i];
		degree[u] = 0;
		for (ept j = pstart[u]; j < pstart[u + 1]; j++)
			if (degree[edges[j]] > 0u)
				if ((degree[edges[j]]--) == threshold)
					peel_sequence[queue_n++] = edges[j];
	}
	ui UB = n;
	if (queue_n == n)
		UB = feasible_solution.size();

	memset(vis, 0, sizeof(char) * n);
	for (ui i = 0; i < n; i++)
	{
		if (degree[i] >= threshold)
			peel_sequence[queue_n + (new_size++)] = i;
		else
		{
			vis[i] = 1;
			core[i] = 0;
			if (i == query_vertex)
				core_q = 0;
		}
	}
	assert(queue_n + new_size == n);

	if (new_size != 0u)
	{

		heap->init(new_size, new_size - 1, peel_sequence + queue_n, degree);
		ui max_core = 0;
		ui idx = n;
		UB = 0;
		for (ui i = 0; i < new_size; i++)
		{
			ui u = 0, key = 0;
			heap->pop_min(u, key);
			if (key > max_core)
				max_core = key;
			core[u] = max_core;
			if (u == query_vertex)
				core_q = core[u];
			peel_sequence[queue_n + i] = u;

			ui t_UB = core[u] + S;
			if (new_size - i < t_UB)
				t_UB = new_size - i;
			if (t_UB > UB)
				UB = t_UB;

			if (idx == n && key + S >= new_size - i)
				idx = i;
			vis[u] = 1;

			for (ept j = pstart[u]; j < pstart[u + 1]; j++)
				if (vis[edges[j]] == 0)
					heap->decrement(edges[j], 1);
		}
	}

	return UB;
}

// core shrink:
