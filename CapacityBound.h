#ifndef _CAPACITY_BOUND_
#define _CAPACITY_BOUND_

#include "Utility.h"
#include <algorithm>
#include <limits>

// Native work credits shared by ARC-SCS modules.  Each field is consumed only
// by work measured in the same unit; no machine-time conversion is used.
struct ARCWorkLedger
{
	unsigned long long edge_scan_credit = 0;
	unsigned long long word_op_credit = 0;
	unsigned long long dp_state_credit = 0;
	unsigned long long bb_node_credit = 0;
};

namespace CapacityBound
{
struct TripleResult
{
	ui upper_bound = 0;
	unsigned long long dp_states = 0;
};

// Solve exactly the cardinality relaxation induced by three unit-capacity
// constraints. counts[mask] is the number of candidates whose non-neighbor
// signature on the three selected vertices is mask (bit i consumes budget i).
// Returns false when the exact enumeration would exceed max_dp_states.
inline bool exact_triple_relaxation(const ui counts[8], const ui budgets[3],
									ui max_dp_states, TripleResult &result)
{
	ui remaining[3] = {budgets[0], budgets[1], budgets[2]};
	ui base = counts[0];
	const ui single_masks[3] = {1u, 2u, 4u};
	for (ui i = 0; i < 3u; ++i)
	{
		ui take = std::min(counts[single_masks[i]], remaining[i]);
		base += take;
		remaining[i] -= take;
	}

	ui max_triple = std::min(counts[7],
							 std::min(remaining[0], std::min(remaining[1], remaining[2])));
	unsigned long long states = 0;
	for (ui x7 = 0; x7 <= max_triple; ++x7)
	{
		ui max_pair01 = std::min(counts[3],
								 std::min(remaining[0] - x7, remaining[1] - x7));
		states += (unsigned long long)max_pair01 + 1ull;
		if (states > max_dp_states)
			return false;
	}

	ui best_multi = 0;
	for (ui x7 = 0; x7 <= max_triple; ++x7)
	{
		ui r0 = remaining[0] - x7;
		ui r1 = remaining[1] - x7;
		ui r2 = remaining[2] - x7;
		ui max_pair01 = std::min(counts[3], std::min(r0, r1));
		for (ui x3 = 0; x3 <= max_pair01; ++x3)
		{
			ui max_pair02 = std::min(counts[5], r0 - x3);
			ui max_pair12 = std::min(counts[6], r1 - x3);
			ui take_other_pairs = std::min(r2, max_pair02 + max_pair12);
			ui value = x7 + x3 + take_other_pairs;
			if (best_multi < value)
				best_multi = value;
		}
	}

	result.upper_bound = base + best_multi;
	result.dp_states = states;
	return true;
}

} // namespace CapacityBound

#endif
