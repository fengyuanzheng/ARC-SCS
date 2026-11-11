#ifndef ARC_SCS_CONFIG_H
#define ARC_SCS_CONFIG_H

// Allocation guards; maximums, not reservations.
namespace ARCSCSMemoryLimits
{
static constexpr unsigned long long matrix_mib = 131072;
static constexpr unsigned long long auxiliary_bytes = 8ull * 1024ull * 1024ull * 1024ull;
}

// Execution options shared by the command-line and solver interfaces.
struct ARCSCSConfig
{
	bool use_index = false;
	bool use_candidate_index = false;
	bool preserve_graph = false;

	unsigned long long memory_limit_mb = ARCSCSMemoryLimits::matrix_mib;

	bool concise_log = false;
};

#endif
