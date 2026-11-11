#include "OfflineIndex.h"
#include "../Graph.h"

bool OfflineIndex::load(Graph &graph, const std::string &path)
{
	return graph.load_offline_index(path);
}

#include <cerrno>
#include <cstring>
#include <fcntl.h>
#include <fstream>
#include <limits>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

using namespace std;

namespace
{
const char INDEX_MAGIC_FULL[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '1'};
const char INDEX_MAGIC_QUERY[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '2'};
const char INDEX_MAGIC_FULL_CORE[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '3'};
const char INDEX_MAGIC_QUERY_CORE[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '4'};
const char INDEX_MAGIC_FULL_CORE_PEEL[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '5'};
const char INDEX_MAGIC_QUERY_CORE_PEEL[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '6'};
const char INDEX_MAGIC_FULL_CORE_PEEL_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '7'};
const char INDEX_MAGIC_QUERY_CORE_PEEL_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '8'};
const char INDEX_MAGIC_CORE_PEEL_ONLY_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', '9'};
const char INDEX_MAGIC_CORE_ONLY_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'A'};
const char INDEX_MAGIC_CORE_THRESHOLD_BITMAP_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'B'};
const char INDEX_MAGIC_HYBRID_CORE_THRESHOLD_BITMAP_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'C'};
const char INDEX_MAGIC_CORE_ORDERED_ADJACENCY_FP[8] = {'S', 'E', 'M', 'N', 'I', 'D', 'X', 'D'};
const ui INVALID_VERTEX = numeric_limits<ui>::max();
}

bool Graph::load_offline_index(const std::string &index_file)
{
	release_index_core_threshold_bitmap_mapping();
	release_index_core_ordered_adjacency_mapping();
	release_index_peel_mapping();
	index_core_ordered_adjacency_available = false;
	index_core_ordered_adjacency_file.clear();
	index_core_ordered_adjacency_offset = 0;
	index_core_ordered_adjacency_bytes = 0;
	index_peel_available = false;
	index_peel_file.clear();
	index_peel_offset = 0;
	index_peel_bytes = 0;
	index_core_threshold_bitmap_loaded = false;
	index_core_threshold_max = 0;
	index_core_threshold_words = 0;
	index_core_threshold_counts.clear();
	index_core_threshold_core_sums.clear();
	index_core_threshold_bitmap_available = false;
	index_core_threshold_bitmap_file.clear();
	index_core_threshold_bitmap_offset = 0;
	index_core_threshold_bitmap_bytes = 0;
	if (!concise_query_log())
	{
		printf("[Index][Load] opening index path=%s\n", index_file.c_str());
		fflush(stdout);
	}
	ifstream in(index_file, ios::binary | ios::ate);
	if (!in.is_open())
	{
		printf("Failed to open %s for reading\n", index_file.c_str());
		fflush(stdout);
		return false;
	}
	long long index_file_size_bytes = (long long)in.tellg();
	if (!concise_query_log())
	{
		printf("[Index][Load] open success file_size_bytes=%lld\n", index_file_size_bytes);
		fflush(stdout);
	}
	in.seekg(0, ios::beg);

	char magic[sizeof(INDEX_MAGIC_FULL)];
	in.read(magic, sizeof(magic));
	bool is_full_index = memcmp(magic, INDEX_MAGIC_FULL, sizeof(INDEX_MAGIC_FULL)) == 0 ||
						 memcmp(magic, INDEX_MAGIC_FULL_CORE, sizeof(INDEX_MAGIC_FULL_CORE)) == 0 ||
						 memcmp(magic, INDEX_MAGIC_FULL_CORE_PEEL, sizeof(INDEX_MAGIC_FULL_CORE_PEEL)) == 0 ||
						 memcmp(magic, INDEX_MAGIC_FULL_CORE_PEEL_FP, sizeof(INDEX_MAGIC_FULL_CORE_PEEL_FP)) == 0;
	bool is_query_index = memcmp(magic, INDEX_MAGIC_QUERY, sizeof(INDEX_MAGIC_QUERY)) == 0 ||
						  memcmp(magic, INDEX_MAGIC_QUERY_CORE, sizeof(INDEX_MAGIC_QUERY_CORE)) == 0 ||
						  memcmp(magic, INDEX_MAGIC_QUERY_CORE_PEEL, sizeof(INDEX_MAGIC_QUERY_CORE_PEEL)) == 0 ||
						  memcmp(magic, INDEX_MAGIC_QUERY_CORE_PEEL_FP, sizeof(INDEX_MAGIC_QUERY_CORE_PEEL_FP)) == 0;
	if (is_query_index)
	{
		printf("The index file %s is query-specific; only full-graph indexes are allowed\n", index_file.c_str());
		fflush(stdout);
		return false;
	}
	bool is_core_peel_only_index =
		memcmp(magic, INDEX_MAGIC_CORE_PEEL_ONLY_FP, sizeof(INDEX_MAGIC_CORE_PEEL_ONLY_FP)) == 0;
	bool is_core_only_index =
		memcmp(magic, INDEX_MAGIC_CORE_ONLY_FP, sizeof(INDEX_MAGIC_CORE_ONLY_FP)) == 0;
	bool is_core_threshold_bitmap_index =
		memcmp(magic, INDEX_MAGIC_CORE_THRESHOLD_BITMAP_FP,
			   sizeof(INDEX_MAGIC_CORE_THRESHOLD_BITMAP_FP)) == 0;
	bool is_hybrid_core_threshold_bitmap_index =
		memcmp(magic, INDEX_MAGIC_HYBRID_CORE_THRESHOLD_BITMAP_FP,
			   sizeof(INDEX_MAGIC_HYBRID_CORE_THRESHOLD_BITMAP_FP)) == 0;
	bool is_core_ordered_adjacency_index =
		memcmp(magic, INDEX_MAGIC_CORE_ORDERED_ADJACENCY_FP,
			   sizeof(INDEX_MAGIC_CORE_ORDERED_ADJACENCY_FP)) == 0;
	bool is_ctbi_index = is_core_threshold_bitmap_index ||
		is_hybrid_core_threshold_bitmap_index || is_core_ordered_adjacency_index;
	bool is_metadata_only_index = is_core_peel_only_index || is_core_only_index ||
		is_ctbi_index;
	bool has_core = memcmp(magic, INDEX_MAGIC_FULL_CORE, sizeof(INDEX_MAGIC_FULL_CORE)) == 0 ||
					memcmp(magic, INDEX_MAGIC_QUERY_CORE, sizeof(INDEX_MAGIC_QUERY_CORE)) == 0 ||
					memcmp(magic, INDEX_MAGIC_FULL_CORE_PEEL, sizeof(INDEX_MAGIC_FULL_CORE_PEEL)) == 0 ||
					memcmp(magic, INDEX_MAGIC_QUERY_CORE_PEEL, sizeof(INDEX_MAGIC_QUERY_CORE_PEEL)) == 0 ||
					memcmp(magic, INDEX_MAGIC_FULL_CORE_PEEL_FP, sizeof(INDEX_MAGIC_FULL_CORE_PEEL_FP)) == 0 ||
					memcmp(magic, INDEX_MAGIC_QUERY_CORE_PEEL_FP, sizeof(INDEX_MAGIC_QUERY_CORE_PEEL_FP)) == 0 ||
					is_metadata_only_index;
	bool has_peel = memcmp(magic, INDEX_MAGIC_FULL_CORE_PEEL, sizeof(INDEX_MAGIC_FULL_CORE_PEEL)) == 0 ||
					memcmp(magic, INDEX_MAGIC_QUERY_CORE_PEEL, sizeof(INDEX_MAGIC_QUERY_CORE_PEEL)) == 0 ||
					memcmp(magic, INDEX_MAGIC_FULL_CORE_PEEL_FP, sizeof(INDEX_MAGIC_FULL_CORE_PEEL_FP)) == 0 ||
					memcmp(magic, INDEX_MAGIC_QUERY_CORE_PEEL_FP, sizeof(INDEX_MAGIC_QUERY_CORE_PEEL_FP)) == 0 ||
					is_core_peel_only_index || is_hybrid_core_threshold_bitmap_index ||
					is_core_ordered_adjacency_index;
	bool has_fingerprint =
		memcmp(magic, INDEX_MAGIC_FULL_CORE_PEEL_FP, sizeof(INDEX_MAGIC_FULL_CORE_PEEL_FP)) == 0 ||
		memcmp(magic, INDEX_MAGIC_QUERY_CORE_PEEL_FP, sizeof(INDEX_MAGIC_QUERY_CORE_PEEL_FP)) == 0 ||
		is_metadata_only_index;
	if (!in || (!is_full_index && !is_metadata_only_index))
	{
		printf("The index file %s is invalid or uses an unsupported format\n", index_file.c_str());
		fflush(stdout);
		return false;
	}

	ui indexed_n = 0;
	ept indexed_m = 0;
	unsigned long long indexed_fingerprint_lo = 0;
	unsigned long long indexed_fingerprint_hi = 0;
	ui indexed_query_count = 0;
	unsigned long long total_candidates = 0;
	in.read(reinterpret_cast<char *>(&indexed_n), sizeof(ui));
	if (has_fingerprint)
	{
		in.read(reinterpret_cast<char *>(&indexed_m), sizeof(ept));
		in.read(reinterpret_cast<char *>(&indexed_fingerprint_lo), sizeof(unsigned long long));
		in.read(reinterpret_cast<char *>(&indexed_fingerprint_hi), sizeof(unsigned long long));
	}
	if (is_ctbi_index)
	{
		in.read(reinterpret_cast<char *>(&index_core_threshold_max), sizeof(ui));
		in.read(reinterpret_cast<char *>(&index_core_threshold_words), sizeof(unsigned long long));
	}
	if (is_metadata_only_index)
	{
		indexed_query_count = 0;
		total_candidates = 0;
	}
	else if (is_full_index)
	{
		indexed_query_count = indexed_n;
		in.read(reinterpret_cast<char *>(&total_candidates), sizeof(unsigned long long));
	}
	if (!in)
	{
		printf("The index file %s is truncated\n", index_file.c_str());
		fflush(stdout);
		return false;
	}
	char magic_text[sizeof(INDEX_MAGIC_FULL) + 1];
	memcpy(magic_text, magic, sizeof(INDEX_MAGIC_FULL));
	magic_text[sizeof(INDEX_MAGIC_FULL)] = '\0';
	ui expected_n = original_graph_n ? original_graph_n : n;
	if ((is_ctbi_index) &&
		index_core_threshold_words != (((unsigned long long)indexed_n + 63ull) >> 6))
	{
		printf("The CTBI file %s has an invalid bitmap word count\n", index_file.c_str());
		fflush(stdout);
		return false;
	}
	if (!concise_query_log())
	{
		printf("[Index][Load] header magic=%s type=%s has_core=%d has_peel=%d indexed_n=%u expected_n=%u indexed_query_count=%u total_candidates=%llu\n",
			   magic_text,
			   (is_core_ordered_adjacency_index ? "core_ordered_adjacency_hybrid_ctbi" :
			   (is_hybrid_core_threshold_bitmap_index ? "hybrid_core_peel_threshold_bitmap" :
			   (is_core_threshold_bitmap_index ? "core_threshold_bitmap" :
			   (is_core_only_index ? "core_only" :
			   (is_core_peel_only_index ? "core_peel_only" : (is_full_index ? "full" : "query")))))),
			   has_core ? 1 : 0,
			   has_peel ? 1 : 0,
			   indexed_n,
			   expected_n,
			   indexed_query_count,
			   total_candidates);
		fflush(stdout);
	}

	if (indexed_n != expected_n)
	{
		printf("The index file %s is built for a graph with %u vertices, but the current graph has %u vertices\n",
			   index_file.c_str(), indexed_n, expected_n);
		fflush(stdout);
		return false;
	}
	if (has_fingerprint)
	{
		if (indexed_m != original_graph_m)
		{
			printf("The index file %s is built for a graph with %u directed edges, but the current graph has %u\n",
				index_file.c_str(), indexed_m, original_graph_m);
			fflush(stdout);
			return false;
		}
		ensure_graph_fingerprint();
		if (indexed_fingerprint_lo != graph_fingerprint_lo ||
			indexed_fingerprint_hi != graph_fingerprint_hi)
		{
			printf("The index file %s does not match the current graph CSR fingerprint\n",
				index_file.c_str());
			fflush(stdout);
			return false;
		}
	}
	else
	{
		if (!concise_query_log())
		{
			printf("[Index][Warning] legacy index has no graph fingerprint; rebuild it to enable graph validation: %s\n",
				index_file.c_str());
			fflush(stdout);
		}
		const char *require_fingerprint = getenv("ARC_SCS_REQUIRE_FINGERPRINTED_INDEX");
		if (require_fingerprint != nullptr && require_fingerprint[0] == '1' &&
			require_fingerprint[1] == '\0')
		{
			printf("[Index][Load] rejected legacy index because ARC_SCS_REQUIRE_FINGERPRINTED_INDEX=1\n");
			fflush(stdout);
			return false;
		}
	}

	index_offsets.assign((unsigned long long)indexed_query_count + 1, 0);
	index_candidate_ids.assign(total_candidates, 0);
	index_candidate_phi.assign(total_candidates, 0);
	index_is_full = is_full_index;
	index_core.clear();
	index_core_loaded = false;
	index_core_threshold_bitmap_loaded = false;
	index_core_threshold_counts.clear();
	index_core_threshold_core_sums.clear();
	index_core_threshold_bitmap_available = false;
	index_core_threshold_bitmap_file.clear();
	index_core_threshold_bitmap_offset = 0;
	index_core_threshold_bitmap_bytes = 0;
	index_core_ordered_adjacency_loaded = false;
	index_core_ordered_adjacency_available = false;
	index_core_ordered_adjacency_file.clear();
	index_core_ordered_adjacency_offset = 0;
	index_core_ordered_adjacency_bytes = 0;
	index_peel_sequence.clear();
	index_peel_loaded = false;
	index_peel_load_us = 0;

	if (has_core)
	{
		index_core.assign(indexed_n, 0);
		in.read(reinterpret_cast<char *>(index_core.data()), sizeof(ui) * index_core.size());
		if (in)
			index_core_loaded = true;
	}

	if ((is_ctbi_index) &&
		index_core_loaded)
	{
		Timer bitmap_metadata_load_timer;
		const unsigned long long threshold_count =
			(unsigned long long)index_core_threshold_max + 1ull;
		const unsigned long long bitmap_value_count =
			threshold_count * index_core_threshold_words;
		if (threshold_count > 4096ull ||
			bitmap_value_count > (unsigned long long)std::numeric_limits<size_t>::max() /
				sizeof(unsigned long long))
			in.setstate(ios::failbit);
		else
		{
			index_core_threshold_counts.assign((size_t)threshold_count, 0);
			index_core_threshold_core_sums.assign((size_t)threshold_count, 0);
			in.read(reinterpret_cast<char *>(index_core_threshold_counts.data()),
				  sizeof(unsigned long long) * index_core_threshold_counts.size());
			in.read(reinterpret_cast<char *>(index_core_threshold_core_sums.data()),
				  sizeof(unsigned long long) * index_core_threshold_core_sums.size());
			index_core_threshold_bitmap_offset = (unsigned long long)in.tellg();
			index_core_threshold_bitmap_bytes = (size_t)bitmap_value_count *
				sizeof(unsigned long long);
			const unsigned long long expected_end =
				index_core_threshold_bitmap_offset + index_core_threshold_bitmap_bytes +
				(is_core_ordered_adjacency_index ?
				 sizeof(ui) * (unsigned long long)indexed_m : 0ull) +
				((is_hybrid_core_threshold_bitmap_index || is_core_ordered_adjacency_index) ?
				 sizeof(ui) * (unsigned long long)indexed_n : 0ull);
			if (!in || expected_end != (unsigned long long)index_file_size_bytes)
			{
				printf("The CTBI file %s has an invalid bitmap partition size\n",
					index_file.c_str());
				in.setstate(ios::failbit);
			}
			else
			{
				index_core_threshold_bitmap_file = index_file;
				index_core_threshold_bitmap_available = true;
				in.seekg((streamoff)index_core_threshold_bitmap_bytes, ios::cur);
			}
		}
	}

	if (is_core_ordered_adjacency_index && index_core_threshold_bitmap_available)
	{
		if ((unsigned long long)indexed_m >
			(unsigned long long)std::numeric_limits<size_t>::max() / sizeof(ui))
			in.setstate(ios::failbit);
		index_core_ordered_adjacency_offset = (unsigned long long)in.tellg();
		index_core_ordered_adjacency_bytes = in ?
			sizeof(ui) * (size_t)indexed_m : 0;
		const unsigned long long expected_end =
			index_core_ordered_adjacency_offset +
			(unsigned long long)index_core_ordered_adjacency_bytes +
			sizeof(ui) * (unsigned long long)indexed_n;
		if (!in || expected_end != (unsigned long long)index_file_size_bytes)
		{
			printf("The COAP file %s has an invalid adjacency partition size\n",
				index_file.c_str());
			in.setstate(ios::failbit);
		}
		else
		{
			index_core_ordered_adjacency_file = index_file;
			index_core_ordered_adjacency_available = true;
			in.seekg((streamoff)index_core_ordered_adjacency_bytes, ios::cur);
		}
	}

	if (has_peel &&
		(is_core_peel_only_index || is_hybrid_core_threshold_bitmap_index ||
		 is_core_ordered_adjacency_index))
	{
		index_peel_offset = (unsigned long long)in.tellg();
		index_peel_bytes = sizeof(ui) * (size_t)indexed_n;
		const unsigned long long expected_end = index_peel_offset + index_peel_bytes;
		if (expected_end != (unsigned long long)index_file_size_bytes)
		{
			printf("The index file %s has an invalid core/peel partition size\n", index_file.c_str());
			in.setstate(ios::failbit);
		}
		else
		{
			index_peel_file = index_file;
			index_peel_available = true;
			in.seekg((streamoff)index_peel_bytes, ios::cur);
		}
	}
	else if (has_peel)
	{
		Timer peel_load_timer;
		index_peel_sequence.assign(indexed_n, 0);
		in.read(reinterpret_cast<char *>(index_peel_sequence.data()), sizeof(ui) * index_peel_sequence.size());
		index_peel_load_us = peel_load_timer.elapsed();
		if (in)
			index_peel_loaded = true;
	}

	if (!is_metadata_only_index)
		in.read(reinterpret_cast<char *>(index_offsets.data()), sizeof(unsigned long long) * index_offsets.size());
	if (total_candidates > static_cast<unsigned long long>(0))
	{
		in.read(reinterpret_cast<char *>(index_candidate_ids.data()), sizeof(ui) * index_candidate_ids.size());
		in.read(reinterpret_cast<char *>(index_candidate_phi.data()), sizeof(ui) * index_candidate_phi.size());
	}
	if (!in)
	{
		printf("The index file %s is truncated\n", index_file.c_str());
		index_offsets.clear();
		index_candidate_ids.clear();
		index_candidate_phi.clear();
		index_core.clear();
		index_core_loaded = false;
		index_core_threshold_bitmap_loaded = false;
		index_core_threshold_counts.clear();
		index_core_threshold_core_sums.clear();
		index_core_threshold_bitmap_available = false;
		index_core_threshold_bitmap_file.clear();
		index_core_threshold_bitmap_offset = 0;
		index_core_threshold_bitmap_bytes = 0;
		index_core_ordered_adjacency_loaded = false;
		index_core_ordered_adjacency_available = false;
		index_core_ordered_adjacency_file.clear();
		index_core_ordered_adjacency_offset = 0;
		index_core_ordered_adjacency_bytes = 0;
		index_peel_sequence.clear();
		index_peel_loaded = false;
		index_peel_available = false;
		index_peel_file.clear();
		fflush(stdout);
		return false;
	}

	index_loaded = true;
	if (!concise_query_log())
	{
		printf("Offline index has been loaded from %s\n", index_file.c_str());
		printf("\tThe indexed query count is: %s\n", Utility::integer_to_string((long long)indexed_query_count).c_str());
		printf("\tThe total number of indexed candidates is: %s\n", Utility::integer_to_string((long long)total_candidates).c_str());
		fflush(stdout);
	}
	return true;
}

void Graph::release_index_core_threshold_bitmap_mapping()
{
	if (index_core_threshold_bitmap_map_base != MAP_FAILED)
		munmap(index_core_threshold_bitmap_map_base,
			   index_core_threshold_bitmap_map_length);
	if (index_core_threshold_bitmap_fd >= 0)
		close(index_core_threshold_bitmap_fd);
	index_core_threshold_bitmap_fd = -1;
	index_core_threshold_bitmap_map_base = MAP_FAILED;
	index_core_threshold_bitmap_map_length = 0;
	index_core_threshold_bitmap_mapped_data = nullptr;
	index_core_threshold_bitmap_loaded = false;
}

bool Graph::ensure_index_core_threshold_bitmap_loaded()
{
	if (index_core_threshold_bitmap_loaded)
		return true;
	if (!index_core_threshold_bitmap_available ||
		index_core_threshold_bitmap_file.empty() ||
		index_core_threshold_bitmap_bytes == 0u)
		return false;

	Timer bitmap_map_timer;
	index_core_threshold_bitmap_fd = open(
		index_core_threshold_bitmap_file.c_str(), O_RDONLY);
	if (index_core_threshold_bitmap_fd < 0)
	{
		printf("[CTBI] open failed path=%s errno=%d\n",
			index_core_threshold_bitmap_file.c_str(), errno);
		return false;
	}
	long page_size = sysconf(_SC_PAGE_SIZE);
	if (page_size <= 0)
		page_size = 4096;
	const unsigned long long aligned_offset =
		index_core_threshold_bitmap_offset -
		(index_core_threshold_bitmap_offset % (unsigned long long)page_size);
	const size_t delta =
		(size_t)(index_core_threshold_bitmap_offset - aligned_offset);
	index_core_threshold_bitmap_map_length = delta +
		index_core_threshold_bitmap_bytes;
	index_core_threshold_bitmap_map_base = mmap(nullptr,
		index_core_threshold_bitmap_map_length, PROT_READ, MAP_PRIVATE,
		index_core_threshold_bitmap_fd, (off_t)aligned_offset);
	if (index_core_threshold_bitmap_map_base == MAP_FAILED)
	{
		printf("[CTBI] mmap failed path=%s errno=%d\n",
			index_core_threshold_bitmap_file.c_str(), errno);
		close(index_core_threshold_bitmap_fd);
		index_core_threshold_bitmap_fd = -1;
		index_core_threshold_bitmap_map_length = 0;
		return false;
	}
	index_core_threshold_bitmap_mapped_data =
		reinterpret_cast<const char *>(index_core_threshold_bitmap_map_base) + delta;
	index_core_threshold_bitmap_loaded = true;
	if (!concise_query_log())
		printf("[CTBI] bitmap_map_us=%s mode=readonly_mmap_lazy\n",
			Utility::integer_to_string(bitmap_map_timer.elapsed()).c_str());
	return true;
}

void Graph::release_index_core_ordered_adjacency_mapping()
{
	if (index_core_ordered_adjacency_map_base != MAP_FAILED)
		munmap(index_core_ordered_adjacency_map_base,
			   index_core_ordered_adjacency_map_length);
	if (index_core_ordered_adjacency_fd >= 0)
		close(index_core_ordered_adjacency_fd);
	index_core_ordered_adjacency_fd = -1;
	index_core_ordered_adjacency_map_base = MAP_FAILED;
	index_core_ordered_adjacency_map_length = 0;
	index_core_ordered_adjacency_mapped_data = nullptr;
	index_core_ordered_adjacency_loaded = false;
}

bool Graph::ensure_index_core_ordered_adjacency_loaded()
{
	if (index_core_ordered_adjacency_loaded)
		return true;
	if (!index_core_ordered_adjacency_available ||
		index_core_ordered_adjacency_file.empty() ||
		index_core_ordered_adjacency_bytes == 0u)
		return false;

	Timer map_timer;
	index_core_ordered_adjacency_fd = open(
		index_core_ordered_adjacency_file.c_str(), O_RDONLY);
	if (index_core_ordered_adjacency_fd < 0)
	{
		printf("[COAP] open failed path=%s errno=%d\n",
			index_core_ordered_adjacency_file.c_str(), errno);
		return false;
	}
	long page_size = sysconf(_SC_PAGE_SIZE);
	if (page_size <= 0)
		page_size = 4096;
	const unsigned long long aligned_offset =
		index_core_ordered_adjacency_offset -
		(index_core_ordered_adjacency_offset % (unsigned long long)page_size);
	const size_t delta =
		(size_t)(index_core_ordered_adjacency_offset - aligned_offset);
	index_core_ordered_adjacency_map_length =
		delta + index_core_ordered_adjacency_bytes;
	index_core_ordered_adjacency_map_base = mmap(nullptr,
		index_core_ordered_adjacency_map_length, PROT_READ, MAP_PRIVATE,
		index_core_ordered_adjacency_fd, (off_t)aligned_offset);
	if (index_core_ordered_adjacency_map_base == MAP_FAILED)
	{
		printf("[COAP] mmap failed path=%s errno=%d\n",
			index_core_ordered_adjacency_file.c_str(), errno);
		close(index_core_ordered_adjacency_fd);
		index_core_ordered_adjacency_fd = -1;
		index_core_ordered_adjacency_map_length = 0;
		return false;
	}
	index_core_ordered_adjacency_mapped_data =
		reinterpret_cast<const ui *>(
			reinterpret_cast<const char *>(index_core_ordered_adjacency_map_base) + delta);
	index_core_ordered_adjacency_loaded = true;
	if (!concise_query_log())
		printf("[COAP] adjacency_map_us=%s mode=readonly_mmap_lazy\n",
			Utility::integer_to_string(map_timer.elapsed()).c_str());
	return true;
}

void Graph::release_index_peel_mapping()
{
	if (index_peel_map_base != MAP_FAILED)
		munmap(index_peel_map_base, index_peel_map_length);
	if (index_peel_fd >= 0)
		close(index_peel_fd);
	index_peel_fd = -1;
	index_peel_map_base = MAP_FAILED;
	index_peel_map_length = 0;
	index_peel_mapped_data = nullptr;
	index_peel_loaded = false;
}

bool Graph::ensure_index_peel_loaded()
{
	if (index_peel_loaded)
		return true;
	if (!index_peel_available || index_peel_file.empty() || index_peel_bytes == 0u)
		return false;

	Timer peel_load_timer;
	index_peel_fd = open(index_peel_file.c_str(), O_RDONLY);
	if (index_peel_fd < 0)
	{
		printf("[Index][Peel] open failed path=%s errno=%d\n", index_peel_file.c_str(), errno);
		return false;
	}
	long page_size = sysconf(_SC_PAGE_SIZE);
	if (page_size <= 0)
		page_size = 4096;
	const unsigned long long aligned_offset = index_peel_offset - (index_peel_offset % (unsigned long long)page_size);
	const size_t delta = (size_t)(index_peel_offset - aligned_offset);
	index_peel_map_length = delta + index_peel_bytes;
	index_peel_map_base = mmap(nullptr, index_peel_map_length, PROT_READ, MAP_PRIVATE,
		index_peel_fd, (off_t)aligned_offset);
	if (index_peel_map_base == MAP_FAILED)
	{
		printf("[Index][Peel] mmap failed path=%s errno=%d\n", index_peel_file.c_str(), errno);
		close(index_peel_fd);
		index_peel_fd = -1;
		index_peel_map_length = 0;
		return false;
	}
	index_peel_mapped_data = reinterpret_cast<const ui *>(
		reinterpret_cast<const char *>(index_peel_map_base) + delta);
	index_peel_load_us = peel_load_timer.elapsed();
	index_peel_loaded = true;
	printf("[Time] peel_load_us=%s mode=readonly_mmap_lazy\n",
		Utility::integer_to_string(index_peel_load_us).c_str());
	fflush(stdout);
	return true;
}

const Graph::QueryResult &Graph::get_last_query_result() const
{
	return last_query_result;
}

// Core-only indexes contain no candidate ranges and return a miss.
bool Graph::get_index_range(ui original_q, unsigned long long &begin, unsigned long long &end) const
{
	if (!concise_query_log())
	{
		printf("[Index][Query] lookup query_id=%u\n", original_q);
		fflush(stdout);
	}
	if (!index_loaded)
	{
		printf("[Index][Query] index miss query_id=%u reason=index_not_loaded\n", original_q);
		fflush(stdout);
		return false;
	}

	if (index_is_full)
	{
		if (original_q + 1 >= index_offsets.size())
		{
			printf("[Index][Query] index miss query_id=%u reason=full_index_range_out_of_bounds offsets_size=%zu\n",
				   original_q, index_offsets.size());
			fflush(stdout);
			return false;
		}
		begin = index_offsets[original_q];
		end = index_offsets[original_q + 1];
		if (!concise_query_log())
		{
			printf("[Index][Query] index hit query_id=%u entry_pos=%u begin=%llu end=%llu count=%llu\n",
				   original_q, original_q, begin, end, end >= begin ? end - begin : 0);
			fflush(stdout);
		}
		return true;
	}

	printf("[Index][Query] index miss query_id=%u reason=full_graph_core_only_has_no_candidate_ranges\n", original_q);
	fflush(stdout);
	return false;
}

bool Graph::extract_subgraph_from_index(ui original_q, int k_min, vector<ui> &ids, vector<pair<ui, ui>> &vp)
{
	ids.clear();
	vp.clear();
	unsigned long long begin = 0, end = 0;
	if (shrink_old2new.empty() || !get_index_range(original_q, begin, end))
	{
		printf("[Index][Query] fallback_to_non_index_path query_id=%u reason=%s\n",
			   original_q, shrink_old2new.empty() ? "shrink_mapping_empty" : "index_miss");
		fflush(stdout);
		return false;
	}

	ui query_vertex = shrink_old2new[original_q];
	if (query_vertex == INVALID_VERTEX)
	{
		printf("[Index][Query] fallback_to_non_index_path query_id=%u reason=query_deleted_by_core_shrink\n", original_q);
		fflush(stdout);
		return false;
	}

	vector<char> exists(n, 0);
	vector<ui> rid(n, INVALID_VERTEX);
	ids.push_back(query_vertex);
	exists[query_vertex] = 1;
	rid[query_vertex] = 0;

	for (unsigned long long i = begin; i < end; ++i)
	{
		if (index_candidate_phi[i] <= (ui)k_min)
			continue;

		ui old_v = index_candidate_ids[i];
		if (old_v >= shrink_old2new.size())
			continue;

		ui new_v = shrink_old2new[old_v];
		if (new_v == INVALID_VERTEX || exists[new_v])
			continue;

		rid[new_v] = ids.size();
		exists[new_v] = 1;
		ids.push_back(new_v);
	}

	for (ui i = 0; i < ids.size(); ++i)
	{
		ui v = ids[i];
		for (ept j = pstart[v]; j < pstart[v + 1]; ++j)
		{
			ui w = edges[j];
			if (exists[w] && rid[v] < rid[w])
				vp.push_back(make_pair(rid[v], rid[w]));
		}
	}
	return true;
}

// Candidate-index fast path for an immutable batch graph whose core-shrunk
// CSR has not been materialized yet.  ids remain in the shrink numbering used
// by the solvers and out_mapping translates each row back to the original CSR.
bool Graph::extract_subgraph_from_index_readonly(ui original_q, int k_min,
											 const ui *out_mapping,
											 const ept *source_pstart, const ui *source_edges,
											 bool source_core_ordered,
											 vector<ui> &ids, vector<pair<ui, ui>> &vp)
{
	ids.clear();
	vp.clear();
	unsigned long long begin = 0, end = 0;
	if (shrink_old2new.empty() || !get_index_range(original_q, begin, end))
		return false;

	ui query_vertex = shrink_old2new[original_q];
	if (query_vertex == INVALID_VERTEX)
		return false;

	vector<char> exists(n, 0);
	vector<ui> rid(n, INVALID_VERTEX);
	ids.push_back(query_vertex);
	exists[query_vertex] = 1;
	rid[query_vertex] = 0;

	for (unsigned long long i = begin; i < end; ++i)
	{
		if (index_candidate_phi[i] <= (ui)k_min)
			continue;
		ui old_v = index_candidate_ids[i];
		if (old_v >= shrink_old2new.size())
			continue;
		ui new_v = shrink_old2new[old_v];
		if (new_v == INVALID_VERTEX || exists[new_v])
			continue;
		rid[new_v] = ids.size();
		exists[new_v] = 1;
		ids.push_back(new_v);
	}

	for (ui i = 0; i < ids.size(); ++i)
	{
		ui new_v = ids[i];
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
