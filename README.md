# ARC-SCS

**Adaptive Reduction and Capacity Bounds for Size-Bounded Community Search (ARC-SCS)** finds an exact size-bounded community in a simple undirected graph. Given a query vertex `q` and size interval `[l, h]`, it returns a connected community containing `q` that maximizes the minimum degree, subject to `l <= |C| <= h`.

The search combines Adaptive Query-Equivalent Reduction (AQER), Hierarchical Exact Capacity Upper Bounds (HECUB), and Unified Incremental State Maintenance (UISM).

## Build

Requires 64-bit Linux, GNU Make, and GNU `g++` with C++14 and LTO support.

```bash
make -j2
make graph-tool
./ARC_SCS --help
```

Run `make clean` to remove build outputs.

### Self-check

With Python 3.8 or later installed, run:

```bash
make check
```

The checks generate small graphs in a temporary directory, compare exact
answers with exhaustive enumeration, and verify index formats, sequential
queries, graph conversion, and rejection of malformed inputs. No datasets,
query selections, indexes, or Python packages need to be downloaded.

## Project structure

```text
main.cpp                      Command-line interface
ARCSCSSolver.*                 Solver interface
ARCSCSConfig.h                 Execution options and allocation guards
Graph.*                        Graph storage and exact search coordination
AdaptiveReduction.cpp          Query reduction
HeuristicSearch.cpp            Feasible-community search and lower bounds
CapacitySearch.*               Exact-search interface
MBBPS.h, MBBPS_matrix.h         Sparse and matrix search backends
CapacityBound.h                Capacity bounds and work accounting
ForcedNeighborProbe.h          Bounded witness search
Index/                         Offline index construction and loading
tools/graph_tool.cpp           Graph conversion tool
tests/smoke.py                Generated-graph self-check
licenses/                      Third-party license notices
```

## Datasets and graph format

Graph data and index files are supplied separately. [DBLP](https://snap.stanford.edu/data/com-DBLP.html), [Google](https://snap.stanford.edu/data/web-Google.html), [Email](https://snap.stanford.edu/data/email-Enron.html), [Gplus](https://snap.stanford.edu/data/egonets-Gplus.html), [HepPh](https://snap.stanford.edu/data/cit-HepPh.html), [BerkStan](https://snap.stanford.edu/data/web-BerkStan.html), [Epinions](https://snap.stanford.edu/data/soc-sign-epinions.html), [Orkut](https://snap.stanford.edu/data/com-Orkut.html), and [YouTube](https://snap.stanford.edu/data/com-Youtube.html) are available from SNAP. [Flickr](https://networkrepository.com/soc-flickr-und.php) is available from Network Repository, and [UK2002](https://law.di.unimi.it/webdata/uk-2002/) and [Webbase](https://law.di.unimi.it/webdata/webbase-2001/) are available from WebGraph/LAW.

The solver accepts **`.bin` files only**: native-endian 32-bit unsigned integers in CSR form, with zero-based vertex IDs, sorted adjacency lists, no duplicate edges or self-loops, and both directions of every undirected edge. It checks the file length and CSR invariants before processing a query. Vertex counts must fit a signed 32-bit integer.

```text
[integer_width = 4][n][m][degree[0] ... degree[n-1]][adjacency[0] ... adjacency[m-1]]
```

`n` is the number of vertices, `m = 2|E|` is the number of adjacency entries, and the degrees sum to `m`.

### Convert a graph

```bash
./tools/graph_tool --input graph.txt --output graph.bin
```

The converter accepts edge lists and square coordinate Matrix Market files. It symmetrizes edges, removes self-loops and duplicates, and sorts adjacency lists. Use `--format headered` for headered edge lists, `--id-base 1` for one-based IDs, `--vertices N` to preserve isolated vertices, or `--relabel` to compact IDs and save a mapping. Query IDs must follow the resulting numbering. See `./tools/graph_tool --help` for all options.

## Run a query

```bash
./ARC_SCS -g graph.bin -l 9 -u 12 -q 0
```

Replace `0` with a valid query vertex ID. The size bounds must satisfy `1 <= l <= h`.

### Optional offline index

```bash
./ARC_SCS -g graph.bin --build-index --core-peel-only-index \
  --index-file graph.idx
./ARC_SCS -g graph.bin -l 9 -u 12 -q 0 \
  --use-index --index-file graph.idx
```

Indexes are query-independent. Rebuild an index when the graph changes. Additional index formats and candidate-index options are listed by `--help`.

### Multiple queries

A query file contains one distinct vertex ID per line; blank lines and lines beginning with `#` are allowed.

```bash
./ARC_SCS -g graph.bin -l 9 -u 12 --batch-query-file queries.txt
```

Queries run sequentially using the same loaded graph and optional index. Results are written to standard output.

## Output and resource limits

The output reports the optimal minimum degree, community size, original vertex IDs, and query time. `SUCCESS` indicates an optimal community; `NO_FEASIBLE` indicates that no community meets the constraints. Invalid input or unsuccessful execution returns a nonzero exit code.

For example, a real single-query run on Google, without an offline index:

```bash
./ARC_SCS -g Google.bin -l 9 -u 12 -q 306168
```

```text
[Graph] name=Google vertices=875713 edges=4322051
[Graph] status=READY
[Query] vertex=306168 size_range=[9,12]
[Heuristic] lower_bound=2
[Timing] total_us=2,051,824 index_load_excluded=0
[Result] status=OPTIMAL min_degree=3 community_size=9
[Community] vertices: 306168 1287 5040 5032 1284 632101 306173 5031 566458
[Status] SUCCESS
```

- `lower_bound=2` is the minimum degree of the initial feasible community.
- The optimal community has minimum degree `3` and `9` vertices; `vertices` lists their original IDs, including the query vertex.
- `total_us=2,051,824` means 2.051824 seconds of query processing. Here `index_load_excluded=0` indicates that no offline index was loaded. Timing varies with the machine and load.

Query time (`total_us`, in microseconds) excludes graph loading, index loading, and offline index construction. Internal work budgets limit auxiliary searches; exhausting one does not constitute a proof of infeasibility, and the exact search retains its fallback paths.

`--matrix-memory-limit-mb N` sets the matrix allocation guard in MiB (default: 131072). It is an allocation guard, not a limit on total process memory. Allocation failures are reported separately from infeasibility.

## Baseline modifications

The baselines used in our evaluation derive from the authors' [SE-MN* code](https://github.com/liubufan1998/size-bounded-community-search/tree/f6807638562f7b41affb284cc2e0bec876091992) and its `Reproduction code for SC-BRB-star.zip` archive.

- **SE-MN\***: retain initial feasible communities, restore original vertex IDs after shrinking, correct size/connectivity handling and premature termination, use 64-bit matrix offsets, and scan complete adjacency rows when saving results. These repairs address empty or invalid output, overflow, and premature stopping. Batch-query support and result/exit-status reporting were also added.
- **SC-BRB\***: add single-query and batch interfaces, reset and release per-query state, close graph files, and capture results for consistent reporting. The original heuristics, reductions, upper bounds, and branching rules are retained, with switches matching the archive's example.

## Acknowledgments

This implementation builds on the authors' [SE-MN* code](https://github.com/liubufan1998/size-bounded-community-search):

Yang Liu, Hejiao Huang, Kaiqiang Yu, Shengxin Liu, Cheng Long, and Zhaoquan Gu.
*[Efficient Size-Bounded Community Search, Revisited: Frameworks for Practical Improvements](https://doi.org/10.1145/3769789)*.
SIGMOD 2026.

The bundled `popl.hpp` command-line parser is distributed under its [MIT license](licenses/popl-MIT.txt).
