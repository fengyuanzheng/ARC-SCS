#include "ARCSCSSolver.h"
#include "Index/IndexBuilder.h"
#include "Index/OfflineIndex.h"
#include <climits>
#include <fstream>
#include <set>
#include <stdexcept>

namespace {
struct Options {
    std::string graph, index, query_file;
    int lower=0, upper=0, query=-1;
    bool build=false, use_index=false, candidates=false;
    unsigned long long memory_mb=ARCSCSMemoryLimits::matrix_mib;
    IndexBuildOptions index_options;
};

void help() {
    std::cout << "ARC-SCS: exact size-bounded community search\n"
        "Usage: ./ARC_SCS -g GRAPH.bin -l L -u U -q V [options]\n"
        "  --use-index --index-file FILE    load an offline index\n"
        "  --use-candidate-index            use indexed 2-hop candidates\n"
        "  --build-index --index-file FILE  build a full candidate index\n"
        "  --core-only-index                store core numbers only\n"
        "  --core-peel-only-index           store core numbers and peel order\n"
        "  --core-threshold-bitmap-index    store core-threshold bitmaps\n"
        "  --hybrid-core-threshold-bitmap-index  include peel-order fallback\n"
        "  --core-ordered-adjacency-index   include core-ordered adjacency\n"
        "  --core-threshold-max N           highest bitmap threshold (default 11)\n"
        "  --batch-query-file FILE          read query IDs instead of -q\n"
        "  --matrix-memory-limit-mb N       Matrix guard (default 131072 MiB)\n"
        "  -h, --help                       show this help\n";
}

unsigned long long number(const std::string &text, unsigned long long maximum) {
    if (text.empty() || text.find_first_not_of("0123456789")!=std::string::npos)
        throw std::invalid_argument("expected an unsigned integer: "+text);
    size_t end=0;
    unsigned long long value=std::stoull(text,&end);
    if (end!=text.size() || value>maximum)
        throw std::invalid_argument("integer out of range: "+text);
    return value;
}

Options parse(int argc,char **argv) {
    Options o;
    std::set<std::string> seen;
    for (int i=1;i<argc;++i) {
        std::string a=argv[i];
        if (!seen.insert(a).second) throw std::invalid_argument("duplicate option: "+a);
        auto value=[&]() -> std::string {
            if (++i>=argc) throw std::invalid_argument("missing value for "+a);
            return argv[i];
        };
        if (a=="-g") o.graph=value();
        else if (a=="-l") o.lower=number(value(),INT_MAX);
        else if (a=="-u") o.upper=number(value(),INT_MAX);
        else if (a=="-q") o.query=number(value(),INT_MAX);
        else if (a=="--index-file") o.index=value();
        else if (a=="--batch-query-file") o.query_file=value();
        else if (a=="--use-index") o.use_index=true;
        else if (a=="--use-candidate-index") o.candidates=true;
        else if (a=="--build-index") o.build=true;
        else if (a=="--core-only-index") o.index_options.core_only=true;
        else if (a=="--core-peel-only-index") o.index_options.core_peel_only=true;
        else if (a=="--core-threshold-bitmap-index") o.index_options.core_threshold_bitmap=true;
        else if (a=="--hybrid-core-threshold-bitmap-index") o.index_options.hybrid_core_threshold_bitmap=true;
        else if (a=="--core-ordered-adjacency-index") o.index_options.core_ordered_adjacency=true;
        else if (a=="--core-threshold-max") o.index_options.core_threshold_max=number(value(),4095);
        else if (a=="--matrix-memory-limit-mb") o.memory_mb=number(value(),ULLONG_MAX/(1024ull*1024ull));
        else throw std::invalid_argument("unknown option: "+a);
    }
    if (o.graph.empty()) throw std::invalid_argument("-g is required");
    if (!o.memory_mb) throw std::invalid_argument("memory limit must be positive");
    const auto &b=o.index_options;
    int formats=b.core_only+b.core_peel_only+b.core_threshold_bitmap+b.hybrid_core_threshold_bitmap+b.core_ordered_adjacency;
    if (formats>1) throw std::invalid_argument("choose one index format");
    if ((formats || seen.count("--core-threshold-max")) && !o.build)
        throw std::invalid_argument("index construction options require --build-index");
    if (seen.count("--core-threshold-max") && !(b.core_threshold_bitmap || b.hybrid_core_threshold_bitmap || b.core_ordered_adjacency))
        throw std::invalid_argument("--core-threshold-max requires a bitmap index format");
    if ((o.build || o.use_index) && o.index.empty())
        throw std::invalid_argument("--index-file is required");
    if (!o.build && !o.use_index && !o.index.empty())
        throw std::invalid_argument("--index-file requires --build-index or --use-index");
    if (o.candidates && !o.use_index)
        throw std::invalid_argument("--use-candidate-index requires --use-index");
    if (o.build && (o.use_index || o.candidates || o.lower || o.upper || o.query>=0 || !o.query_file.empty()))
        throw std::invalid_argument("index construction and queries are separate commands");
    if (!o.build && (o.lower<1 || o.upper<o.lower || ((o.query>=0)==!o.query_file.empty())))
        throw std::invalid_argument("require 1 <= L <= U and exactly one of -q or --batch-query-file");
    return o;
}

std::vector<int> queries(const Options &o) {
    if (o.query>=0) return {o.query};
    std::ifstream in(o.query_file);
    if (!in) throw std::runtime_error("cannot open query file: "+o.query_file);
    std::vector<int> result;
    std::set<int> seen;
    std::string line;
    while (std::getline(in,line)) {
        auto start=line.find_first_not_of(" \t\r");
        if (start==std::string::npos || line[start]=='#') continue;
        auto end=line.find_last_not_of(" \t\r");
        int q=number(line.substr(start,end-start+1),INT_MAX);
        if (!seen.insert(q).second) throw std::invalid_argument("duplicate query ID");
        result.push_back(q);
    }
    if (in.bad() || result.empty()) throw std::runtime_error("empty or unreadable query file");
    return result;
}
}

int main(int argc,char **argv) {
    try {
        if (argc==1 || (argc==2 && (std::string(argv[1])=="--help" || std::string(argv[1])=="-h"))) {
            help(); return 0;
        }
        Options o=parse(argc,argv);
        Graph graph(o.graph.c_str(),1);
        graph.readBinFile();
        if (o.build) return IndexBuilder::build(graph,o.index,o.index_options)?0:1;
        if (o.use_index && !OfflineIndex::load(graph,o.index)) return 1;
        ARCSCSConfig config;
        config.use_index=o.use_index;
        config.use_candidate_index=o.candidates;
        config.preserve_graph=!o.query_file.empty();
        config.memory_limit_mb=o.memory_mb;
        ARCSCSSolver solver(graph,config);
        bool failed=false;
        for (int q:queries(o)) {
            int lower=0,upper=o.upper-1;
            std::cout << "[Query] vertex=" << q << " size_range=[" << o.lower << ',' << o.upper << "]\n";
            SearchResult result=solver.solve_arc_scs(q,o.lower,o.upper,lower,upper);
            if (result.infeasible) std::cout << "[Status] NO_FEASIBLE\n";
            else if (result.success) {
                std::cout << "[Status] SUCCESS\n";
            } else {
                std::cout << "[Status] FAILED\n"; failed=true;
            }
        }
        return failed?1:0;
    } catch (const std::exception &e) {
        std::cerr << "ARC-SCS: " << e.what() << '\n'; return 1;
    }
}
