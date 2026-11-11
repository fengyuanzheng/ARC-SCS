// Standalone converter for ARC-SCS's native-endian uint32 CSR graph format.
// No solver dependency. Linux/POSIX; compressed input uses gzip/bzip2/xz via
// exec (never a shell). Edge sorting is external and bounded by --sort-memory-mb.
#include <algorithm>
#include <cerrno>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <memory>
#include <queue>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

namespace {
using U32 = uint32_t;
using U64 = uint64_t;
constexpr U64 MAX_VERTICES = U64(std::numeric_limits<U32>::max()) - 1;
constexpr U64 MAX_ENTRIES = std::numeric_limits<U32>::max();
static_assert(sizeof(U32) == 4, "ARC-SCS requires 32-bit integers");

[[noreturn]] void fail(const std::string &s) { throw std::runtime_error(s); }
U64 integer(const std::string &s) {
    if (s.empty()) fail("expected a nonnegative integer");
    U64 v = 0;
    for (char c : s) {
        if (c < '0' || c > '9') fail("invalid nonnegative integer: " + s);
        unsigned d = unsigned(c - '0');
        if (v > (std::numeric_limits<U64>::max() - d) / 10)
            fail("integer overflow: " + s);
        v = v * 10 + d;
    }
    return v;
}
std::string lower(std::string s) {
    for (char &c : s) if (c >= 'A' && c <= 'Z') c = char(c - 'A' + 'a');
    return s;
}
bool ends(const std::string &s, const std::string &suffix) {
    return s.size() >= suffix.size() &&
        s.compare(s.size() - suffix.size(), suffix.size(), suffix) == 0;
}
std::string json(const std::string &s) {
    std::ostringstream o;
    o << '"';
    for (unsigned char c : s) {
        switch (c) {
        case '"': o << "\\\""; break;
        case '\\': o << "\\\\"; break;
        case '\n': o << "\\n"; break;
        case '\r': o << "\\r"; break;
        case '\t': o << "\\t"; break;
        default:
            if (c < 32) o << "\\u" << std::hex << std::setw(4)
                          << std::setfill('0') << unsigned(c) << std::dec;
            else o << char(c);
        }
    }
    o << '"';
    return o.str();
}
struct Options {
    std::string input, output, format = "auto";
    U64 vertices = 0, memory_mb = 512, skip_lines = 0;
    unsigned base = 0;
    bool vertices_set = false, base_set = false, relabel = false;
    bool ignore_weights = false, force = false;
};
void help() {
    std::cout <<
        "Usage: graph_tool --input GRAPH --output GRAPH.bin [options]\n"
        "  --format auto|edge-list|headered|mtx  (default: auto)\n"
        "  --id-base 0|1       Edge-list numbering (default: 0; MTX is 1-based)\n"
        "  --vertices N        Preserve N vertices, including isolated vertices\n"
        "  --relabel           Edge-list only: map arbitrary nonnegative IDs to 0..n-1\n"
        "                      Writes GRAPH.bin.ids.tsv (original_id, internal_id)\n"
        "  --ignore-weights    Explicitly discard numeric edge/matrix weights\n"
        "  --skip-lines N      Skip N leading lines (edge-list/headered only)\n"
        "  --sort-memory-mb N  Edge-sort buffer, default 512 MiB\n"
        "  --force             Replace existing regular output files\n"
        "  --help\n"
        "Text inputs may be compressed with .gz, .bz2, or .xz. Archives and\n"
        "WebGraph .graph files must first be extracted/exported to an edge list.\n"
        "Comments (#, %, //), blank lines, whitespace and comma delimiters are accepted.\n"
        "AUTO detects a Matrix Market header; otherwise it reads an edge list.\n"
        "A numeric 'n m' header must be selected explicitly with --format headered.\n"
        "All outputs are simple undirected graphs: self-loops are removed,\n"
        "edges are symmetrized/deduplicated, and each CSR row is sorted.\n";
}
Options options(int argc, char **argv) {
    Options o;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--help" || a == "-h") { help(); std::exit(0); }
        if (a == "--relabel") { o.relabel = true; continue; }
        if (a == "--ignore-weights") { o.ignore_weights = true; continue; }
        if (a == "--force") { o.force = true; continue; }
        if (a != "--input" && a != "-i" && a != "--output" && a != "-o" &&
            a != "--format" && a != "--vertices" && a != "--id-base" &&
            a != "--sort-memory-mb" && a != "--skip-lines")
            fail("unknown option: " + a);
        if (++i == argc) fail("missing value for " + a);
        std::string v = argv[i];
        if (a == "--input" || a == "-i") o.input = v;
        else if (a == "--output" || a == "-o") o.output = v;
        else if (a == "--format") o.format = lower(v);
        else if (a == "--vertices") { o.vertices = integer(v); o.vertices_set = true; }
        else if (a == "--id-base") {
            U64 b = integer(v);
            if (b > 1) fail("--id-base must be 0 or 1");
            o.base = unsigned(b); o.base_set = true;
        } else if (a == "--sort-memory-mb") o.memory_mb = integer(v);
        else o.skip_lines = integer(v);
    }
    if (o.input.empty() || o.output.empty()) fail("--input and --output are required");
    if (o.format != "auto" && o.format != "edge-list" &&
        o.format != "headered" && o.format != "mtx") fail("unsupported --format");
    if (o.vertices_set && (o.vertices == 0 || o.vertices > MAX_VERTICES))
        fail("--vertices exceeds ARC-SCS's supported uint32 vertex range");
    if (o.relabel && (o.vertices_set || o.base_set))
        fail("--relabel cannot be combined with --vertices or --id-base");
    if (o.memory_mb == 0 ||
        o.memory_mb > std::numeric_limits<size_t>::max() / (1024ull * 1024ull))
        fail("invalid --sort-memory-mb");
    return o;
}

// A private directory on the output filesystem makes the final rename atomic.
// Only files created by this instance are removed.
class Workspace {
    std::string directory_;
    std::vector<std::string> files_;
public:
    explicit Workspace(const std::string &output) {
        size_t slash = output.find_last_of('/');
        std::string parent = slash == std::string::npos ? "." :
            (slash == 0 ? "/" : output.substr(0, slash));
        std::string pattern = parent + "/.graph-tool-XXXXXX";
        std::vector<char> path(pattern.begin(), pattern.end()); path.push_back(0);
        char *made = mkdtemp(path.data());
        if (!made) fail("cannot create temporary directory: " + std::string(strerror(errno)));
        directory_ = made;
    }
    Workspace(const Workspace &) = delete;
    Workspace &operator=(const Workspace &) = delete;
    ~Workspace() {
        for (const std::string &p : files_) unlink(p.c_str());
        rmdir(directory_.c_str());
    }
    std::string file() {
        std::string p = directory_ + "/part-" + std::to_string(files_.size());
        files_.push_back(p); return p;
    }
};

class Lines {
    int fd_ = -1;
    pid_t child_ = -1;
    char buffer_[65536];
    size_t begin_ = 0, end_ = 0;
    bool eof_ = false;
public:
    U64 number = 0;
    std::string compression = "none";
    explicit Lines(const std::string &path) {
        std::string p = lower(path), program;
        if (ends(p, ".gz")) program = "gzip";
        else if (ends(p, ".bz2")) program = "bzip2";
        else if (ends(p, ".xz")) program = "xz";
        else if (ends(p, ".zip") || ends(p, ".7z"))
            fail("extract the archive first; supported compression: .gz/.bz2/.xz");
        int input = open(path.c_str(), O_RDONLY | O_CLOEXEC);
        if (input < 0) fail("cannot open input: " + std::string(strerror(errno)));
        if (program.empty()) { fd_ = input; return; }
        int pipes[2];
        if (pipe(pipes) != 0) { close(input); fail("pipe failed"); }
        child_ = fork();
        if (child_ < 0) {
            close(input); close(pipes[0]); close(pipes[1]); fail("fork failed");
        }
        if (child_ == 0) {
            if (dup2(input, STDIN_FILENO) < 0 || dup2(pipes[1], STDOUT_FILENO) < 0)
                _exit(126);
            close(input); close(pipes[0]); close(pipes[1]);
            execlp(program.c_str(), program.c_str(), "-dc", static_cast<char *>(nullptr));
            _exit(127);
        }
        close(input); close(pipes[1]); fd_ = pipes[0]; compression = program;
    }
    Lines(const Lines &) = delete;
    Lines &operator=(const Lines &) = delete;
    ~Lines() {
        if (fd_ >= 0) close(fd_);
        if (child_ > 0) {
            int status;
            while (waitpid(child_, &status, 0) < 0 && errno == EINTR) {}
        }
    }
    bool next(std::string &line) {
        line.clear();
        while (true) {
            if (begin_ == end_) {
                if (eof_) {
                    if (line.empty()) return false;
                    ++number; return true;
                }
                ssize_t count;
                do { count = read(fd_, buffer_, sizeof(buffer_)); }
                while (count < 0 && errno == EINTR);
                if (count < 0) fail("input read failed: " + std::string(strerror(errno)));
                begin_ = 0; end_ = size_t(count);
                if (count == 0) { eof_ = true; continue; }
            }
            const char *start = buffer_ + begin_;
            const char *nl = static_cast<const char *>(memchr(start, '\n', end_ - begin_));
            size_t count = nl ? size_t(nl - start) : end_ - begin_;
            if (memchr(start, 0, count)) fail("input contains NUL bytes; expected a text graph");
            line.append(start, count); begin_ += count;
            if (nl) { ++begin_; ++number; return true; }
        }
    }
    void finish() {
        if (!eof_) fail("internal error: input not fully consumed");
        close(fd_); fd_ = -1;
        if (child_ > 0) {
            int status = 0;
            pid_t result;
            do { result = waitpid(child_, &status, 0); } while (result < 0 && errno == EINTR);
            child_ = -1;
            if (result < 0 || !WIFEXITED(status) || WEXITSTATUS(status) != 0)
                fail("decompression failed (missing utility or corrupt compressed file)");
        }
    }
};

std::vector<std::string> tokens(std::string s) {
    size_t cut = s.size();
    for (const std::string marker : {"#", "%", "//"}) {
        size_t p = s.find(marker); if (p != std::string::npos) cut = std::min(cut, p);
    }
    s.resize(cut);
    std::replace(s.begin(), s.end(), ',', ' ');
    std::istringstream in(s);
    std::vector<std::string> t;
    std::string word;
    while (in >> word) t.push_back(word);
    return t;
}
long double weight(const std::string &s) {
    size_t count = 0;
    long double value;
    try { value = std::stold(s, &count); }
    catch (...) { fail("invalid numeric weight: " + s); }
    if (count != s.size() || !std::isfinite(value)) fail("invalid numeric weight: " + s);
    return value;
}
void close_checked(std::ofstream &out, const std::string &path) {
    out.close();
    if (!out) fail("write failed (possibly insufficient disk space): " + path);
}
bool read_key(std::ifstream &in, U64 &key) {
    in.read(reinterpret_cast<char *>(&key), sizeof(key));
    if (in.gcount() == 0 && in.eof()) return false;
    if (in.gcount() != sizeof(key) || !in) fail("temporary sorted run is truncated");
    return true;
}
struct HeapEntry { U64 key; size_t reader; };
struct Greater {
    bool operator()(const HeapEntry &a, const HeapEntry &b) const {
        return a.key > b.key || (a.key == b.key && a.reader > b.reader);
    }
};
template <class Emit>
void merge(const std::vector<std::string> &paths, Emit emit) {
    std::vector<std::unique_ptr<std::ifstream>> readers;
    std::priority_queue<HeapEntry, std::vector<HeapEntry>, Greater> heap;
    for (const std::string &p : paths) {
        readers.emplace_back(new std::ifstream(p, std::ios::binary));
        if (!*readers.back()) fail("cannot read sorted run: " + p);
        U64 k;
        if (read_key(*readers.back(), k)) heap.push({k, readers.size() - 1});
    }
    bool seen = false; U64 previous = 0;
    while (!heap.empty()) {
        HeapEntry e = heap.top(); heap.pop();
        if (!seen || e.key != previous) { emit(e.key); previous = e.key; seen = true; }
        U64 next;
        if (read_key(*readers[e.reader], next)) heap.push({next, e.reader});
    }
}
class Sorter {
    Workspace &workspace_;
    size_t capacity_;
    std::vector<U64> buffer_;
    std::vector<std::string> runs_;
    size_t fanin_;
public:
    Sorter(Workspace &w, U64 memory_mb) : workspace_(w) {
        capacity_ = size_t(memory_mb * 1024ull * 1024ull / sizeof(U64));
        if (capacity_ < 2 || capacity_ > buffer_.max_size()) fail("invalid sort buffer size");
        buffer_.reserve(capacity_);
        long descriptors = sysconf(_SC_OPEN_MAX);
        if (descriptors > 0 && descriptors < 20) fail("file descriptor limit is too small");
        fanin_ = size_t(descriptors > 0 ? std::min<long>(64, descriptors - 12) : 64);
    }
    void add(U64 key) {
        if (buffer_.size() == capacity_) flush();
        buffer_.push_back(key);
    }
    void flush() {
        if (buffer_.empty()) return;
        std::sort(buffer_.begin(), buffer_.end());
        auto last = std::unique(buffer_.begin(), buffer_.end());
        std::string path = workspace_.file();
        std::ofstream out(path, std::ios::binary);
        if (!out) fail("cannot write temporary run");
        out.write(reinterpret_cast<const char *>(buffer_.data()),
            std::streamsize((last - buffer_.begin()) * sizeof(U64)));
        close_checked(out, path);
        runs_.push_back(path); buffer_.clear();
    }
    template <class Emit> void finish(Emit emit) {
        // Small graphs do not need a disk sorting pass.
        if (runs_.empty()) {
            std::sort(buffer_.begin(), buffer_.end());
            auto last = std::unique(buffer_.begin(), buffer_.end());
            for (auto it = buffer_.begin(); it != last; ++it) emit(*it);
            return;
        }
        flush();
        std::vector<U64>().swap(buffer_);
        while (runs_.size() > fanin_) {
            std::vector<std::string> next;
            for (size_t i = 0; i < runs_.size(); i += fanin_) {
                size_t end = std::min(runs_.size(), i + fanin_);
                std::vector<std::string> group(runs_.begin() + i, runs_.begin() + end);
                if (group.size() == 1) { next.push_back(group[0]); continue; }
                std::string path = workspace_.file();
                std::ofstream out(path, std::ios::binary);
                if (!out) fail("cannot write merged run");
                merge(group, [&](U64 key) {
                    out.write(reinterpret_cast<const char *>(&key), sizeof(key));
                });
                close_checked(out, path);
                for (const std::string &p : group) unlink(p.c_str());
                next.push_back(path);
            }
            runs_.swap(next);
        }
        merge(runs_, emit);
        for (const std::string &p : runs_) unlink(p.c_str());
    }
};
class U32Writer {
    std::string path_;
    std::ofstream out_;
    std::vector<U32> buffer_;
public:
    explicit U32Writer(const std::string &path) : path_(path), out_(path, std::ios::binary) {
        if (!out_) fail("cannot write: " + path);
        buffer_.reserve(65536);
    }
    void add(U32 v) { buffer_.push_back(v); if (buffer_.size() == 65536) flush(); }
    void zeros(U64 count) {
        while (count) {
            size_t take = size_t(std::min<U64>(count, 65536 - buffer_.size()));
            buffer_.insert(buffer_.end(), take, 0);
            count -= take;
            if (buffer_.size() == 65536) flush();
        }
    }
    void flush() {
        if (!buffer_.empty())
            out_.write(reinterpret_cast<const char *>(buffer_.data()),
                std::streamsize(buffer_.size() * sizeof(U32)));
        if (!out_) fail("write failed: " + path_);
        buffer_.clear();
    }
    void finish() { flush(); close_checked(out_, path_); }
};
void copy_file(const std::string &path, std::ofstream &out) {
    std::ifstream in(path, std::ios::binary);
    if (!in) fail("cannot read temporary file");
    std::vector<char> buffer(1024 * 1024);
    while (in) {
        in.read(buffer.data(), std::streamsize(buffer.size()));
        out.write(buffer.data(), in.gcount());
        if (!out) fail("output write failed");
    }
    if (!in.eof()) fail("temporary file read failed");
}
void check_destination(const std::string &path, const Options &o, const struct stat &input) {
    struct stat st;
    if (lstat(path.c_str(), &st) == 0) {
        if (st.st_dev == input.st_dev && st.st_ino == input.st_ino)
            fail("refusing to overwrite the input: " + path);
        if (!o.force) fail("output exists; use --force to replace it: " + path);
        if (!S_ISREG(st.st_mode)) fail("output is not a regular file: " + path);
    } else if (errno != ENOENT) fail("cannot inspect output: " + path);
}
void publish(const std::string &from, const std::string &to,
             const Options &o, const struct stat &input) {
    check_destination(to, o, input);
    if (o.force) {
        if (rename(from.c_str(), to.c_str()) != 0) fail("cannot publish: " + to);
    } else {
        // link is an atomic no-clobber publication on the same filesystem.
        if (link(from.c_str(), to.c_str()) != 0)
            fail("cannot publish output without overwriting: " + to);
        if (unlink(from.c_str()) != 0) fail("cannot unlink published temporary file");
    }
}
void convert(Options o) {
    struct stat input;
    if (stat(o.input.c_str(), &input) != 0 || !S_ISREG(input.st_mode))
        fail("input must be a readable regular text/compressed file");
    std::string metadata_path = o.output + ".meta.json";
    std::string mapping_path = o.output + ".ids.tsv";
    check_destination(o.output, o, input);
    check_destination(metadata_path, o, input);
    if (o.relabel) check_destination(mapping_path, o, input);
    else {
        struct stat old_map;
        if (lstat(mapping_path.c_str(), &old_map) == 0)
            fail("an ID mapping already exists for this output; choose a new output path");
    }
    Workspace workspace(o.output);
    Lines lines(o.input);
    Sorter sorter(workspace, o.memory_mb);
    std::unordered_map<U64, U32> labels;
    std::string mapping_temp;
    std::ofstream mapping;
    if (o.relabel) {
        mapping_temp = workspace.file(); mapping.open(mapping_temp);
        if (!mapping) fail("cannot create ID mapping");
        mapping << "original_id\tinternal_id\n";
    }
    U64 n = o.vertices_set ? o.vertices : 0;
    U64 records = 0, loops = 0, zeros = 0, weighted = 0;
    U64 declared_records = 0;
    bool declared = false, matrix = false, dimensions_read = false;
    std::string matrix_field, matrix_symmetry, line;
    bool format_selected = false;
    for (U64 i = 0; i < o.skip_lines; ++i)
        if (!lines.next(line)) fail("--skip-lines exceeds input length");

    auto vertex = [&](U64 original) -> U32 {
        if (o.relabel) {
            auto it = labels.find(original);
            if (it != labels.end()) return it->second;
            if (labels.size() >= MAX_VERTICES) fail("too many vertices for ARC-SCS");
            U32 id = U32(labels.size());
            labels.emplace(original, id);
            mapping << original << '\t' << id << '\n';
            if (!mapping) fail("ID mapping write failed");
            n = labels.size();
            return id;
        }
        U64 base = matrix ? 1 : o.base;
        if (original < base) fail("vertex ID is below the configured ID base");
        U64 id = original - base;
        if (id >= MAX_VERTICES) fail("vertex ID exceeds uint32 range; use --relabel for sparse IDs");
        if (declared || o.vertices_set) {
            if (id >= n) fail("vertex ID is outside the declared vertex range");
        } else n = std::max(n, id + 1);
        return U32(id);
    };
    while (lines.next(line)) {
        try {
            size_t first = line.find_first_not_of(" \t\r");
            if (first == std::string::npos) continue;
            bool magic = line.compare(first, 14, "%%MatrixMarket") == 0;
            if (!format_selected) {
                if (magic) {
                    if (o.format != "auto" && o.format != "mtx")
                        fail("Matrix Market header conflicts with --format");
                    if (o.skip_lines) fail("--skip-lines is not valid for Matrix Market");
                    if (o.relabel || o.base_set)
                        fail("MTX preserves its declared vertices and 1-based IDs; do not use --relabel/--id-base");
                    std::istringstream header(line.substr(first));
                    std::string signature, object, storage, extra;
                    header >> signature >> object >> storage >> matrix_field >> matrix_symmetry;
                    matrix_field = lower(matrix_field); matrix_symmetry = lower(matrix_symmetry);
                    if (lower(object) != "matrix" || lower(storage) != "coordinate" ||
                        (matrix_field != "pattern" && matrix_field != "real" && matrix_field != "integer") ||
                        (matrix_symmetry != "general" && matrix_symmetry != "symmetric") ||
                        (header >> extra))
                        fail("supported MTX: square coordinate pattern/real/integer, general/symmetric");
                    if (matrix_field != "pattern" && !o.ignore_weights)
                        fail("weighted MTX requires --ignore-weights");
                    matrix = true; o.format = "mtx"; format_selected = true; continue;
                }
                auto t = tokens(line);
                if (t.empty()) continue;
                if (o.format == "mtx") fail("missing %%MatrixMarket header");
                if (o.format == "auto") o.format = "edge-list";
                if (o.relabel && o.format == "headered")
                    fail("--relabel is only supported for edge lists without a vertex-count header");
                format_selected = true;
            }
            auto t = tokens(line);
            if (t.empty()) continue;
            if (!dimensions_read && (matrix || o.format == "headered")) {
                if (t.size() != (matrix ? 3u : 2u)) fail("invalid dimension/edge-count header");
                n = integer(t[0]);
                if (matrix && integer(t[1]) != n)
                    fail("rectangular MTX is not a simple graph; explicitly export a bipartite edge list");
                declared_records = integer(t[matrix ? 2 : 1]);
                if (n == 0 || n > MAX_VERTICES) fail("unsupported vertex count in header");
                if (o.vertices_set && n != o.vertices) fail("--vertices disagrees with header");
                declared = true; dimensions_read = true; continue;
            }
            if (t.size() != 2 && t.size() != 3) fail("expected two endpoint columns and an optional weight");
            if (matrix && t.size() != (matrix_field == "pattern" ? 2u : 3u))
                fail("entry columns do not match MTX field");
            U64 a = integer(t[0]), b = integer(t[1]);
            ++records;
            if (declared && records > declared_records) fail("more entries than declared in header");
            U32 u = vertex(a), v = vertex(b); // Includes vertices appearing only in loops.
            bool zero_entry = false;
            if (t.size() == 3) {
                if (!o.ignore_weights) fail("weighted edge list requires --ignore-weights");
                long double w = weight(t[2]); ++weighted;
                zero_entry = matrix && w == 0; // Explicit matrix zero is not an adjacency.
            }
            if (zero_entry) { ++zeros; continue; }
            if (u == v) { ++loops; continue; }
            sorter.add((U64(u) << 32) | v);
            sorter.add((U64(v) << 32) | u);
        } catch (const std::exception &e) {
            fail("input line " + std::to_string(lines.number) + ": " + e.what());
        }
    }
    lines.finish();
    if (matrix && !dimensions_read) fail("MTX dimensions are missing");
    if (o.format == "headered" && !dimensions_read) fail("edge-list header is missing");
    if (declared && records != declared_records) fail("fewer entries than declared in header");
    if (n == 0) fail("no vertices found; use --vertices for an edge-free graph");
    if (o.format == "auto") o.format = "edge-list";
    if (mapping.is_open()) close_checked(mapping, mapping_temp);
    labels.clear(); labels.rehash(0);

    std::string degree_temp = workspace.file(), adjacency_temp = workspace.file();
    U32Writer degrees(degree_temp), adjacency(adjacency_temp);
    U64 row = 0, row_degree = 0, entries = 0, nonisolated = 0;
    sorter.finish([&](U64 key) {
        U64 u = key >> 32; U32 v = U32(key);
        if (u != row) {
            degrees.add(U32(row_degree));
            if (row_degree) ++nonisolated;
            degrees.zeros(u - row - 1);
            row = u; row_degree = 0;
        }
        if (++entries > MAX_ENTRIES) fail("directed adjacency count exceeds ARC-SCS uint32 format");
        ++row_degree;
        adjacency.add(v);
    });
    degrees.add(U32(row_degree));
    if (row_degree) ++nonisolated;
    degrees.zeros(n - row - 1);
    degrees.finish(); adjacency.finish();
    if (entries % 2) fail("internal error: asymmetric directed edge count");
    U64 edge_count = entries / 2;
    if (records - zeros - loops < edge_count) fail("internal error: invalid edge accounting");
    U64 duplicates = records - zeros - loops - edge_count;

    std::string binary_temp = workspace.file();
    std::ofstream binary(binary_temp, std::ios::binary);
    if (!binary) fail("cannot create graph output");
    U32 header[] = {4, U32(n), U32(entries)};
    binary.write(reinterpret_cast<const char *>(header), sizeof(header));
    copy_file(degree_temp, binary); copy_file(adjacency_temp, binary);
    close_checked(binary, binary_temp);
    struct stat produced;
    U64 expected_bytes = 12 + 4 * (n + entries);
    if (stat(binary_temp.c_str(), &produced) != 0 || U64(produced.st_size) != expected_bytes)
        fail("internal error: graph file size mismatch");

    std::string meta_temp = workspace.file();
    std::ofstream meta(meta_temp);
    if (!meta) fail("cannot create metadata");
    U32 one = 1;
    const bool little = *reinterpret_cast<unsigned char *>(&one) == 1;
    meta << "{\n"
         << "  \"schema\": \"arc-scs-graph-conversion-v1\",\n"
         << "  \"input\": " << json(o.input) << ",\n"
         << "  \"output\": " << json(o.output) << ",\n"
         << "  \"input_format\": " << json(o.format) << ",\n"
         << "  \"compression\": " << json(lines.compression) << ",\n"
         << "  \"input_file_bytes\": " << input.st_size << ",\n"
         << "  \"input_records\": " << records << ",\n"
         << "  \"header_declares_vertices\": " << (declared ? "true" : "false") << ",\n"
         << "  \"vertices\": " << n << ",\n"
         << "  \"undirected_edges\": " << edge_count << ",\n"
         << "  \"directed_entries\": " << entries << ",\n"
         << "  \"isolated_vertices\": " << n - nonisolated << ",\n"
         << "  \"removed_self_loop_records\": " << loops << ",\n"
         << "  \"removed_zero_matrix_records\": " << zeros << ",\n"
         << "  \"duplicate_nonloop_records\": " << duplicates << ",\n"
         << "  \"ignored_weight_records\": " << weighted << ",\n"
         << "  \"relabel\": " << (o.relabel ? "true" : "false") << ",\n"
         << "  \"input_id_base\": " << (matrix ? 1 : o.base) << ",\n"
         << "  \"id_mapping\": " << (o.relabel ? json(mapping_path) : "null") << ",\n"
         << "  \"undirected_symmetrization\": true,\n"
         << "  \"adjacency_sorted\": true,\n"
         << "  \"integer_bytes\": 4,\n"
         << "  \"byte_order\": " << json(little ? "little" : "big") << ",\n"
         << "  \"output_bytes\": " << expected_bytes << ",\n"
         << "  \"sort_memory_mb\": " << o.memory_mb << "\n}\n";
    close_checked(meta, meta_temp);
    // The graph is published last, only after complete input/decompression,
    // sorted CSR, mapping and metadata have all been successfully written.
    if (o.relabel) publish(mapping_temp, mapping_path, o, input);
    publish(meta_temp, metadata_path, o, input);
    publish(binary_temp, o.output, o, input);
    std::cout << "[GraphTool] vertices=" << n << " undirected_edges=" << edge_count
              << " directed_entries=" << entries << " isolated_vertices=" << n - nonisolated << '\n'
              << "[GraphTool] input_records=" << records << " self_loops_removed=" << loops
              << " duplicate_records=" << duplicates << " zero_matrix_records=" << zeros << '\n'
              << "[GraphTool] output=" << o.output << " metadata=" << metadata_path << '\n';
    if (o.relabel) std::cout << "[GraphTool] id_mapping=" << mapping_path << '\n';
}
} // namespace
int main(int argc, char **argv) {
    try { convert(options(argc, argv)); return 0; }
    catch (const std::exception &e) {
        std::cerr << "[GraphTool][Error] " << e.what() << '\n';
        return 1;
    }
}
