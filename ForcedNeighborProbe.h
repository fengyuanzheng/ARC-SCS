#ifndef ARC_SCS_FORCED_NEIGHBOR_PROBE_H
#define ARC_SCS_FORCED_NEIGHBOR_PROBE_H
#include <algorithm>
#include <cstdint>
#include <vector>
#include <utility>

// A bounded exact probe. Infeasible is returned only after every branch is
// certified; any resource or representation limit returns Unknown.
namespace arc_forced_neighbor {
enum Verdict { Unknown, Infeasible, Found };
struct Result {
    Verdict verdict = Unknown;
    std::vector<unsigned> witness;
    unsigned long long nodes = 0, edge_visits = 0, capacity_prunes = 0;
};
template<class Offset> class Probe {
    struct Constraint {
        unsigned vertex, deficit;
        std::vector<unsigned> candidates;
    };
    unsigned n_, query_, lower_, upper_, target_;
    const Offset *start_;
    const unsigned *edges_, *core_;
    unsigned long long node_cap_, edge_cap_, nodes_ = 0, visits_ = 0, prunes_ = 0;
    bool stopped_ = false, complete_sizes_ = false;
    unsigned recursion_depth_ = 0;
    unsigned order_mode_ = 0;
    std::vector<unsigned> query_twin_class_;
    std::vector<unsigned char> state_, support_;
    std::vector<unsigned> forced_, trail_, stamps_, pattern_stamps_;
    std::vector<unsigned short> patterns_;
    unsigned epoch_ = 0, pattern_epoch_ = 0;
    std::vector<unsigned> witness_;

    bool charge(Offset length) {
        visits_ += (unsigned long long)length;
        if (visits_ > edge_cap_) stopped_ = true;
        return !stopped_;
    }
    void set(unsigned v, unsigned char value) {
        state_[v] = value; trail_.push_back(v);
        if (value == 1) forced_.push_back(v);
    }
    void undo(size_t ts, size_t fs) {
        while (trail_.size() > ts) {
            state_[trail_.back()] = 0; trail_.pop_back();
        }
        forced_.resize(fs);
    }
    Verdict search() {
        if (complete_sizes_ && recursion_depth_ >= 256u) { stopped_ = true; return Unknown; }
        const size_t ts = trail_.size(), fs = forced_.size();
        ++recursion_depth_;
        Verdict result = visit();
        --recursion_depth_;
        undo(ts, fs);
        return result;
    }

    Verdict branch_vertex(unsigned selected) {
        const size_t ts = trail_.size(), fs = forced_.size();
        set(selected, 1);
        Verdict include = search();
        undo(ts, fs);
        if (include == Found) return Found;
        if (stopped_) return Unknown;
        set(selected, 2);
        Verdict exclude = search();
        undo(ts, fs);
        if (exclude == Found) return Found;
        return include == Unknown || exclude == Unknown ? Unknown : Infeasible;
    }

    // Enumerate exact membership in N(v). All subsets with at least the
    // remaining degree deficit are covered; omissions become forbidden.
    Verdict combinations(const std::vector<unsigned> &c, unsigned pos,
                         unsigned needed, std::vector<unsigned> &chosen) {
        if (stopped_) return Unknown;
        if (needed == 0u) {
            const size_t ts = trail_.size(), fs = forced_.size();
            size_t cursor = 0;
            for (unsigned i = 0; i < c.size(); ++i) {
                bool take = cursor < chosen.size() && chosen[cursor] == i;
                if (take) ++cursor;
                set(c[i], take ? 1 : 2);
            }
            Verdict r = search();
            undo(ts, fs);
            return r;
        }
        bool unknown = false;
        for (unsigned i = pos; i + needed <= c.size(); ++i) {
            bool equivalent_choice = false;
            if ((order_mode_ & 32u) && query_twin_class_[c[i]]) {
                for (unsigned j = pos; j < i; ++j)
                    if (query_twin_class_[c[j]] == query_twin_class_[c[i]]) {
                        equivalent_choice = true; break;
                    }
            }
            if (equivalent_choice) continue;
            chosen.push_back(i);
            Verdict r = combinations(c, i + 1, needed - 1, chosen);
            chosen.pop_back();
            if (r == Found) return Found;
            if (r == Unknown) unknown = true;
            if (stopped_) return Unknown;
        }
        return unknown ? Unknown : Infeasible;
    }
    Verdict visit() {
        if (stopped_ || ++nodes_ > node_cap_) {
            stopped_ = true; return Unknown;
        }
        std::vector<Constraint> constraints;
        for (;;) {
            if (forced_.size() > upper_) return Infeasible;
            unsigned room = upper_ - (unsigned)forced_.size();
            if (++epoch_ == 0u) {
                std::fill(stamps_.begin(), stamps_.end(), 0); ++epoch_;
            }
            std::vector<unsigned> inside(forced_.size(), 0);
            // For any selected future vertex u, d_F(u)+room-1 >= k is
            // necessary. This does not assume anything about the unchosen
            // vertices or about edges among them.
            for (size_t i = 0; i < forced_.size(); ++i) {
                unsigned v = forced_[i];
                if (!charge(start_[v + 1] - start_[v])) return Unknown;
                for (Offset e = start_[v]; e < start_[v + 1]; ++e) {
                    unsigned u = edges_[e];
                    if (state_[u] == 1) ++inside[i];
                    if ((room <= target_ || (order_mode_ & 16u)) && state_[u] == 0 && core_[u] >= target_) {
                        if (stamps_[u] != epoch_) {
                            stamps_[u] = epoch_; support_[u] = 0;
                        }
                        ++support_[u];
                    }
                }
            }
            constraints.clear();
            std::vector<unsigned> mandatory;
            for (size_t i = 0; i < forced_.size(); ++i) {
                if (inside[i] >= target_) continue;
                Constraint c;
                c.vertex = forced_[i]; c.deficit = target_ - inside[i];
                if (c.deficit > room) return Infeasible;
                if (!charge(start_[c.vertex + 1] - start_[c.vertex])) return Unknown;
                for (Offset e = start_[c.vertex]; e < start_[c.vertex + 1]; ++e) {
                    unsigned u = edges_[e];
                    if (state_[u] || core_[u] < target_) continue;
                    if (room <= target_ &&
                        (stamps_[u] != epoch_ || (unsigned)support_[u] + room <= target_))
                        continue;
                    c.candidates.push_back(u);
                }
                if (c.candidates.size() < c.deficit) return Infeasible;
                if (c.candidates.size() == c.deficit)
                    mandatory.insert(mandatory.end(), c.candidates.begin(), c.candidates.end());
                if (order_mode_ & 17u)
                    std::stable_sort(c.candidates.begin(), c.candidates.end(), [&](unsigned a,unsigned b) {
                        if ((order_mode_ & 16u) && support_[a] != support_[b]) return support_[a] > support_[b];
                        return (order_mode_ & 1u) && start_[a+1]-start_[a] > start_[b+1]-start_[b];
                    });
                constraints.push_back(std::move(c));
            }
            if (mandatory.empty()) break;
            for (unsigned u : mandatory) if (!state_[u]) set(u, 1);
        }
        if (constraints.empty()) {
            if (forced_.size() >= lower_) {
                witness_ = forced_;
                return Found;
            }
            if (!complete_sizes_) return Unknown;
            // A connected feasible completion must select a vertex on the
            // boundary of the current connected forced set. Degree satisfaction
            // alone does not certify infeasibility when |F| is below L.
            if (forced_.size() >= upper_) return Infeasible;
            if (++epoch_ == 0u) {
                std::fill(stamps_.begin(), stamps_.end(), 0); ++epoch_;
            }
            std::vector<unsigned> boundary;
            for (unsigned v : forced_) {
                if (!charge(start_[v + 1] - start_[v])) return Unknown;
                for (Offset e = start_[v]; e < start_[v + 1]; ++e) {
                    unsigned u = edges_[e];
                    if (state_[u] || core_[u] < target_) continue;
                    if (stamps_[u] != epoch_) {
                        stamps_[u] = epoch_; support_[u] = 0;
                        boundary.push_back(u);
                    }
                    ++support_[u];
                }
            }
            if (boundary.empty()) return Infeasible;
            unsigned selected = boundary[0];
            for (unsigned u : boundary) {
                if (support_[u] > support_[selected] ||
                    (support_[u] == support_[selected] &&
                     start_[u + 1] - start_[u] < start_[selected + 1] - start_[selected]))
                    selected = u;
            }
            if (order_mode_ & 2u)
                for (unsigned u : boundary)
                    if (start_[u+1]-start_[u] > start_[selected+1]-start_[selected])
                        selected = u;
            return branch_vertex(selected);
        }
        unsigned room = upper_ - (unsigned)forced_.size();
        std::sort(constraints.begin(), constraints.end(),
                  [](const Constraint &a, const Constraint &b) {
                      return a.candidates.size() != b.candidates.size()
                          ? a.candidates.size() < b.candidates.size()
                          : a.vertex < b.vertex;
                  });
        // A subset of up to eight tight constraints suffices for a safe
        // capacity inequality. Ignoring other constraints only weakens it.
        unsigned count = std::min<unsigned>(8, constraints.size());
        if (++pattern_epoch_ == 0u) {
            std::fill(pattern_stamps_.begin(), pattern_stamps_.end(), 0); ++pattern_epoch_;
        }
        unsigned histogram[256] = {};
        for (unsigned i = 0; i < count; ++i) {
            for (unsigned u : constraints[i].candidates) {
                if (pattern_stamps_[u] != pattern_epoch_) {
                    pattern_stamps_[u] = pattern_epoch_; patterns_[u] = 0;
                }
                patterns_[u] |= (1u << i);
            }
        }
        // Count each candidate once, including vertices shared by constraints.
        for (unsigned i = 0; i < count; ++i) {
            for (unsigned u : constraints[i].candidates) {
                if (pattern_stamps_[u] == pattern_epoch_) {
                    ++histogram[patterns_[u]];
                    pattern_stamps_[u] = 0;
                }
            }
        }
        for (unsigned mask = 1; mask < (1u << count); ++mask) {
            unsigned demand = 0, coverage[9] = {};
            for (unsigned i = 0; i < count; ++i)
                if ((mask >> i) & 1u) demand += constraints[i].deficit;
            for (unsigned pattern = 1; pattern < (1u << count); ++pattern)
                coverage[__builtin_popcount(pattern & mask)] += histogram[pattern];
            unsigned left = room, capacity = 0;
            for (unsigned cover = count; cover && left; --cover) {
                unsigned take = std::min(left, coverage[cover]);
                capacity += take * cover; left -= take;
            }
            if (demand > capacity) { ++prunes_; return Infeasible; }
        }
        const Constraint &c = constraints.front();
        if (c.candidates.size() > 16) {
            if (!complete_sizes_) return Unknown;
            unsigned selected = c.candidates.front();
            for (unsigned u : c.candidates)
                if ((order_mode_ & 16u) && support_[u] != support_[selected]
                        ? support_[u] > support_[selected]
                        : ((order_mode_ & 8u)
                            ? start_[u + 1] - start_[u] > start_[selected + 1] - start_[selected]
                            : start_[u + 1] - start_[u] < start_[selected + 1] - start_[selected]))
                    selected = u;
            return branch_vertex(selected);
        }
        bool unknown = false;
        std::vector<unsigned> chosen;
        for (unsigned offset = 0, maximum = std::min<unsigned>(room, c.candidates.size()); offset <= maximum - c.deficit; ++offset) {
            const unsigned take = (order_mode_ & 4u) ? maximum - offset : c.deficit + offset;
            Verdict r = combinations(c.candidates, 0, take, chosen);
            if (r == Found) return Found;
            if (r == Unknown) unknown = true;
            if (stopped_) return Unknown;
        }
        return unknown ? Unknown : Infeasible;
    }
public:
    Probe(unsigned n, const Offset *start, const unsigned *edges, const unsigned *core,
          unsigned query, unsigned lower, unsigned upper, unsigned target,
          unsigned long long node_cap = 250000, unsigned long long edge_cap = 250000000,
          bool complete_sizes = false, unsigned order_mode = 0)
        : n_(n), query_(query), lower_(lower), upper_(upper), target_(target),
          start_(start), edges_(edges), core_(core), node_cap_(node_cap), edge_cap_(edge_cap),
          state_(n, 0), support_(n, 0), stamps_(n, 0), pattern_stamps_(n, 0), patterns_(n, 0) {
        complete_sizes_ = complete_sizes; order_mode_ = order_mode;
    }
    Result run() {
        Result out;
        if (!target_ || query_ >= n_ || !lower_ || lower_ > upper_ || upper_ > 28u) return out;
        if (core_[query_] < target_) { out.verdict = Infeasible; return out; }
        if (order_mode_ & 32u) {
            // Equal closed neighborhoods define exact true twins. Swapping two
            // undecided twins preserves every edge, the fixed query, and size.
            // Keep one representative per equivalent membership combination.
            query_twin_class_.assign(n_,0u);
            std::vector<std::vector<unsigned>> signatures;
            for (Offset e = start_[query_]; e < start_[query_+1]; ++e) {
                const unsigned v = edges_[e];
                if (core_[v] < target_) continue;
                if (!charge(start_[v+1]-start_[v])) { out.edge_visits=visits_; return out; }
                std::vector<unsigned> closed(edges_+start_[v],edges_+start_[v+1]);
                closed.push_back(v);std::sort(closed.begin(),closed.end());
                unsigned group=0;
                while(group<signatures.size() && signatures[group]!=closed)++group;
                if(group==signatures.size())signatures.push_back(std::move(closed));
                query_twin_class_[v]=group+1u;
            }
        }
        set(query_, 1);
        out.verdict = search(); out.witness = witness_;
        out.nodes = nodes_; out.edge_visits = visits_; out.capacity_prunes = prunes_;
        return out;
    }
};
}
#endif
