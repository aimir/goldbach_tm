// Bounded repair search for a quotient of the current 24-state table.
// The same phase checker is exposed to the optional counterexample-guided solver.
#define MACHINE_STATES 24
#include "phase_screen.hpp"
#include <algorithm>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

static Machine baseline;
static std::vector<Fixture> fixtures;
static unsigned long long evaluations = 0;

// Failure traces justify pruning: changing no visited branch repeats the failure.
// A bootstrap failure unions all possible initial-state traces, since any one
// successful initial state would suffice. A successful return supplies its state.
static int failure(const Machine &m, int dead, int keep, std::uint64_t &trace) {
    for (int i = 0; i < int(fixtures.size()); ++i) {
        if (!run(m, dead, keep, fixtures[i])) {
            trace = visited;
            return i;
        }
    }
    trace = 0;
    for (int start = 0; start < MACHINE_STATES; ++start) {
        if (start == dead) continue;
        if (run(m, dead, keep, Fixture{0, 0, 0, true, 45}, 3, start)) {
            trace = start;
            return -1;
        }
        trace |= visited;
    }
    return fixtures.size();
}

extern "C" void initialize(const int *data, int n) {
    fixtures.clear();
    for (int i = 0; i < n; ++i)
        fixtures.push_back(Fixture{data[5*i], data[5*i+1], data[5*i+2],
                                   bool(data[5*i+3]), data[5*i+4]});
}

// Edge 0 is HALT; other values encode target, write bit and direction.
extern "C" int check(const int *data, int dead, int keep, std::uint64_t *trace) {
    Machine m;
    for (int i = 0; i < 48; ++i) {
        int x = data[i];
        m[i/2][i%2] = x == 0 ? Edge{0, 0, -1} :
            Edge{((x-1)%4)/2, ((x-1)%2) ? 1 : -1, (x-1)/4};
    }
    steps_run = 0;
    return failure(m, dead, keep, *trace);
}
extern "C" long long last_steps() { return steps_run; }

static std::string key(const Machine &m, int dead, int start) {
    std::string result(1, char(start - (start > dead)));
    for (int q = 0; q < 24; ++q) if (q != dead) {
        for (auto e : m[q]) {
            result.push_back(e.w + 1);
            result.push_back(e.d + 1);
            result.push_back(e.q < 0 ? 0 : e.q - (e.q > dead) + 1);
        }
    }
    return result;
}

static void save(const Machine &m, int dead, int keep, int start,
                 const std::string &path) {
    std::ofstream out(path);
    if (!out) throw std::runtime_error("Cannot write candidate: " + path);
    out << "{\"removed\":" << dead << ",\"merged_into\":" << keep
        << ",\"start\":" << start << ",\"table\":[";
    for (int q = 0; q < 24; ++q) {
        if (q) out << ',';
        out << '[';
        for (int b = 0; b < 2; ++b) {
            if (b) out << ',';
            auto e = m[q][b];
            out << '[' << e.w << ',' << e.d << ',' << e.q << ']';
        }
        out << ']';
    }
    out << "]}\n";
}

class Search {
    int dead, keep;
    std::string output;
    std::unordered_set<std::string> &found;
    std::vector<Edge> edges{{0, 0, -1}};
public:
    Search(int d, int k, const std::string &o, std::unordered_set<std::string> &f)
        : dead(d), keep(k), output(o), found(f) {
        for (int t = 0; t < 24; ++t) if (t != dead)
            for (int w = 0; w < 2; ++w)
                for (int move : {-1, 1}) edges.push_back(Edge{w, move, t});
    }
    void visit(Machine &m, int remaining, std::uint64_t edited = 0) {
        ++evaluations;
        std::uint64_t trace;
        int fail = failure(m, dead, keep, trace);
        if (fail < 0) {
            int start = trace;
            if (found.insert(key(m, dead, start)).second) {
                save(m, dead, keep, start, output + "/candidate-" +
                     std::to_string(found.size()) + ".json");
                std::cout << "Finite survivor " << found.size() << ": remove "
                          << dead << ", start " << start << std::endl;
            }
            return;
        }
        if (!remaining) return;
        for (int branch = 0; branch < 48; ++branch) {
            if (branch/2 == dead || !(trace >> branch & 1) || (edited >> branch & 1)) continue;
            auto old = m[branch/2][branch%2];
            for (auto e : edges) if (!(e == old)) {
                m[branch/2][branch%2] = e;
                visit(m, remaining-1, edited | (1ULL << branch));
            }
            m[branch/2][branch%2] = old;
        }
    }
};

#ifndef SCREEN_LIBRARY
int main(int argc, char **argv) {
    if (argc != 4) return 2;
    std::string output = argv[1], groups = argv[3];
    int repairs = std::stoi(argv[2]);
    if ((repairs != 1 && repairs != 2) || (groups != "scans" && groups != "all")) return 2;
    for (auto &row : baseline) for (auto &e : row)
        if (!(std::cin >> e.w >> e.d >> e.q)) return 2;
    int core_count, total;
    std::cin >> core_count >> total;
    for (int i = 0; i < total; ++i) {
        Fixture f;
        std::cin >> f.kind >> f.n >> f.p >> f.success >> f.baseline_steps;
        fixtures.push_back(f);
    }
    std::uint64_t trace;
    if (failure(baseline, -1, -1, trace) >= 0) {
        std::cerr << "Baseline fixtures failed\n";
        return 2;
    }
    steps_run = 0;
    std::vector<std::pair<int, int>> pairs;
    if (groups == "scans") {
        for (auto group : std::vector<std::vector<int>>{{13,14,16,18,20,22},{11,19,21},{5,7,8}})
            for (int d : group) for (int k : group) if (d != k) pairs.push_back({d,k});
    } else {
        for (int d = 0; d < 24; ++d)
            for (int k = 0; k < 24; ++k) if (d != k) pairs.push_back({d,k});
    }
    std::unordered_set<std::string> found;
    for (auto [dead, keep] : pairs) {
        Machine m = baseline;
        for (auto &row : m) for (auto &e : row) if (e.q == dead) e.q = keep;
        Search(dead, keep, output, found).visit(m, repairs);
    }
    std::ofstream report(output + "/summary.json");
    if (!report) return 2;
    report << "{\"ordered_pairs\":" << pairs.size() << ",\"repairs\":" << repairs
           << ",\"evaluations\":" << evaluations << ",\"simulated_steps\":" << steps_run
           << ",\"fixtures\":" << total << ",\"distinct_finite_survivors\":" << found.size() << "}\n";
    std::cout << "Finished " << evaluations << " evaluations; " << found.size()
              << " distinct finite survivors." << std::endl;
}
#endif
