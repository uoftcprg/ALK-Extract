#ifndef SEMANTIC_ALK_HPP
#define SEMANTIC_ALK_HPP

// Semantic detection of cardinality constraints.
//
// The Encoded_ALK engine guesses which variables are auxiliary from the shape of
// the clauses around them (blocking-set counts, clause lengths, the outline of a
// totalizer tree). This engine uses three facts that hold for every encoding:
//
//  1. An encoding touches the rest of the formula only through the literals it
//     counts. Cut the formula at the counted variables and the auxiliary
//     variables of the encoding fall off as a connected piece of their own.
//  2. "At most k of L" means: make any k literals of L true and the others are
//     forced false. Unit propagation shows such sets without knowing how they
//     are encoded.
//  3. Whether a piece of the formula says exactly "at most k of L" is a question
//     for a SAT solver: no assignment with k+1 true literals satisfies it, and
//     every assignment that the constraint allows can be extended to it.
//
// A candidate is replaced by a klause only after check 3. Every verified
// constraint tells which variables are problem variables, and the formula is
// cut again at those (1) until nothing new is found.
//
// Two stages produce candidates:
//
//   cut    components of the variables that are not known to be problem
//          variables, each with the problem variables it touches. Problem
//          variables are known from klauses that were already extracted and
//          from clauses with more than `big_clause` literals.
//   prop   sets of literals that exclude each other under unit propagation
//          (bounds 1 .. max_bound). The clauses of such a set are the pieces
//          that fall off when the formula is cut at it, plus the clauses over
//          the set itself that the constraint implies (an encoding without
//          auxiliary variables consists of those alone).
//
// The clauses of one encoding can often be read as more than one constraint
// (the first output of a counter can be counted in place of the input that
// switches it on, for example). All readings that pass check 3 are collected,
// each variable gets a vote for every reading that counts it, and the readings
// with the most votes per counted literal are replaced first: a problem
// variable is counted wherever the clauses around it are probed, an auxiliary
// variable only where an encoding is cut short.
//
// What the engine does not use: variable numbers (other than to break ties in
// the order of work), the order of clauses or literals, comments, or any
// pattern of a particular encoding.

#include <climits>
#include <random>
#include <unordered_set>

#include "cnf2knf.hpp"

namespace cnf2knf {

using namespace std;

class Semantic_ALK : public Extraction_engine {

public:

  using Extraction_engine::Extraction_engine;

  // ---------------------------------------------------------------- options
  int  min_data_vars;      // a constraint has more counted literals than this
  int  max_bound;          // largest bound that the propagation stage proposes
  int  big_clause;         // variables of a clause longer than this are problem variables
  long exhaustive_limit;   // this many assignments at the bound are all checked ...
  int  nsamples;           // ... beyond that, this many random ones
  int  conflict_limit;     // per SAT call (a call that runs into it rejects the candidate)
  int  upper_limit;        // the same for the one call that proves the bound
  int  extend_limit;       // and for a call that extends a full assignment of the counted literals
                           // (in an encoding this is a matter of propagation)
  int  pool_limit;         // largest set of rivals that is looked at for one seed
  long subset_limit;       // most k-subsets probed when a set of rivals is refined
  bool stage_cut, stage_prop;
  int  direct_bound;       // constraints without an auxiliary variable are replaced from this bound on

  // ---------------------------------------------------------------- counters
  int  n_cut, n_prop, n_direct;       // constraints per stage; n_direct: without an auxiliary variable
  long n_candidates, n_sat_calls, n_probes;
  int  n_all_checked, n_sampled;      // constraints whose assignments at the bound were all checked / sampled
  int  rounds;
  double stage_end;        // the running stage stops at this time (seconds since the start) ...
  long probe_end;          // ... or at this number of probes
  long probes_per_clause;  // probes that a propagation stage with a bound above 1 may spend per clause
  bool stage_timeout;      // a propagation stage ran out of its share of the time or of its probes

  void init (unordered_map<string, string> engine_options) {
    auto get = [&] (const char *key, long dflt) {
      auto it = engine_options.find (key);
      return it == engine_options.end () ? dflt : stol (it->second);
    };
    min_data_vars    = get ("semantic_min_data_vars", 2);
    max_bound        = get ("semantic_max_bound", 3);
    big_clause       = get ("semantic_big_clause", 4);
    exhaustive_limit = get ("semantic_exhaustive", 20000);
    nsamples         = get ("semantic_samples", 500);
    conflict_limit   = get ("semantic_conflicts", 20000);
    upper_limit      = get ("semantic_upper_conflicts", 2000000);
    extend_limit     = get ("semantic_extend_conflicts", 1000);
    pool_limit       = get ("semantic_pool", 1000);
    subset_limit     = get ("semantic_subsets", 4000);
    probes_per_clause = get ("semantic_probes_per_clause", 2000);
    stage_cut  = engine_options["semantic_cut"] != "false";
    stage_prop = engine_options["semantic_prop"] != "false";
    direct_bound     = get ("semantic_direct_bound", 2);
    n_cut = n_prop = n_direct = 0;
    n_candidates = n_sat_calls = n_probes = 0;
    n_all_checked = n_sampled = rounds = 0;
    rng = default_random_engine (1);
  }

  void run (double timeout) {
    this->stats = new Stats ();   // starts the clock
    this->timeout = timeout;
    nvars = cnf_extractor->nvars;
    stage_end = timeout;
    probe_end = LONG_MAX;
    stage_timeout = false;
    build_occurrences ();
    mark_problem_variables ();
    if (stage_cut) cut_fixpoint ();
    if (stage_prop && root_propagation ()) {
      for (int k = 1; k <= max_bound && !out_of_time (); k++) {
        // a bound above 1 has many more seeds to try: it gets a quarter of the time at most
        // and a number of probes in proportion to the size of the formula
        stage_end = (k == 1) ? timeout : stats->get_elapsed_time () + timeout / 4;
        long live = 0;
        for (auto &c : cls ()) live += !c.deleted;
        probe_end = (k == 1) ? LONG_MAX : n_probes + max (2000000L, probes_per_clause * live);
        int found = propagation_stage (k);
        stage_end = timeout;
        probe_end = LONG_MAX;
        log_comment ("SEM stage prop bound " + to_string (k) + " found " + to_string (found), 1);
        if (found && stage_cut) cut_fixpoint ();
      }
    }
  }

  void write_stats () {}

private:

  struct Gadget {
    vector<int> cids;      // clauses that the klause replaces
    vector<int> counted;   // at most `bound` of these literals are true
    int bound;
    int naux;              // auxiliary variables that disappear
    bool all_checked;      // every assignment at the bound was checked
    Gadget () : bound (0), naux (0), all_checked (false) {}
  };

  int nvars;
  vector<vector<int>> occ;           // literal -> ids of the clauses that contain it
  vector<char> is_problem;           // known problem variable
  vector<char> in_klause;            // the variable occurs in a klause: it can never be an auxiliary
                                     // variable of another constraint, the klause still needs it
  vector<int> vstamp, cstamp, xstamp, pstamp, nstamp;   // scratch marks, valid while equal to `stamp`
  vector<int> lmark, lsign, rmark, piece_of, tmark;      // scratch marks of locate (), each with its own counter
  int stamp, lstamp, tstamp;
  vector<int> reach;                 // literal -> number of literals it implies (-1: it fails)
  vector<char> pure;                 // variable occurs in one polarity only in the clauses that are left
  vector<int> pcount, ncount;        // scratch: occurrences per polarity
  default_random_engine rng;
  unordered_set<size_t> rejected;    // candidates that failed (by their clause ids), not tried again

  inline int lidx (int lit) const { return lit > 0 ? 2 * lit : -2 * lit + 1; }
  inline vector<Klause> &cls () { return cnf_extractor->clauses; }

  bool out_of_time () {
    double t = stats->get_elapsed_time ();
    if (t > timeout) { reached_timeout = true; return true; }
    if (t > stage_end || n_probes > probe_end) { stage_timeout = true; return true; }
    return false;
  }

  void build_occurrences () {
    occ.assign (2 * nvars + 2, vector<int> ());
    for (int c = 0; c < (int) cls ().size (); c++) {
      if (cls ()[c].deleted) continue;
      for (int lit : cls ()[c].literals) occ[lidx (lit)].push_back (c);
    }
    cstamp.assign (cls ().size (), 0);
    vstamp.assign (nvars + 1, 0);
    xstamp.assign (nvars + 1, 0);
    pstamp.assign (nvars + 1, 0);
    nstamp.assign (nvars + 1, 0);
    pcount.assign (nvars + 1, 0);
    ncount.assign (nvars + 1, 0);
    lmark.assign (nvars + 1, 0);
    lsign.assign (nvars + 1, 0);
    rmark.assign (nvars + 1, 0);
    piece_of.assign (nvars + 1, 0);
    tmark.assign (nvars + 1, 0);
    stamp = lstamp = tstamp = 0;
    is_problem.assign (nvars + 1, 0);
    in_klause.assign (nvars + 1, 0);
  }

  // What is known about problem variables before the first cut: the variables of
  // the klauses that are already there, and the variables of long clauses.
  void mark_problem_variables () {
    for (auto &c : cls ())
      if (!c.deleted && (int) c.literals.size () > big_clause)
        for (int lit : c.literals) is_problem[abs (lit)] = 1;
    for (auto &k : cnf_extractor->klauses)
      for (int lit : k.literals) is_problem[abs (lit)] = in_klause[abs (lit)] = 1;
  }

  static size_t hash_ids (const vector<int> &sorted_ids) {
    size_t h = 1469598103934665603ULL;
    for (int i : sorted_ids) { h ^= (size_t) i + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2); }
    return h;
  }

  // ------------------------------------------------------------------------
  // SAT side
  // ------------------------------------------------------------------------

  int solve (CaDiCaL::Solver &s, const vector<int> &assumptions, int limit = 0) {
    for (int a : assumptions) s.assume (a);
    s.limit ("conflicts", limit ? limit : conflict_limit);
    n_sat_calls++;
    return s.solve ();
  }

  void add_clauses (CaDiCaL::Solver &s, const vector<int> &cids) {
    for (int c : cids) {
      for (int lit : cls ()[c].literals) s.add (lit);
      s.add (0);
    }
  }

  // A literal that is true only if at least `need` of `lits` are true (the
  // other direction is not needed). Fresh variables start at `next_var`.
  int at_least (CaDiCaL::Solver &s, const vector<int> &lits, int need, int &next_var) {
    int n = lits.size ();
    // c[i][j]: among the first i literals at least j are true (i = 1..n, j = 1..need)
    vector<vector<int>> c (n + 1, vector<int> (need + 1, 0));
    for (int i = 1; i <= n; i++)
      for (int j = 1; j <= need && j <= i; j++) c[i][j] = next_var++;
    for (int i = 1; i <= n; i++) {
      for (int j = 1; j <= need && j <= i; j++) {
        int prev = (i - 1 >= j) ? c[i - 1][j] : 0;          // 0: false
        // c[i][j] -> c[i-1][j] or lits[i-1]
        s.add (-c[i][j]); if (prev) s.add (prev); s.add (lits[i - 1]); s.add (0);
        // c[i][j] -> c[i-1][j] or c[i-1][j-1]      (c[i-1][0] is true)
        if (j > 1) {
          s.add (-c[i][j]); if (prev) s.add (prev);
          if (i - 1 >= j - 1) s.add (c[i - 1][j - 1]);
          s.add (0);
        }
      }
    }
    return c[n][need];
  }

  // Largest set of counted literals that the clauses allow to be true together,
  // grown from a model. For a cardinality constraint every such set that cannot
  // be extended has the size of the bound. -1: no model, or the solver gave up.
  int maximal_true (CaDiCaL::Solver &s, const vector<int> &counted, vector<char> *which = nullptr) {
    int res = solve (s, vector<int> ());
    if (res != 10) return -1;
    vector<char> in (counted.size (), 0);
    vector<int> chosen;
    for (size_t i = 0; i < counted.size (); i++)
      if (s.val (counted[i]) > 0) { in[i] = 1; chosen.push_back (counted[i]); }
    for (size_t i = 0; i < counted.size (); i++) {
      if (in[i]) continue;
      vector<int> as = chosen;
      as.push_back (counted[i]);
      res = solve (s, as);
      if (res == 0) return -1;
      if (res != 10) continue;
      chosen.clear ();
      for (size_t j = 0; j < counted.size (); j++) {
        in[j] = s.val (counted[j]) > 0;
        if (in[j]) chosen.push_back (counted[j]);
      }
    }
    if (which) *which = in;
    return chosen.size ();
  }

  static long binomial (long n, long k, long cap) {
    if (k < 0 || k > n) return 0;
    if (k > n - k) k = n - k;
    long r = 1;
    for (long i = 1; i <= k; i++) {
      r = r * (n - k + i) / i;
      if (r > cap) return cap + 1;
    }
    return r;
  }

  // Every assignment that makes exactly `t` of `lits` true (and the others
  // false) satisfies the solver's clauses for some value of the other variables.
  // All of them if there are at most exhaustive_limit, a random sample otherwise.
  // The clauses contain these literals only negated, so the values that extend
  // such an assignment also extend every assignment with fewer true literals.
  bool all_extend (CaDiCaL::Solver &s, const vector<int> &lits, int t, bool &all_checked) {
    int m = lits.size ();
    if (t > m) t = m;
    vector<int> as (m);
    long count = binomial (m, t, exhaustive_limit);
    if (count <= exhaustive_limit) {
      vector<int> pick (t);
      for (int i = 0; i < t; i++) pick[i] = i;
      while (true) {
        for (int i = 0; i < m; i++) as[i] = -lits[i];
        for (int i : pick) as[i] = lits[i];
        if (solve (s, as, extend_limit) != 10) return false;
        int i = t - 1;
        while (i >= 0 && pick[i] == m - t + i) i--;
        if (i < 0) break;
        pick[i]++;
        for (int j = i + 1; j < t; j++) pick[j] = pick[j - 1] + 1;
      }
      return true;
    }
    all_checked = false;
    vector<int> order (m);
    for (int i = 0; i < m; i++) order[i] = i;
    for (int r = 0; r < nsamples; r++) {
      shuffle (order.begin (), order.end (), rng);
      for (int i = 0; i < m; i++) as[order[i]] = (i < t) ? lits[order[i]] : -lits[order[i]];
      if (solve (s, as, extend_limit) != 10) return false;
    }
    return true;
  }

  // Counted literals of the boundary variables `xs` of the clauses `cids`: a
  // variable that these clauses mention only negatively is counted positively
  // (they can only stop it from being true) and the other way round. False if a
  // variable occurs in both polarities: the clauses are not monotone in it.
  // If a variable occurs in both polarities the clauses are not monotone in it
  // (an encoding with equivalences, like the order encoding): the result is
  // false, and `counted` holds a guess (the polarity with fewer occurrences is
  // the counted one) that the caller has to settle with the solver.
  bool phases_by_purity (const vector<int> &cids, const vector<int> &xs, vector<int> &counted) {
    ++stamp;
    for (int x : xs) { xstamp[x] = stamp; pcount[x] = ncount[x] = 0; }
    for (int c : cids)
      for (int lit : cls ()[c].literals) {
        int v = abs (lit);
        if (xstamp[v] != stamp) continue;
        if (lit > 0) pcount[v]++; else ncount[v]++;
      }
    counted.clear ();
    bool pure_in_all = true;
    for (int x : xs) {
      if (pcount[x] && ncount[x]) pure_in_all = false;
      counted.push_back (ncount[x] >= pcount[x] ? x : -x);
    }
    return pure_in_all;
  }

  void emit (Gadget &g, const char *stage) {
    vector<int> lits;
    for (int l : g.counted) lits.push_back (-l);
    int n = g.counted.size ();
    Klause klause (lits, n - g.bound);
    sort (g.cids.begin (), g.cids.end ());
    cnf_extractor->add_klause (klause, g.cids);
    for (int l : g.counted) is_problem[abs (l)] = in_klause[abs (l)] = 1;
    stats->nconstraints++;
    tuple<int, int> key (n, n - g.bound);
    if (stats->ALK_constraint_sizes.find (key) == stats->ALK_constraint_sizes.end ()) stats->ALK_constraint_sizes[key] = 0;
    stats->ALK_constraint_sizes[key]++;
    if (g.all_checked) n_all_checked++; else n_sampled++;
    if (g.naux == 0) n_direct++;
    string s = "k " + to_string (n - g.bound) + " ";
    for (int l : lits) s += to_string (l) + " ";
    cout << "c " << s << "0" << endl;
    log_comment (string ("SEM ") + stage + " ok n " + to_string (n) + " bound " + to_string (g.bound) + " naux "
                 + to_string (g.naux) + " ncls " + to_string (g.cids.size ()) + (g.all_checked ? " all" : " sampled"), 1);
  }

  // ------------------------------------------------------------------------
  // Stage "cut"
  // ------------------------------------------------------------------------

  // No encoding in use needs more auxiliary variables than this for n counted
  // literals (sequential counter and totalizer: at most n * k, k < n). A larger
  // piece is the rest of the formula, not an encoding.
  static long aux_cap (long n) { return 2 * n * n + 64; }

  // Is the piece (auxiliary variables `vars`, their clauses `cids`, the problem
  // variables `xs` they touch) a cardinality constraint over `xs`?
  bool check_piece (const vector<int> &vars, const vector<int> &cids, const vector<int> &xs, Gadget &g, string &why) {
    int n = xs.size ();
    if (n <= min_data_vars) { why = "small"; return false; }
    if ((long) vars.size () > aux_cap (n)) { why = "large"; return false; }
    vector<int> counted;
    bool mono = phases_by_purity (cids, xs, counted);
    CaDiCaL::Solver s;
    add_clauses (s, cids);
    vector<char> in;
    int k = maximal_true (s, counted, &in);
    if (!mono && k >= 0) {
      // The polarities were a guess. In an assignment at the bound, changing a counted literal
      // that is true leaves the clauses satisfiable and changing one that is false does not:
      // the solver says which literal of each variable is the counted one.
      vector<int> now (n), as (n);
      for (int i = 0; i < n; i++) now[i] = in[i] ? counted[i] : -counted[i];
      k = 0;
      for (int i = 0; i < n; i++) {
        as = now;
        as[i] = -now[i];
        int res = solve (s, as);
        if (res == 0) { why = "mixed"; return false; }
        if (res == 10) { counted[i] = now[i]; k++; } else counted[i] = -now[i];
      }
    }
    if (k < 1 || k > n - 2) { why = mono ? "trivial" : "mixed"; return false; }
    bool all_checked = true;
    // not monotone: the values that extend an assignment at the bound need not extend one below it
    for (int level = mono ? k : 0; level <= k; level++)
      if (!all_extend (s, counted, level, all_checked)) { why = "lower"; return false; }
    int next_var = nvars + 1;
    int top = at_least (s, counted, k + 1, next_var);
    if (solve (s, vector<int> (1, top), upper_limit) != 20) { why = "upper"; return false; }
    g.cids = cids;
    g.counted = counted;
    g.bound = k;
    g.naux = vars.size ();
    g.all_checked = all_checked;
    return true;
  }

  int cut_round () {
    int found = 0;
    vector<char> seen (nvars + 1, 0);
    vector<int> stack, vars, cids, xs;
    for (int v0 = 1; v0 <= nvars; v0++) {
      if (is_problem[v0] || seen[v0]) continue;
      if (out_of_time ()) break;
      ++stamp;
      vars.clear (); cids.clear (); xs.clear ();
      stack.push_back (v0);
      seen[v0] = 1;
      while (!stack.empty ()) {
        int v = stack.back ();
        stack.pop_back ();
        vars.push_back (v);
        for (int sgn = 0; sgn < 2; sgn++)
          for (int c : occ[2 * v + sgn]) {
            if (cls ()[c].deleted || cstamp[c] == stamp) continue;
            cstamp[c] = stamp;
            cids.push_back (c);
            for (int lit : cls ()[c].literals) {
              int u = abs (lit);
              if (is_problem[u]) {
                if (vstamp[u] != stamp) { vstamp[u] = stamp; xs.push_back (u); }
              } else if (!seen[u]) {
                seen[u] = 1;
                stack.push_back (u);
              }
            }
          }
      }
      if (cids.empty () || xs.empty ()) continue;
      sort (cids.begin (), cids.end ());
      size_t h = hash_ids (cids);
      if (rejected.count (h)) continue;
      n_candidates++;
      Gadget g;
      string why;
      sort (xs.begin (), xs.end ());
      if (check_piece (vars, cids, xs, g, why)) {
        emit (g, "cut");
        n_cut++;
        found++;
      } else {
        rejected.insert (h);
        log_comment ("SEM cut " + why + " n " + to_string (xs.size ()) + " naux " + to_string (vars.size ())
                     + " ncls " + to_string (cids.size ()), 2);
      }
    }
    return found;
  }

  void cut_fixpoint () {
    while (!out_of_time ()) {
      rounds++;
      int found = cut_round ();
      log_comment ("SEM stage cut round " + to_string (rounds) + " found " + to_string (found), 1);
      if (!found) break;
    }
  }

  // ------------------------------------------------------------------------
  // Unit propagation on the clauses that are left
  // ------------------------------------------------------------------------

  vector<signed char> val;   // per variable: 0 unassigned, 1 true, -1 false
  vector<int> trail;
  size_t root;               // trail position after the units of the formula

  inline int value (int lit) const { int v = val[abs (lit)]; return lit > 0 ? v : -v; }

  bool enqueue (int lit) {
    int v = value (lit);
    if (v) return v > 0;
    val[abs (lit)] = lit > 0 ? 1 : -1;
    trail.push_back (lit);
    return true;
  }

  bool propagate (size_t from) {
    for (size_t i = from; i < trail.size (); i++) {
      int lit = trail[i];
      for (int c : occ[lidx (-lit)]) {
        if (cls ()[c].deleted) continue;
        int open = 0, last = 0;
        bool sat = false;
        for (int l : cls ()[c].literals) {
          int v = value (l);
          if (v > 0) { sat = true; break; }
          if (v == 0) { open++; last = l; }
        }
        if (sat || open > 1) continue;
        if (open == 0) return false;
        enqueue (last);
      }
    }
    return true;
  }

  void backtrack (size_t to) {
    while (trail.size () > to) { val[abs (trail.back ())] = 0; trail.pop_back (); }
  }

  // Makes the literals true one after the other; false on a conflict (also if
  // one of them is already false). The caller backtracks.
  bool probe (const vector<int> &lits) {
    n_probes++;
    for (int l : lits) {
      size_t from = trail.size ();
      if (!enqueue (l)) return false;
      if (!propagate (from)) return false;
    }
    return true;
  }

  bool root_propagation () {
    val.assign (nvars + 1, 0);
    trail.clear ();
    for (auto &c : cls ())
      if (!c.deleted && c.literals.size () == 1 && !enqueue (c.literals[0])) return false;
    if (!propagate (0)) return false;
    root = trail.size ();
    return true;
  }

  // ------------------------------------------------------------------------
  // Stage "prop"
  // ------------------------------------------------------------------------

  // The clauses that implement "at most k of L", if there are any:
  //   - every piece that falls off when the formula is cut at the variables of
  //     L and that the constraint implies (every assignment that the constraint
  //     allows extends to it),
  //   - every clause over L alone that the constraint implies (at least k+1
  //     negated literals of L).
  // Together they must imply the constraint.
  bool locate (const vector<int> &L, int k, Gadget &g, string &why) {
    int n = L.size ();
    ++lstamp;
    for (int l : L) { lmark[abs (l)] = lstamp; lsign[abs (l)] = l > 0 ? 1 : -1; }
    // a clause literal on a variable of L is "negated" if it is the negation of the counted literal
    auto in_L = [&] (int v) { return lmark[v] == lstamp; };
    auto negated = [&] (int lit) { return (lit > 0 ? 1 : -1) == -lsign[abs (lit)]; };

    vector<int> inside;                      // clauses over L that the constraint implies
    vector<vector<int>> pieces_vars, pieces_cids;
    vector<char> pieces_mono;                // the piece mentions the literals of L only negated
    const int given_up = -1;
    long cap = aux_cap (n);
    vector<int> stack, pv, pc;
    ++stamp;                                 // cstamp[c] == stamp: clause c was looked at
    for (int l : L) {
      int x = abs (l);
      for (int sgn = 0; sgn < 2; sgn++)
        for (int c : occ[2 * x + sgn]) {
          if (cls ()[c].deleted || cstamp[c] == stamp) continue;
          bool only_L = true, implied = true;
          int start = 0;
          for (int lit : cls ()[c].literals) {
            int u = abs (lit);
            if (!in_L (u)) { only_L = false; if (!start && rmark[u] != lstamp) start = u; }
            else if (!negated (lit)) implied = false;
          }
          if (only_L) {
            cstamp[c] = stamp;
            if (implied && (int) cls ()[c].literals.size () >= k + 1) inside.push_back (c);
            continue;
          }
          if (!start) continue;              // its other variables were reached before
          // the piece that contains `start`: everything reachable without passing a variable of L
          pv.clear (); pc.clear (); stack.clear ();
          // A variable that a klause counts is not auxiliary: the klause is not among the clauses,
          // so a piece that contains such a variable does not hold everything that is said about it.
          bool ok = !in_klause[start], mono = true;
          int id = pieces_vars.size () + 1;
          stack.push_back (start);
          rmark[start] = lstamp;
          piece_of[start] = id;
          while (ok && !stack.empty ()) {
            int v = stack.back ();
            stack.pop_back ();
            pv.push_back (v);
            if ((long) pv.size () > cap) { ok = false; break; }
            for (int s2 = 0; s2 < 2; s2++)
              for (int c2 : occ[2 * v + s2]) {
                if (cls ()[c2].deleted || cstamp[c2] == stamp) continue;
                cstamp[c2] = stamp;
                pc.push_back (c2);
                for (int lit : cls ()[c2].literals) {
                  int u = abs (lit);
                  if (in_L (u)) {
                    if (!negated (lit)) mono = false;           // an encoding with equivalences (order encoding)
                  } else if (rmark[u] != lstamp) {
                    rmark[u] = lstamp;
                    piece_of[u] = id;
                    stack.push_back (u);
                    if (in_klause[u]) ok = false;               // counted by a klause: not auxiliary
                  } else if (piece_of[u] == given_up) {
                    ok = false;                                 // it joins a piece that was given up
                  }
                }
              }
          }
          if (!ok) {
            for (int v : pv) piece_of[v] = given_up;
            for (int v : stack) piece_of[v] = given_up;
            continue;
          }
          pieces_vars.push_back (pv);
          pieces_cids.push_back (pc);
          pieces_mono.push_back (mono);
        }
    }
    // which pieces does the constraint imply?
    g.cids.clear ();
    g.naux = 0;
    g.all_checked = true;
    for (size_t p = 0; p < pieces_vars.size (); p++) {
      vector<int> &cids = pieces_cids[p];
      ++tstamp;
      vector<int> mine;                      // counted literals that the piece mentions
      for (int c : cids)
        for (int lit : cls ()[c].literals) {
          int u = abs (lit);
          if (in_L (u) && tmark[u] != tstamp) { tmark[u] = tstamp; mine.push_back (lsign[u] * u); }
        }
      if (mine.empty ()) continue;
      CaDiCaL::Solver s;
      add_clauses (s, cids);
      bool all_checked = true, extends = true;
      // a piece that mentions L only negated: the assignments at the bound are enough (the values
      // that extend one of them extend every assignment below it); otherwise every number of true
      // literals up to the bound is checked
      int top_level = min (k, (int) mine.size ());
      for (int level = pieces_mono[p] ? top_level : 0; level <= top_level && extends; level++)
        extends = all_extend (s, mine, level, all_checked);
      if (!extends) continue;
      if (!all_checked) g.all_checked = false;
      g.cids.insert (g.cids.end (), cids.begin (), cids.end ());
      g.naux += pieces_vars[p].size ();
    }
    g.cids.insert (g.cids.end (), inside.begin (), inside.end ());
    if (g.cids.empty ()) { why = "no clauses"; return false; }
    // do they imply the constraint?
    CaDiCaL::Solver s;
    add_clauses (s, g.cids);
    int next_var = nvars + 1;
    int top = at_least (s, L, k + 1, next_var);
    if (solve (s, vector<int> (1, top), upper_limit) != 20) { why = "upper"; return false; }
    g.counted = L;
    g.bound = k;
    return true;
  }

  unordered_set<size_t> tried;      // literal sets that were looked at (sorted, with the bound)

  bool is_new (vector<int> L, int k) {
    sort (L.begin (), L.end ());
    L.push_back (k);
    size_t h = hash_ids (L);
    if (tried.count (h)) return false;
    tried.insert (h);
    return true;
  }

  // ---- what single literals force (cached until clauses are deleted) ----

  unordered_map<int, vector<int>> imp_cache;      // literal -> literals it implies, sorted (itself included)
  unordered_set<int> failing;                      // literals that lead to a conflict on their own

  // false if the literal fails
  bool implied (int lit, const vector<int> *&out) {
    auto it = imp_cache.find (lit);
    if (it == imp_cache.end ()) {
      backtrack (root);
      bool ok = probe (vector<int> (1, lit));
      vector<int> v (trail.begin () + root, trail.end ());
      backtrack (root);
      sort (v.begin (), v.end ());
      if (!ok) failing.insert (lit);
      it = imp_cache.emplace (lit, v).first;
    }
    out = &it->second;
    return !failing.count (lit);
  }

  static bool has (const vector<int> &sorted, int x) { return binary_search (sorted.begin (), sorted.end (), x); }

  // a implies b or b implies a
  bool comparable (int a, int b) {
    const vector<int> *ia, *ib;
    bool oa = implied (a, ia), ob = implied (b, ib);
    return (oa && has (*ia, b)) || (ob && has (*ib, a));
  }

  // How much each literal forces on its own. A literal that implies another
  // forces everything the other forces and more, so going through literals by
  // decreasing reach meets a counted literal before a literal that stands for
  // it (the output of a counter that it switches on).
  // A variable that the remaining clauses use in one polarity only cannot be a
  // problem variable (nothing ever needs it the other way round): it is never
  // proposed as a counted literal.
  void compute_pure () {
    pure.assign (nvars + 1, 0);
    for (int v = 1; v <= nvars; v++) {
      bool pos = false, neg = false;
      for (int c : occ[2 * v]) if (!cls ()[c].deleted) { pos = true; break; }
      for (int c : occ[2 * v + 1]) if (!cls ()[c].deleted) { neg = true; break; }
      pure[v] = pos != neg;
    }
  }

  void compute_reach () {
    reach.assign (2 * nvars + 2, 0);
    for (int v = 1; v <= nvars; v++) {
      if (val[v] || (occ[2 * v].empty () && occ[2 * v + 1].empty ())) continue;
      for (int sgn = 1; sgn >= -1; sgn -= 2) {
        backtrack (root);
        bool ok = probe (vector<int> (1, sgn * v));
        reach[lidx (sgn * v)] = ok ? (int) (trail.size () - root) - 1 : -1;
      }
    }
    backtrack (root);
  }

  // Every k literals of L force all the others false: all k-subsets if there
  // are at most `limit`, else `limit` random ones.
  bool saturating (const vector<int> &L, int k, long limit) {
    int n = L.size ();
    if (n < k + 1) return false;
    long count = binomial (n, k, limit);
    bool all = count <= limit;
    long todo = all ? count : limit;
    vector<int> pick (k), order (n), sub (k);
    for (int i = 0; i < k; i++) pick[i] = i;
    for (int i = 0; i < n; i++) order[i] = i;
    vector<char> in (n);
    bool good = true;
    while (good && todo-- > 0) {
      if (!all) {
        shuffle (order.begin (), order.end (), rng);
        for (int i = 0; i < k; i++) pick[i] = order[i];
      }
      for (int i = 0; i < k; i++) sub[i] = L[pick[i]];
      backtrack (root);
      if (!probe (sub)) { good = false; break; }
      fill (in.begin (), in.end (), 0);
      for (int i : pick) in[i] = 1;
      for (int i = 0; i < n && good; i++)
        if (!in[i] && value (L[i]) >= 0) good = false;
      if (all) {
        int i = k - 1;
        while (i >= 0 && pick[i] == n - k + i) i--;
        if (i < 0) break;
        pick[i]++;
        for (int j = i + 1; j < k; j++) pick[j] = pick[j - 1] + 1;
      }
    }
    backtrack (root);
    return good;
  }

  // The same clauses can often be read in more than one way. The first output
  // of a counter can be counted in place of the input that switches it on, the
  // last one in place of the input that it blocks, and an auxiliary literal of
  // a neighbouring encoding in place of the literal that it forces. Each of
  // these readings is a constraint of the formula. A problem variable turns up
  // as a counted literal wherever the clauses around it are probed, an
  // auxiliary variable only where an encoding is cut short or reached into
  // from the next one. So every variable gets one vote for each probe in which
  // it is a seed or a literal that can take a seed's place; where literals
  // stand for each other the ones with the most votes are counted, and the
  // candidates with the most votes per counted literal are replaced first.
  vector<int> votes;       // per variable: candidates that count it
  vector<int> tvotes;      // per variable: probes in which it is a seed or can take a seed's place
  vector<char> was_seed;   // per literal: it was a seed of a probe that forced rivals false
  struct Tuple { vector<int> seeds, rivals; };
  vector<Tuple> tuples;    // probes with too many rivals that stand for each other to try every choice

  struct Cand {
    vector<int> L;
    Gadget g;
    long votes;
  };
  vector<Cand> cands;

  // Locates the encoding of "at most k of L" and keeps it as a candidate.
  bool collect (const vector<int> &L, int k, bool known_new = false) {
    if ((int) L.size () <= min_data_vars || (int) L.size () < k + 2) return false;
    if (!known_new && !is_new (L, k)) return false;
    n_candidates++;
    Cand c;
    string why;
    if (!locate (L, k, c.g, why)) {
      if (logging >= 2) {
        string t = "SEM prop " + why + " n " + to_string (L.size ()) + " bound " + to_string (k) + " lits";
        for (int l : L) t += " " + to_string (l);
        log_comment (t, 2);
      }
      return false;
    }
    // A set of binary clauses that forms a clique is an at-most-one in its pairwise form:
    // it is left as it is unless asked for (as the Direct_AMO engine is off by default).
    if (c.g.naux == 0 && k < direct_bound) return false;
    c.L = L;
    c.votes = 0;
    cands.push_back (c);
    return true;
  }

  // Replaces the collected candidates: most votes first, of equal ones the
  // larger encoding first; a candidate that has lost a clause to an earlier
  // one is dropped.
  int replace_candidates () {
    votes.assign (nvars + 1, 0);
    for (auto &c : cands) for (int l : c.L) votes[abs (l)]++;
    for (auto &c : cands) { c.votes = 0; for (int l : c.L) c.votes += votes[abs (l)]; }
    vector<int> order (cands.size ());
    for (size_t i = 0; i < cands.size (); i++) order[i] = i;
    // votes per counted literal (compared as fractions)
    stable_sort (order.begin (), order.end (), [&] (int a, int b) {
      long va = cands[a].votes * (long) cands[b].L.size (), vb = cands[b].votes * (long) cands[a].L.size ();
      if (va != vb) return va > vb;
      return cands[a].g.cids.size () > cands[b].g.cids.size ();
    });
    int found = 0;
    for (int i : order) {
      Cand &c = cands[i];
      bool intact = true;
      for (int id : c.g.cids) if (cls ()[id].deleted) { intact = false; break; }
      if (!intact) continue;
      emit (c.g, "prop");
      n_prop++;
      found++;
    }
    cands.clear ();
    return found;
  }

  // Bound 1. The rivals of a literal are the literals that it forces false. A
  // set of literals that are rivals of each other is an at-most-one constraint.
  // The set is built around the seed from its rivals, the one with the largest
  // reach first.
  int amo_from (int seed) {
    int found = 0;
    const vector<int> *is;
    if (!implied (seed, is)) return 0;
    if ((int) is->size () < 3 || (int) is->size () > pool_limit) return 0;
    vector<int> pool;
    for (int t : *is) if (t != seed && !pure[abs (t)]) pool.push_back (-t);
    vector<int> cand;                                // rivals of the seed in both directions
    for (int m : pool) {
      const vector<int> *im;
      if (implied (m, im) && has (*im, -seed)) cand.push_back (m);
    }
    if ((int) cand.size () < 2) return 0;
    sort (cand.begin (), cand.end (), [&] (int a, int b) {
      size_t ra = imp_cache[a].size (), rb = imp_cache[b].size ();
      if (ra != rb) return ra > rb;
      return abs (a) < abs (b);
    });
    vector<vector<int>> sets;
    vector<char> covered (cand.size (), 0);
    for (size_t a = 0; a < cand.size (); a++) {
      if (covered[a]) continue;
      vector<int> members (1, a);
      for (size_t b = 0; b < cand.size (); b++) {
        if (b == a) continue;
        bool all = true;
        for (int m : members)
          if (!has (imp_cache[cand[m]], -cand[b]) || !has (imp_cache[cand[b]], -cand[m])) { all = false; break; }
        if (all) members.push_back (b);
      }
      vector<int> L (1, seed);
      for (int m : members) { covered[m] = 1; L.push_back (cand[m]); }
      sets.push_back (L);
    }
    for (auto &L : sets) {
      if (out_of_time ()) break;
      if (collect (L, 1)) found++;
    }
    return found;
  }

  // Bound k >= 2. Seeds are k literals that can be true together: the first is
  // any literal, each further one is taken from a clause that the literals
  // before it have shortened. If the k-th literal forces literals false, these
  // are candidates for the other counted literals.
  int amk_from (int seed, int k) {
    backtrack (root);
    vector<int> chosen (1, seed);
    int found = 0;
    if (probe (chosen)) found = extend_seed (chosen, k);
    backtrack (root);
    return found;
  }

  // candidates for the next seed: negations of the open literals of clauses
  // that the current assignment has shortened
  void next_seeds (vector<int> &out) {
    ++tstamp;
    out.clear ();
    for (size_t i = root; i < trail.size (); i++) {
      int lit = trail[i];
      for (int c : occ[lidx (-lit)]) {
        if (cls ()[c].deleted) continue;
        bool sat = false;
        for (int l : cls ()[c].literals) if (value (l) > 0) { sat = true; break; }
        if (sat) continue;
        for (int l : cls ()[c].literals) {
          int u = abs (l);
          if (value (l) == 0 && tmark[u] != tstamp && !pure[u]) { tmark[u] = tstamp; out.push_back (-l); }
        }
      }
    }
    sort (out.begin (), out.end (), [&] (int a, int b) {
      if (reach[lidx (a)] != reach[lidx (b)]) return reach[lidx (a)] > reach[lidx (b)];
      return abs (a) < abs (b);
    });
  }

  unordered_set<size_t> seeded;     // seed tuples that were probed (sorted)

  // The trail holds the propagation of `chosen`.
  int extend_seed (vector<int> &chosen, int k) {
    int found = 0;
    vector<int> cands2;
    next_seeds (cands2);
    if ((int) cands2.size () > pool_limit) return 0;
    for (int c : cands2) {
      if (out_of_time ()) break;
      if (value (c) != 0) continue;
      if ((int) chosen.size () + 1 == k) {
        vector<int> key = chosen;
        key.push_back (c);
        sort (key.begin (), key.end ());
        key.push_back (-k);
        size_t h = hash_ids (key);
        if (seeded.count (h)) continue;
        seeded.insert (h);
      }
      size_t mark = trail.size ();
      chosen.push_back (c);
      n_probes++;
      if (enqueue (c) && propagate (mark)) {
        if ((int) chosen.size () < k) {
          found += extend_seed (chosen, k);
        } else if (trail.size () > mark + 2) {
          vector<int> rivals;
          for (size_t i = mark + 1; i < trail.size (); i++) rivals.push_back (-trail[i]);
          vector<int> seeds = chosen;
          vector<int> prefix (chosen.begin (), chosen.end () - 1);
          backtrack (root);
          // the same literals (seeds and rivals together) were probed from other seeds
          vector<int> key = rivals;
          key.insert (key.end (), seeds.begin (), seeds.end ());
          sort (key.begin (), key.end ());
          key.push_back (-1000 - k);
          if (seeded.insert (hash_ids (key)).second) found += from_tuple (seeds, rivals, k);
          backtrack (root);
          chosen.pop_back ();
          if (!probe (prefix)) return found;       // cannot happen: nothing was deleted
          continue;
        }
      }
      backtrack (mark);
      chosen.pop_back ();
    }
    return found;
  }

  // The seeds are true together and force the rivals false. Which rivals can
  // be counted with the seeds? A counted literal can take the place of a seed:
  // with the other seeds it forces that seed and the other counted literals
  // false. Rivals that do not are dropped, the one at odds with the most others
  // first. Two rivals of which one implies the other are not held against each
  // other: one of them stands for the other. Of such rivals every choice is
  // tried (no two that are comparable) and each choice that is a constraint
  // becomes a candidate; if there are too many choices the tuple is kept for
  // the second sweep.
  int from_tuple (const vector<int> &seeds, vector<int> C, int k) {
    if ((int) C.size () < 2 || (int) C.size () > pool_limit) return 0;
    ++tstamp;
    for (int l : seeds) tmark[abs (l)] = tstamp;
    {
      // a rival must force each seed false when it takes its place
      vector<int> keep;
      const vector<int> *ic;
      for (int c : C) {
        if (tmark[abs (c)] == tstamp || pure[abs (c)] || !implied (c, ic)) continue;
        bool ok = true;
        for (int si = 0; si < k && ok; si++) {
          if (has (*ic, seeds[si]) || comparable (c, seeds[si])) { ok = false; break; }
          vector<int> T = seeds;
          T[si] = c;
          backtrack (root);
          ok = probe (T) && value (seeds[si]) < 0;
        }
        if (ok) keep.push_back (c);
      }
      backtrack (root);
      C.swap (keep);
    }
    while ((int) C.size () >= 2) {
      int m = C.size ();
      vector<long> bad (m, 0);
      bool any = false;
      for (int ci = 0; ci < m; ci++)
        for (int si = 0; si < k; si++) {
          vector<int> T = seeds;
          T[si] = C[ci];
          backtrack (root);
          if (!probe (T)) { bad[ci] += m + 1; any = true; continue; }
          vector<int> open;
          for (int di = 0; di < m; di++) if (di != ci && value (C[di]) >= 0) open.push_back (di);
          backtrack (root);
          for (int di : open) {
            if (comparable (C[ci], C[di])) continue;
            bad[ci]++; bad[di]++; any = true;
          }
        }
      backtrack (root);
      if (!any) break;
      int worst = 0;
      for (int i = 1; i < m; i++) if (bad[i] > bad[worst]) worst = i;
      C.erase (C.begin () + worst);
    }
    if ((int) C.size () < 2) return 0;
    for (int l : seeds) { tvotes[abs (l)]++; was_seed[lidx (l)] = 1; }
    for (int c : C) tvotes[abs (c)]++;
    // groups of rivals that are comparable, directly or through others
    int m = C.size ();
    vector<int> group (m, -1);
    int ngroups = 0;
    for (int i = 0; i < m; i++) {
      if (group[i] >= 0) continue;
      vector<int> st (1, i);
      group[i] = ngroups;
      while (!st.empty ()) {
        int a = st.back (); st.pop_back ();
        for (int b2 = 0; b2 < m; b2++)
          if (group[b2] < 0 && comparable (C[a], C[b2])) { group[b2] = ngroups; st.push_back (b2); }
      }
      ngroups++;
    }
    // the choices of each group: its sets of pairwise incomparable rivals
    vector<vector<vector<int>>> choices (ngroups);
    long combos = 1;
    for (int gi = 0; gi < ngroups && combos <= 256; gi++) {
      vector<int> mem;
      for (int i = 0; i < m; i++) if (group[i] == gi) mem.push_back (i);
      if ((int) mem.size () > 10) { combos = 257; break; }
      for (int mask = 1; mask < (1 << mem.size ()); mask++) {
        vector<int> pickd;
        bool ok = true;
        for (size_t a = 0; a < mem.size () && ok; a++) {
          if (!(mask >> a & 1)) continue;
          for (int q : pickd) if (comparable (C[q], C[mem[a]])) { ok = false; break; }
          pickd.push_back (mem[a]);
        }
        if (ok) choices[gi].push_back (pickd);
      }
      combos *= choices[gi].size ();
    }
    if (combos > 256) {
      // too many choices to try each: the votes decide in the second sweep
      Tuple t;
      t.seeds = seeds;
      t.rivals = C;
      tuples.push_back (t);
      return 1;
    }
    vector<int> at (ngroups, 0);
    int found = 0;
    while (true) {
      vector<int> L = seeds;
      for (int gi = 0; gi < ngroups; gi++) for (int i : choices[gi][at[gi]]) L.push_back (C[i]);
      if ((int) L.size () >= k + 2 && (int) L.size () > min_data_vars && is_new (L, k) && saturating (L, k, subset_limit)
          && collect (L, k, true)) found++;
      int gi = 0;
      while (gi < ngroups && ++at[gi] == (int) choices[gi].size ()) at[gi++] = 0;
      if (gi == ngroups) break;
    }
    return found;
  }

  // A counted literal counts one thing. A literal that forces two seeds true
  // that do not force each other (the "nothing is false in this half" literal
  // of a neighbouring counter, for example) stands for several counted
  // literals at once and is not one itself.
  bool stands_for_several (int c) {
    const vector<int> *ic;
    if (!implied (c, ic)) return true;
    vector<int> forced;
    for (int t : *ic) if (t != c && was_seed[lidx (t)]) { forced.push_back (t); if (forced.size () > 24) break; }
    for (size_t a = 0; a < forced.size (); a++)
      for (size_t b = a + 1; b < forced.size (); b++)
        if (!comparable (forced[a], forced[b])) return true;
    return false;
  }

  // Second sweep: of the rivals of a tuple that stand for each other the ones
  // with the most votes are counted.
  void candidates_from_tuples (int k) {
    for (auto &t : tuples) {
      if (out_of_time ()) break;
      vector<int> order = t.rivals;
      // equal votes: the rival that the seeds forced first comes first
      stable_sort (order.begin (), order.end (), [&] (int a, int b) { return tvotes[abs (a)] > tvotes[abs (b)]; });
      vector<int> L = t.seeds;
      for (int c : order) {
        if (stands_for_several (c)) continue;
        bool free = true;
        for (size_t i = t.seeds.size (); i < L.size () && free; i++) if (comparable (c, L[i])) free = false;
        if (free) L.push_back (c);
      }
      if ((int) L.size () >= k + 2 && (int) L.size () > min_data_vars && is_new (L, k) && saturating (L, k, subset_limit))
        collect (L, k, true);
    }
    backtrack (root);
    tuples.clear ();
  }

  int propagation_stage (int k) {
    int total = 0;
    for (int pass = 0; pass < 8 && !out_of_time (); pass++) {
      imp_cache.clear ();
      failing.clear ();
      tried.clear ();
      seeded.clear ();
      cands.clear ();
      tuples.clear ();
      tvotes.assign (nvars + 1, 0);
      was_seed.assign (2 * nvars + 2, 0);
      compute_pure ();
      compute_reach ();
      vector<int> seeds;
      for (int v = 1; v <= nvars; v++) {
        if (val[v] || pure[v] || (occ[2 * v].empty () && occ[2 * v + 1].empty ())) continue;
        for (int sgn = 1; sgn >= -1; sgn -= 2)
          if (reach[lidx (sgn * v)] >= (k == 1 ? 2 : 0)) seeds.push_back (sgn * v);
      }
      sort (seeds.begin (), seeds.end (), [&] (int a, int b) {
        if (reach[lidx (a)] != reach[lidx (b)]) return reach[lidx (a)] > reach[lidx (b)];
        if (abs (a) != abs (b)) return abs (a) < abs (b);
        return a > b;
      });
      for (int seed : seeds) {
        if (out_of_time ()) break;
        if (k == 1) amo_from (seed); else amk_from (seed, k);
      }
      backtrack (root);
      if (k > 1) candidates_from_tuples (k);
      int found = replace_candidates ();
      total += found;
      if (!found) break;
    }
    return total;
  }

};

}

#endif
