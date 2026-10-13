# Regression tests

Run `python3 -m unittest discover -s tests -v` from the repository root.

The 27 tests cover the baseline audit mechanics and the new 24-state construction.
Positive controls include genuinely compatible toy states and a collapsible toy
path. Negative controls corrupt reachability witnesses, conflict certificates,
primality decisions and growth entry behavior. Pair tests check the first return
boundary, including deliberately incorrect acceptance of a composite pair.

The longer arithmetic, growth and whole-number sweeps belong to `tools/verify24.py`
and `tools/audit.py`. Unbounded correctness is established by the Lean build.

Seven tests compile the shared C++ search checker in temporary storage (and are
skipped when no C++17 compiler is available). They exercise a damaged prime
return followed by a later valid-looking return, pair/outer returns with a wrong
number of ones, removal of the halting branch, a real negative fixture, and the
complete current baseline. Both interpreters reject the first incorrect boundary.

A positive control runs the repair search on a toy machine with a known merge,
one-transition repair and changed initial state. It must recover that proposal;
this checks that pruning does not simply reject everything.
