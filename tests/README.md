# Regression tests

Run `python3 -m unittest discover -s tests -v` from the repository root.

The 35 tests cover the baseline audit mechanics and the new 24-state construction.
Positive controls include compatible toy states and a collapsible toy
path. Negative controls corrupt reachability witnesses, conflict certificates,
primality decisions and growth entry behavior. Pair tests check the first return
boundary, including deliberately incorrect acceptance of a composite pair.

The longer arithmetic, growth and whole-number sweeps belong to `tools/verify24.py`
and `tools/audit.py`. Unbounded correctness is established by the Lean build.

The search tests compile the shared C++ search checker in temporary storage (and are
skipped when no C++17 compiler is available). They exercise a damaged prime
return followed by a later valid-looking return, pair/outer returns with a wrong
number of ones, removal of the halting branch, a real negative fixture, and the
complete current baseline. Both interpreters reject the first incorrect boundary.

A positive control runs the repair search on a toy machine with a known merge,
one-transition repair and changed initial state. It must recover that proposal;
this checks that pruning does not simply reject everything.

The proved changed-return 24-state adapter is a positive control for the optional
prime-call certificate guide. Its prime return is at offset zero, while its
nonprime return for input one is at offset minus one. The guide must clear both
calls before observing later prime inputs. It accepts a return at or left of the
configured classification boundary; these observations remain search guidance,
not additional machine memory or a correctness proof.
