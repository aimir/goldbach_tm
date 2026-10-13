# Shared definitions and machine proof

The unchanged upstream `Basic.lean` defines `Goldbach` with `Nat.Prime`, its finite
search predicate, and the induction principle for arbitrarily late boundaries.
`Format.lean` and `ListBlank.lean` support tape representation and simulation.

[The current proof](Tm24/README.md) uses these definitions. The default-build
[headline theorem](../GoldbachTm.lean) exposes the full mathematical statement.
There is no second copy of the old 25-state proof in this tree.
