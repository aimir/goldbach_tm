# Changed-return arithmetic fragment

This separate namespace formalizes the seven-rewrite classifier recorded in
`reference/optimization23.json`. It does not change the accepted 24-state table
or claim a 23-state blank-tape machine.

`Machine.lean` retains original `Fin 24` state labels. `machine caller` fixes the
arithmetic branches and leaves every other branch to `caller`. `run caller start`
executes from any configuration. The arithmetic contract therefore applies to
future compatible callers without assuming any particular initialization.

`Contract.lean` defines the input and exact exits. `classifies` proves the right
exit for every positive unary input, with arbitrary separated contexts and strict
progress. `terminates` connects both exits to halting and proves termination.
The prime exit is on the erased first input cell; the nonprime exit preserves
all cells and is on the input's left separator.

The modular-counter argument follows the existing Tm24 proof. The changed
failed-divisor restoration and prime tail are proved for the new transitions.
The scan and counter modules remain separated by the same proof responsibilities
as Tm24. All contracts use ordinary kernel proofs at the pinned Lean toolchain.
