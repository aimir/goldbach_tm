# Literal machine tables

- **`goldbach24.tm`** is the current formally verified machine. Its header specifies
  **initial state 18**. It has 24 working states; original state 22 is removed and
  original states 23/24 are renumbered 22/23.
- `goldbach25.tm` is the pinned baseline, initially state 0.

Each row is `state: transition-on-0 transition-on-1`. `1R22`, for example, writes
1, moves right and enters state 22. `HALT` performs no write or move, matching the
Lean `none` semantics. Both machines start on an all-zero two-way infinite tape.
The initial state's numeric label is only a label and adds no working states.

`tools/verify24.py` checks the current table against Lean and the one-edge change.
`tools/audit.py` checks the baseline against its pinned original Lean source.
