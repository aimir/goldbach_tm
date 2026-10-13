/- Adapted from Yijun Leng, goldbach_tm (Apache-2.0).
   Updated for the 24-state table and initialization; see reference/upstream.json. -/
import GoldbachTm.Tm24.Machine
import GoldbachTm.Basic

open Tm24

unsafe def foo (cfg : Cfg) : IO Unit :=
match (step machine cfg) with
| some cfg => do
                IO.println s!"{cfg}"
                foo cfg
| none => IO.println s!"halt"


unsafe def main : List String → IO Unit
| _ => foo (init [])
