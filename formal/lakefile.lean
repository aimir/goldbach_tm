import Lake
open Lake DSL
package "goldbach_tm" where
  version := v!"0.1.0"
require "leanprover-community" / "mathlib"
@[default_target]
lean_lib «GoldbachTm»
lean_exe «sim24» where
  root := `GoldbachTm.Tm24.Sim24
