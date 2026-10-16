/- Adapted from Yijun Leng, goldbach_tm (Apache-2.0).
   Changed-return arithmetic fragment; separate from the accepted Tm24 construction. -/
-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import GoldbachTm.Tm24.Machine
import Mathlib.Computability.TuringMachine
import Mathlib.Tactic.Ring.RingNF
import GoldbachTm.Basic
import GoldbachTm.Format
import GoldbachTm.ListBlank

namespace ChangedReturn

open Lean Meta Elab Tactic Std Term

/-- Use the existing tape semantics and original state labels while the caller is unresolved. -/
abbrev Machine := Tm24.Machine
abbrev Cfg := Tm24.Cfg
def step (M : Machine) : Cfg → Option Cfg :=
  fun ⟨q, T⟩ ↦ (M q T.1).map fun ⟨q', a⟩ ↦ ⟨q', (T.write a.write).move a.move⟩

/-- The changed arithmetic fragment; all non-arithmetic branches belong to its caller. -/
def machine (caller : Machine) : Machine
| ⟨ 0, _⟩, Γ.one => some ⟨⟨ 1, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 1, _⟩, Γ.zero => some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 1, _⟩, Γ.one  => some ⟨⟨ 2, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 2, _⟩, Γ.zero => some ⟨⟨20, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 2, _⟩, Γ.one => some ⟨⟨12, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 4, _⟩, Γ.zero => some ⟨⟨16, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨ 4, _⟩, Γ.one => some ⟨⟨19, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 5, _⟩, Γ.zero => some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 5, _⟩, Γ.one => some ⟨⟨ 5, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨ 6, _⟩, Γ.zero => some ⟨⟨ 8, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 6, _⟩, Γ.one  => some ⟨⟨ 7, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 7, _⟩, Γ.zero => some ⟨⟨ 9, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 7, _⟩, Γ.one  => some ⟨⟨ 7, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 8, _⟩, Γ.zero => some ⟨⟨ 9, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 8, _⟩, Γ.one  => some ⟨⟨ 8, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 9, _⟩, Γ.zero => some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 9, _⟩, Γ.one  => some ⟨⟨21, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨10, _⟩, Γ.zero => some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨10, _⟩, Γ.one  => some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨11, _⟩, Γ.zero => some ⟨⟨12, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨11, _⟩, Γ.one  => some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨12, _⟩, Γ.zero => some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨12, _⟩, Γ.one  => some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨13, _⟩, Γ.zero => some ⟨⟨ 6, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨13, _⟩, Γ.one  => some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨14, _⟩, Γ.zero => some ⟨⟨15, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨14, _⟩, Γ.one  => some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨15, _⟩, Γ.zero => some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨15, _⟩, Γ.one  => some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨16, _⟩, Γ.one  => some ⟨⟨16, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨18, _⟩, Γ.zero => some ⟨⟨ 5, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨18, _⟩, Γ.one  => some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨19, _⟩, Γ.zero => some ⟨⟨ 2, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨19, _⟩, Γ.one  => some ⟨⟨19, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨20, _⟩, Γ.one  => some ⟨⟨20, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| q, b => caller q b

@[simp] theorem edge_0_one (caller : Machine) :
  machine caller 0 Γ.one = some ⟨⟨ 1, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_1_zero (caller : Machine) :
  machine caller 1 Γ.zero = some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_1_one (caller : Machine) :
  machine caller 1 Γ.one = some ⟨⟨ 2, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_2_zero (caller : Machine) :
  machine caller 2 Γ.zero = some ⟨⟨20, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_2_one (caller : Machine) :
  machine caller 2 Γ.one = some ⟨⟨12, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_4_zero (caller : Machine) :
  machine caller 4 Γ.zero = some ⟨⟨16, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_4_one (caller : Machine) :
  machine caller 4 Γ.one = some ⟨⟨19, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_5_zero (caller : Machine) :
  machine caller 5 Γ.zero = some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_5_one (caller : Machine) :
  machine caller 5 Γ.one = some ⟨⟨ 5, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_6_zero (caller : Machine) :
  machine caller 6 Γ.zero = some ⟨⟨ 8, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_6_one (caller : Machine) :
  machine caller 6 Γ.one = some ⟨⟨ 7, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_7_zero (caller : Machine) :
  machine caller 7 Γ.zero = some ⟨⟨ 9, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_7_one (caller : Machine) :
  machine caller 7 Γ.one = some ⟨⟨ 7, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_8_zero (caller : Machine) :
  machine caller 8 Γ.zero = some ⟨⟨ 9, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_8_one (caller : Machine) :
  machine caller 8 Γ.one = some ⟨⟨ 8, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_9_zero (caller : Machine) :
  machine caller 9 Γ.zero = some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_9_one (caller : Machine) :
  machine caller 9 Γ.one = some ⟨⟨21, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_10_zero (caller : Machine) :
  machine caller 10 Γ.zero = some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_10_one (caller : Machine) :
  machine caller 10 Γ.one = some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_11_zero (caller : Machine) :
  machine caller 11 Γ.zero = some ⟨⟨12, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_11_one (caller : Machine) :
  machine caller 11 Γ.one = some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_12_zero (caller : Machine) :
  machine caller 12 Γ.zero = some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_12_one (caller : Machine) :
  machine caller 12 Γ.one = some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_13_zero (caller : Machine) :
  machine caller 13 Γ.zero = some ⟨⟨ 6, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_13_one (caller : Machine) :
  machine caller 13 Γ.one = some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_14_zero (caller : Machine) :
  machine caller 14 Γ.zero = some ⟨⟨15, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem edge_14_one (caller : Machine) :
  machine caller 14 Γ.one = some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_15_zero (caller : Machine) :
  machine caller 15 Γ.zero = some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_15_one (caller : Machine) :
  machine caller 15 Γ.one = some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_16_one (caller : Machine) :
  machine caller 16 Γ.one = some ⟨⟨16, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_18_zero (caller : Machine) :
  machine caller 18 Γ.zero = some ⟨⟨ 5, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_18_one (caller : Machine) :
  machine caller 18 Γ.one = some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem edge_19_zero (caller : Machine) :
  machine caller 19 Γ.zero = some ⟨⟨ 2, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_19_one (caller : Machine) :
  machine caller 19 Γ.one = some ⟨⟨19, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem edge_20_one (caller : Machine) :
  machine caller 20 Γ.one = some ⟨⟨20, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

def run (caller : Machine) (start : Cfg) : (n : Nat) -> Option Cfg
| 0 => some start
| Nat.succ n => match (run caller start n) with
                | none => none
                | some cfg =>  step (machine caller) cfg


-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/binderIdent.20vs.20Ident/near/402516388
def toBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

elab "forwardR" g:ident : tactic => withSynthesize <| withMainContext do
  let some ldecl := (← getLCtx).findFromUserName? g.getId
    | throwErrorAt g m!"Identifier {g} not found"
  match ldecl with
  | LocalDecl.cdecl _ _ _ (Expr.app (Expr.app _ (Expr.app fn arg)) _) _ _ =>
      let argType ← inferType arg
      if ← isDefEq argType (mkConst ``Nat) then
        let arg ← Elab.Term.exprToSyntax arg
        let fn ← Elab.Term.exprToSyntax fn
        evalTactic (← `(tactic| (
            have h : $fn ($arg + 1) = $fn ($arg + 1) := rfl
            nth_rewrite 2 [run] at h
            simp [*, step, Option.map, Turing.Tape.write, Turing.Tape.move] at h
            try simp! [*, -run] at h
            try ring_nf at h
            clear $g
            rename_i $(toBinderIdent g)
        )))
      else
        throwError "The first argument of {g} is not a Nat"
  | _ => logInfo m!"please forward on nth_cfg i = some ⟨...⟩"



end ChangedReturn
