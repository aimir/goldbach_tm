import GoldbachTm.ChangedReturn.Contract

namespace ChangedReturn.Adapter

/-- A concrete compatibility adapter, using state 3 as a caller helper.
It restores the erased first cell and skips the input's left separator.
This construction still uses 24 states. -/
def caller : Machine
  | 20, Γ.zero => some ⟨3, ⟨Turing.Dir.left, Γ.one⟩⟩
  | 3, Γ.zero => some ⟨22, ⟨Turing.Dir.left, Γ.zero⟩⟩
  | q, b => Tm24.machine q b

/-- The same exact blank input as the accepted machine. -/
def start : Cfg := Tm24.init []

@[simp] theorem caller_edge_0_0 : machine caller 0 Γ.zero =
  some ⟨10, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem caller_edge_3_0 : machine caller 3 Γ.zero =
  some ⟨22, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem caller_edge_3_1 : machine caller 3 Γ.one =
  some ⟨4, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem caller_edge_16_0 : machine caller 16 Γ.zero =
  some ⟨17, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem caller_edge_17_0 : machine caller 17 Γ.zero =
  some ⟨9, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem caller_edge_17_1 : machine caller 17 Γ.one =
  some ⟨23, ⟨Turing.Dir.left, Γ.zero⟩⟩ := rfl

@[simp] theorem caller_edge_20_0 : machine caller 20 Γ.zero =
  some ⟨3, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem caller_edge_21_0 : machine caller 21 Γ.zero =
  some ⟨17, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem caller_edge_21_1 : machine caller 21 Γ.one =
  some ⟨21, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

@[simp] theorem caller_edge_22_0 : machine caller 22 Γ.zero =
  some ⟨0, ⟨Turing.Dir.right, Γ.zero⟩⟩ := rfl

@[simp] theorem caller_edge_22_1 : machine caller 22 Γ.one =
  some ⟨22, ⟨Turing.Dir.left, Γ.one⟩⟩ := rfl

@[simp] theorem caller_edge_23_0 : machine caller 23 Γ.zero =
  none := rfl

@[simp] theorem caller_edge_23_1 : machine caller 23 Γ.one =
  some ⟨22, ⟨Turing.Dir.right, Γ.one⟩⟩ := rfl

/-- Exact blank initialization reaches the canonical boundary for four. -/
theorem cfg27 : run caller start 27 = some ⟨21,
    ⟨Γ.zero, Turing.ListBlank.mk (List.replicate 4 Γ.one), Turing.ListBlank.mk []⟩⟩ := by
  have h : run caller start 0 = some ⟨18,
    ⟨Γ.zero, Turing.ListBlank.mk [], Turing.ListBlank.mk []⟩⟩ := rfl
  iterate 27 forwardR h
  simp [h]
  simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  right
  use 2
  tauto

end ChangedReturn.Adapter
