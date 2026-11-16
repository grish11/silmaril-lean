module

public import Silmaril.Logic.ModalMu.FiniteVector.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

@[expose] public section
noncomputable section
namespace Silmaril.Logic.ModalMu.FiniteVector.Examples

/-- Four genuinely coupled equations capturing P: X0=P∨X1, X1=X2,
X2=X3, X3=X0. No restriction on the model's carrier. -/
def captured {S : Signature} : System S 4 1 :=
  ⟨Fin.cases (.disj (.var 4) (.var 1))
    (Fin.cases (.var 2) (Fin.cases (.var 3) (fun _ => .var 0)))⟩

theorem captured_mu {S : Signature} (M : Model S) (ρ : Env M.World 1) :
    captured.denote false M ρ = fun _ => ρ 0 := by
  let op := captured.operator M ρ
  have upper : op.lfp ≤ fun _ => ρ 0 := by
    apply op.lfp_le
    intro i
    fin_cases i
    · exact Set.union_subset le_rfl le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
  have first : ρ 0 ⊆ op.lfp 0 := by
    intro w hw
    have h : w ∈ op op.lfp 0 := Or.inl hw
    exact (congrArg (fun X => w ∈ X 0) op.map_lfp).mp h
  have h1 : op.lfp 2 = op.lfp 1 := congrFun op.map_lfp 1
  have h2 : op.lfp 3 = op.lfp 2 := congrFun op.map_lfp 2
  have h3 : op.lfp 0 = op.lfp 3 := congrFun op.map_lfp 3
  apply le_antisymm upper
  intro i
  fin_cases i
  · exact first
  · exact first.trans_eq (h3.trans (h2.trans h1))
  · exact first.trans_eq (h3.trans h2)
  · exact first.trans_eq h3

theorem captured_nu {S : Signature} (M : Model S) (ρ : Env M.World 1) :
    captured.denote true M ρ = fun _ => Set.univ := by
  apply le_antisymm le_top
  change (fun _ => Set.univ) ≤ (captured.operator M ρ).gfp
  apply OrderHom.le_gfp
  intro i
  fin_cases i
  · exact Set.subset_union_right
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

/-- Both uniform kinds evaluate actual compiled formulas, not a special-case solver. -/
theorem captured_compiled {S : Signature} (M : Model S) (ρ : Env M.World 1) :
    (fun i => (captured.compile false i).denote M ρ) = (fun _ => ρ 0) ∧
    (fun i => (captured.compile true i).denote M ρ) = (fun _ => Set.univ) :=
  ⟨(captured.compile_correct false M ρ).trans (captured_mu M ρ),
    (captured.compile_correct true M ρ).trans (captured_nu M ρ)⟩

/-- Zero equations compile to the unique empty family. -/
theorem zero_compiled {S : Signature} {n : Nat} (s : System S 0 n)
    (greatest : Bool) (M : Model S) (ρ : Env M.World n) :
    (fun i => (s.compile greatest i).denote M ρ) = s.denote greatest M ρ :=
  s.compile_correct greatest M ρ

/-- A one-equation self loop distinguishes μ and ν in every nonempty pointed model. -/
def self {S : Signature} : System S 1 0 := ⟨fun _ => .var 0⟩

theorem self_kinds {S : Signature} (M : Model S) :
    (self.compile false 0).denote M emptyEnv = ∅ ∧
    (self.compile true 0).denote M emptyEnv = Set.univ := by
  have low : self.denote false M emptyEnv = (fun _ => ∅) := by
    apply le_antisymm
    · exact (self.operator M emptyEnv).lfp_le (by intro i; exact le_rfl)
    · exact bot_le
  have high : self.denote true M emptyEnv = (fun _ => Set.univ) := by
    apply le_antisymm le_top
    exact (self.operator M emptyEnv).le_gfp (by intro i; exact le_rfl)
  exact ⟨congrFun ((self.compile_correct false M emptyEnv).trans low) 0,
    congrFun ((self.compile_correct true M emptyEnv).trans high) 0⟩

/-- Three modal equations form a cycle. -/
def modalCycle {S : Signature} (a : S.Action) : System S 3 0 :=
  ⟨Fin.cases (.diamond a (.var 1))
    (Fin.cases (.diamond a (.var 2)) (fun _ => .diamond a (.var 0)))⟩

/-- A greatest block cannot manufacture successors at deadlock, for any carrier. -/
theorem modal_deadlock {S : Signature} (a : S.Action) (M : Model S)
    (dead : ∀ w v, ¬ M.step a w v) (greatest : Bool) :
    (fun i => ((modalCycle a).compile greatest i).denote M emptyEnv) = fun _ => ∅ := by
  let op := (modalCycle a).operator M emptyEnv
  have constant (X : Env M.World 3) : op X = fun _ => ∅ := by
    funext i
    apply Set.ext
    intro w
    fin_cases i <;>
      change (∃ v, M.step a w v ∧ _) ↔ False
    all_goals constructor
    all_goals first | intro ⟨v, h, _⟩; exact dead w v h | intro h; exact h.elim
  have unfold : op (Vector.fixed greatest op) = Vector.fixed greatest op := by
    cases greatest
    · exact op.map_lfp
    · exact op.map_gfp
  rw [constant] at unfold
  exact ((modalCycle a).compile_correct greatest M emptyEnv).trans unfold.symm

/-- On a serial action every coordinate of the greatest modal cycle is full. -/
theorem modal_serial_nu {S : Signature} (a : S.Action) (M : Model S)
    (serial : ∀ w, ∃ v, M.step a w v) :
    (fun i => ((modalCycle a).compile true i).denote M emptyEnv) = fun _ => Set.univ := by
  have full : (modalCycle a).denote true M emptyEnv = fun _ => Set.univ := by
    apply le_antisymm le_top
    apply OrderHom.le_gfp
    intro i w _
    fin_cases i <;> change (∃ v, M.step a w v ∧ v ∈ Set.univ)
    all_goals obtain ⟨v, hv⟩ := serial w
    all_goals exact ⟨v, hv, trivial⟩
  exact ((modalCycle a).compile_correct true M emptyEnv).trans full

/-- Pointed models witness that μ and ν are not interchangeable. -/
theorem self_distinct {S : Signature} (M : Model S) :
    (self.compile false 0).denote M emptyEnv ≠ (self.compile true 0).denote M emptyEnv := by
  intro h
  have hp : M.point ∈ (self.compile true 0).denote M emptyEnv := by
    rw [(self_kinds M).2]
    trivial
  have hn : M.point ∈ (self.compile false 0).denote M emptyEnv := h.symm ▸ hp
  rw [(self_kinds M).1] at hn
  exact hn

end Silmaril.Logic.ModalMu.FiniteVector.Examples
