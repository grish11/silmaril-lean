module

public import Silmaril.Logic.Algebraic.Initial.Generation.Thms

/-! Authored semantic controls over the actual public EQ syntax. No finite-sort
or finite-operation instance is supplied to the generic generation theorem. -/

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Generation.Examples

open Silmaril.Logic.Institution.Examples
open Presented.Characterization

namespace InfiniteChain

/-- Infinitely many genuine sorts and one distinct cross-sorted operation for
every natural number, in addition to the single seed. -/
inductive Operation : (n : Nat) → (Fin n → Nat) → Nat → Type
  | seed : Operation 0 Fin.elim0 0
  | advance (s : Nat) : Operation 1 (fun _ => s) (s + 1)

abbrev signature : EQ.Signature := ⟨Nat, Operation⟩

/-- Equal underlying carrier types do not identify the different source sorts
or the distinct dependent operation profiles. -/
abbrev model : EQ.Algebra signature where
  carrier _ := Nat
  op := fun {_ _ _} op args => by
    cases op with
    | seed => exact 0
    | advance _ => exact args 0 + 1

def term : (s : Nat) → Ground signature s
  | 0 => .app .seed (fun i => i.elim0)
  | s + 1 => .app (.advance s) (fun _ => term s)

theorem evaluate_eq_sort {s : Nat} (t : Ground signature s) :
    evaluate model t = s := by
  refine EQ.Term.rec (motive := fun s (t : Ground signature s) => evaluate model t = s) ?_ ?_ t
  · intro i
    exact i.elim0
  · intro n w s op args ih
    cases op with
    | seed => rfl
    | advance s => exact congrArg (fun n : Nat => n + 1) (ih 0)

/-- The infinite product fixed point has one generated value at each original
sort, and is not the whole independently chosen carrier. -/
theorem generated_singleton (s : Nat) : generated model s = {s} := by
  change (groundStep model).lfp s = {s}
  rw [groundStep_lfp_eq_range]
  apply Set.ext
  intro x
  change (∃ t : Ground signature s, evaluate model t = x) ↔ x = s
  constructor
  · rintro ⟨t, ht⟩
    exact ht.symm.trans (evaluate_eq_sort t)
  · intro hx
    subst x
    exact ⟨term s, evaluate_eq_sort (term s)⟩

theorem not_generated : ¬ Presented.Characterization.Generated model := by
  intro h
  obtain ⟨t, ht⟩ := h 0 1
  have wrong : (1 : Nat) = 0 := ht.symm.trans (evaluate_eq_sort t)
  cases wrong

end InfiniteChain

namespace Mutual

/-- Inputs really change sort; there is no homogeneous tuple replacement. -/
inductive Operation : (n : Nat) → (Fin n → Bool) → Bool → Type
  | seed : Operation 0 Fin.elim0 false
  | toRight : Operation 1 (fun _ => false) true
  | toLeft : Operation 1 (fun _ => true) false

abbrev signature : EQ.Signature := ⟨Bool, Operation⟩

/-- The two carriers are independent and have different actual types. -/
abbrev model : EQ.Algebra signature where
  carrier := fun | false => Nat | true => Bool
  op := fun {_ _ _} op args => by
    cases op with
    | seed => exact 0
    | toRight => exact decide (args 0 = 0)
    | toLeft => exact cond (args 0) 0 1

def left : Ground signature false := .app .seed (fun i => i.elim0)
def right : Ground signature true := .app .toRight (fun _ => left)

theorem left_generated : (0 : Nat) ∈ generated model false :=
  evaluate_mem_generated model left

theorem right_generated : true ∈ generated model true :=
  evaluate_mem_generated model right

/-- A sort-indexed invariant distinguishes independently typed carrier values. -/
abbrev invariant : Family model := fun s =>
  match s with
  | false => {0}
  | true => {true}

theorem invariant_closed : groundStep model invariant ≤ invariant := by
  rintro s x ⟨n, w, op, args, hargs, rfl⟩
  cases op with
  | seed => rfl
  | toRight =>
      have hzero : args 0 = (0 : Nat) := hargs 0
      change decide (args 0 = 0) = true
      rw [hzero]
      rfl
  | toLeft =>
      have htrue : args 0 = true := hargs 0
      change cond (args 0) 0 1 = (0 : Nat)
      rw [htrue]
      rfl

theorem extra_left_not_generated : (1 : Nat) ∉ generated model false := by
  intro h
  have wrong : (1 : Nat) = 0 := generated_le_of_closed model invariant invariant_closed false h
  cases wrong

theorem extra_right_not_generated : false ∉ generated model true := by
  intro h
  have wrong : false = true := generated_le_of_closed model invariant invariant_closed true h
  cases wrong

end Mutual

namespace Unseeded

inductive Operation : (n : Nat) → (Fin n → Bool) → Bool → Type
  | toRight : Operation 1 (fun _ => false) true
  | toLeft : Operation 1 (fun _ => true) false

abbrev signature : EQ.Signature := ⟨Bool, Operation⟩

/-- With no seed, a mutual cycle cannot manufacture a generated value, for ANY
actual algebra, even when its independently chosen carriers are inhabited. -/
theorem groundStep_bot (M : EQ.Algebra signature) : groundStep M ⊥ = ⊥ := by
  funext s
  apply Set.ext
  intro x
  constructor
  · rintro ⟨n, w, op, args, hargs, _⟩
    cases op with
    | toRight => exact hargs 0
    | toLeft => exact hargs 0
  · intro hx
    exact hx.elim

theorem generated_bot (M : EQ.Algebra signature) : generated M = ⊥ :=
  le_antisymm (generated_le_of_closed M ⊥ (groundStep_bot M).le) bot_le

/-- The same signature admits genuinely empty carriers, without defaults. -/
abbrev emptyModel : EQ.Algebra signature where
  carrier _ := PEmpty
  op := fun {_ _ _} op args => by
    cases op with
    | toRight => exact args 0
    | toLeft => exact args 0

theorem no_ground (s : Bool) : IsEmpty (Ground signature s) :=
  ⟨fun t => (evaluate emptyModel t).elim⟩

theorem empty_generated : Presented.Characterization.Generated emptyModel := by
  intro s x
  exact x.elim

end Unseeded

namespace ZeroSorts

abbrev signature : EQ.Signature := ⟨PEmpty, fun _ _ _ => PEmpty⟩

abbrev model : EQ.Algebra signature where
  carrier s := s.elim
  op := fun {_ _ _} op => op.elim

theorem generated_top : generated model = ⊤ := by
  funext s
  exact s.elim

theorem generated_bottom : generated model = ⊥ := by
  funext s
  exact s.elim

end ZeroSorts

end Silmaril.Logic.Algebraic.Initial.Generation.Examples
