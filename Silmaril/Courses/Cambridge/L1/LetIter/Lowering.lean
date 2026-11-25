module

public import Silmaril.Courses.Cambridge.L1.LetIter.Model
public import Silmaril.Courses.Cambridge.L1.Metatheory.Inversion

/-! Syntax-directed lowering carries the target term and its proof-relevant
LetIter typing derivation together. L1 has no local value variables, so the
translation can run under any bound context introduced by LetIter. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.LetIter

open Silmaril.Isotope (BoundCtx Ctx)
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (BoundDen TyDen)
open EffectfulDenotational (Computation)

abbrev Lowered {n : Nat} (β : BoundCtx TargetTy n) (A : TargetTy) :=
  Σ t : Tm Empty Instr n,
    Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless.HasType Instr
      (.nil : Ctx Empty TargetTy) β t A

/-- Translate the original L1 syntax, using its typing proof to determine
the operand and result types. LetIter supplies sequencing, cases and iteration. -/
def lower {Γ : TypeEnv} : (e : Expr) → (T : L1.Ty) → L1.HasType Γ e T →
    {n : Nat} → (β : BoundCtx TargetTy n) → Lowered β (lowerTy T)
  | .int z, T, typed, _, _ => by
      have equal := typed.int_inversion
      subst T
      exact ⟨.op (.literal z) .unit, .op .unit⟩
  | .bool b, T, typed, _, _ => by
      have equal := typed.bool_inversion
      subst T
      cases b with
      | false => exact ⟨.inr .unit, .inr .unit⟩
      | true => exact ⟨.inl .unit, .inl .unit⟩
  | .skip, T, typed, _, _ => by
      have equal := typed.skip_inversion
      subst T
      exact ⟨.unit, .unit⟩
  | .deref loc, T, typed, _, _ => by
      have equal := typed.deref_inversion.1
      subst T
      exact ⟨.op (.read loc) .unit, .op .unit⟩
  | .assign loc e, T, typed, _, β => by
      obtain ⟨equal, _, operand⟩ := typed.assign_inversion
      subst T
      let rhs := lower e .int operand β
      exact ⟨.op (.write loc) rhs.1, .op rhs.2⟩
  | .binary l .add r, T, typed, _, β => by
      have operands : T = .int ∧ L1.HasType Γ l .int ∧ L1.HasType Γ r .int := by
        simpa using typed.binary_inversion
      obtain ⟨equal, left, right⟩ := operands
      subst T
      let a := lower l .int left β
      let b := lower r .int right β
      exact ⟨.op .add (.pair a.1 b.1), .op (.pair a.2 b.2)⟩
  | .binary l .ge r, T, typed, _, β => by
      have operands : T = .bool ∧ L1.HasType Γ l .int ∧ L1.HasType Γ r .int := by
        simpa using typed.binary_inversion
      obtain ⟨equal, left, right⟩ := operands
      subst T
      let a := lower l .int left β
      let b := lower r .int right β
      exact ⟨.op .ge (.pair a.1 b.1), .op (.pair a.2 b.2)⟩
  | .cond test yes no, T, typed, _, β =>
      let guard := lower test .bool typed.cond_inversion.1 β
      let left := lower yes T typed.cond_inversion.2.1 (.snoc β unitTy)
      let right := lower no T typed.cond_inversion.2.2 (.snoc β unitTy)
      ⟨.case guard.1 left.1 right.1, .case guard.2 left.2 right.2⟩
  | .seq first second, T, typed, _, β =>
      let a := lower first .unit typed.seq_inversion.1 β
      let b := lower second T typed.seq_inversion.2 (.snoc β unitTy)
      ⟨.let₁ a.1 b.1, .let₁ a.2 b.2⟩
  | .loop test body, T, typed, _, β => by
      obtain ⟨equal, guardTyped, bodyTyped⟩ := typed.loop_inversion
      subst T
      let loopCtx := BoundCtx.snoc β unitTy
      let guard := lower test .bool guardTyped loopCtx
      let command := lower body .unit bodyTyped (.snoc loopCtx unitTy)
      exact ⟨.iter .unit (.case guard.1 (.let₁ command.1 (.inr .unit)) (.inl .unit)),
        .iter .unit (.case guard.2 (.let₁ command.2 (.inr .unit)) (.inl .unit))⟩
termination_by structural e => e

/-- The direct monadic evaluation of a translated LetIter derivation. -/
noncomputable def evalLower {Γ : TypeEnv} {e : Expr} {T : L1.Ty} {n : Nat}
    {β : BoundCtx TargetTy n} (typed : L1.HasType Γ e T) (ρ : BoundDen β) :
    Computation (TyDen (lowerTy T)) :=
  Silmaril.Isotope.LetIter.ProofRelevant.Semantics.denote (ε := Bool)
    (lower e T typed β).2 PUnit.unit ρ

end Silmaril.Courses.Cambridge.L1.LetIter
