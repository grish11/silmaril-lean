module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls

/-! # Exact reifier replay for ordered primitive calls -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches)
open Region.Paper.WithComputedCallReturns
open Morphism.CaseSSA (erase)
open LetCase.Structural.Finite (Context Types)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Schedule

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {r s : Region Φ} {fs gs : List Φ}

/-- The scheduled region types at the original singleton exit. -/
theorem CallSchedule.valueBranches (p : CallSchedule Γ r A fs) : ValueBranches Γ r [A] :=
  p.valueBranches_proof

/-- Substituting constructor values keeps all requests in order. -/
theorem CallSchedule.subst {Δ : VCtx τ} {θ : Nat → Tm Φ} (p : CallSchedule Γ r A fs)
    (values : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    CallSchedule Δ (r.substVars θ) A fs :=
  p.subst_proof values

/-- Rename the captured variables without changing the call schedule. -/
theorem CallSchedule.rename {Δ : VCtx τ} {ρ : Nat → Nat} (p : CallSchedule Γ r A fs)
    (typed : Ren Γ Δ ρ) : CallSchedule Δ (r.renameVars ρ) A fs :=
  p.rename_proof typed

/-- Continuation composition preserves captures and concatenates call order. -/
theorem CallSchedule.splice (p : CallSchedule Γ r A fs) (q : CallSchedule (A :: Γ) s B gs) :
    CallSchedule Γ (r.lsubst (fun _ => s)) B (fs ++ gs) :=
  p.splice_proof q

/-- Run the left schedule before the right. Weaken the right under the
left result and return the two values in their original component order. -/
theorem CallSchedule.pair (p : CallSchedule Γ r A fs) (q : CallSchedule Γ s B gs) :
    CallSchedule Γ (r.lsubst (fun _ =>
      (s.renameVars Nat.succ).lsubst (fun _ => .br 0 (.pair (.var 1) (.var 0)))))
      (product A B) (fs ++ gs) :=
  p.pair_proof q

/-- The literal guarded return and the actual reification of an admitted
exact operand replay to the same typed region in source call order. -/
theorem operand_schedule {ε : Type w} [HasEff Φ ε] (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {D : τ} (a : Operand Φ β D)
    (shape : CallOperand (erase a.1)) :
    ∃ r, CallSchedule β.toList r D (operandCalls (erase a.1)) ∧
      ConstructorJoin.Eqv pe β.toList ((Code.br a).guardedSSA 0) r [D] ∧
      ConstructorJoin.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA 0) r [D] :=
  operand_schedule_with_proof pe (fun e => e) false (fun h => Bool.noConfusion h) a shape

/-- With unrestricted pair returns, both children of a pair can be
arbitrary admitted operands. The two exact guarded endpoints replay to
one native schedule. -/
theorem operand_pair_schedule {ε : Type w} [HasEff Φ ε] (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {D : τ} (a : Operand Φ β D)
    (shape : CallOperand (erase a.1) true) :
    ∃ r, CallSchedule β.toList r D (operandCalls (erase a.1) true) ∧
      OrderedPairs.Eqv pe β.toList ((Code.br a).guardedSSA 0) r [D] ∧
      OrderedPairs.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA 0) r [D] :=
  operand_schedule_with_proof pe Or.inl true (fun _ => Or.inr) a shape

end Schedule

/-- At a written guarded outward endpoint, an admitted compilation suffices
to replay ordered calls back to the original region. -/
theorem Endpoint.call_schedule {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} (p : Endpoint Φ β A)
    (guarded : ValueBranches β.toList p.region [A]) (shape : CallOperand (erase p.compile.1)) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase p.compile.1)) ∧
      ConstructorJoin.Eqv false β.toList p.region r [A] :=
  call_schedule_with_proof false (fun e => e) (fun h => Bool.noConfusion h) p guarded shape

/-- The extra computed-call step is sound at the original typed outward
arrows under the same #4334 model assumptions. -/
theorem Endpoint.call_sound {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} {p q : Endpoint Φ β A}
    (h : p.CallEqv q) : p.Valid q :=
  call_sound_proof h

/-- Replay a guarded written endpoint whose exact compilation admits
computed pair operands. The schedule retains the original typed exit. -/
theorem Endpoint.pair_call_schedule {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} (p : Endpoint Φ β A)
    (guarded : ValueBranches β.toList p.region [A]) (shape : CallOperand (erase p.compile.1) true) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase p.compile.1) true) ∧
      OrderedPairs.Eqv false β.toList p.region r [A] :=
  call_schedule_with_proof true Or.inl (fun _ => Or.inr) p guarded shape

/-- The enlarged relation is sound at the original outward endpoints in
the same coherent shared-tensor model class. -/
theorem Endpoint.pair_call_sound {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} {p q : Endpoint Φ β A}
    (h : p.PairCallEqv q) : p.Valid q :=
  pair_call_sound_proof h

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
