module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumContinuation

/-! # Case schedules followed by a primitive and a typed continuation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Continuation

open Region (HasType ValueBranches)
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.UnaryReturn.Beta.Constructors (inlSequence inrSequence)
open Morphism.CaseSSA (erase)
open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂

section Native

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε]
  {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {A B D : τ} {f : Φ} {p q : Region Φ} {e l r : Tm Φ}

theorem ofSums (h : SumBind.Eqv pe Γ p q L) : Eqv pe Γ p q L :=
  ofSums_proof h

/-- Split a returned case at its exact native singleton result interface. -/
theorem split_return (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l D)
    (hr : Tm.HasType (B :: Γ) r D) :
    Eqv pe Γ (returnOnce (.case e l r)) (.case e (returnOnce l) (returnOnce r)) [D] :=
  split_return_proof he hl hr

/-- Split the literal return of a binary-let expression. Both sides bind
the same product, in left-field then right-field order, before the body. -/
theorem split_let₂ {a b : Tm Φ} (ha : Tm.HasType Γ a (product A B))
    (hb : Tm.HasType (B :: A :: Γ) b D) :
    Eqv pe Γ (returnOnce (.let₂ a b)) (.let₂ a (returnOnce b)) [D] :=
  split_let₂_proof ha hb

/-- Evaluate an arbitrary typed payload once before tagging it on the left. -/
theorem split_inl {a : Tm Φ} (ha : Tm.HasType Γ a A) :
    Eqv pe Γ (returnOnce (.inl a)) (inlSequence a) [coprod A B] :=
  split_inl_proof ha

/-- Evaluate an arbitrary typed payload once before tagging it on the right. -/
theorem split_inr {a : Tm Φ} (ha : Tm.HasType Γ a B) :
    Eqv pe Γ (returnOnce (.inr a)) (inrSequence a) [coprod A B] :=
  split_inr_proof ha

/-- Split a returned empty elimination at its original singleton result.
Only the producer of the empty value is evaluated before the eliminator. -/
theorem split_abort {a : Tm Φ} (ha : Tm.HasType Γ a empty) :
    Eqv pe Γ (returnOnce (.abort a)) (.let₁ a (returnOnce (.abort (.var 0)))) [D] :=
  split_abort_proof ha

/-- Use the computed case as the argument to a later primitive; leave the
body at its original ordered exits under the primitive reply binder. -/
theorem call_replay (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l (instrSrc f))
    (hr : Tm.HasType (B :: Γ) r (instrSrc f)) (hq : HasType (instrTrg f :: Γ) q L)
    (scheduled : ValueBranches Γ p [instrSrc f])
    (producer : Eqv pe Γ (.case e (returnOnce l) (returnOnce r)) p [instrSrc f]) :
    Eqv pe Γ (.let₁ (.op f (.case e l r)) q) (p.lsubst (fun _ => invoke f q)) L :=
  call_replay_proof he hl hr hq scheduled producer

/-- The contextual extension preserves exactly typed arrows in the same
coherent shared-tensor, central-unit strong Elgot Freyd class. -/
theorem sound {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
    [RegionTypingCoherent (Φ := Φ) J M]
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    (h : Eqv pe Γ p q L) (hp : HasType Γ p L) (hq : HasType Γ q L) :
    denoteRegion J M hp = denoteRegion J M hq :=
  sound_proof J M shared h hp hq

end Native

/-- Weakening or renaming captures leaves the request paths unchanged. -/
theorem rename_schedule {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    {Γ Δ : VCtx τ} {L : LCtx τ} {p : Region Φ} {paths : List (List Φ × Nat)} {ρ : Nat → Nat}
    (h : Schedule Γ p L paths) (typed : Ren Γ Δ ρ) :
    Schedule Δ (p.renameVars ρ) L paths :=
  rename_schedule_proof h typed

/-- A typed case schedule can feed a fresh call and an arbitrary typed case
schedule on its reply. Each resulting path contains one new call occurrence. -/
theorem splice {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    {Γ : VCtx τ} {L : LCtx τ} {f : Φ} {p q : Region Φ} {before after : List (List Φ × Nat)}
    (producer : Schedule Γ p [instrSrc f] before) (body : Schedule (instrTrg f :: Γ) q L after) :
    Schedule Γ (p.lsubst (fun _ => invoke f q)) L (callPaths f before after) :=
  splice_proof producer body rfl

section Operands

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {L : LCtx (Ty α)} {A B : Ty α} {f : Φ} {q : Region Φ}
  {after : List (List Φ × Nat)} {n : Nat} {β : BoundCtx (Ty α) n}

/-- Normalize the original computed argument, with its branch structure,
through the later call and the already scheduled body. -/
theorem operand_schedule (e : Operand Φ β (Ty.coprod A B))
    (l : Operand Φ (β.snoc A) (instrSrc f)) (r : Operand Φ (β.snoc B) (instrSrc f))
    (he : CallOperand (erase e.1) true) (hl : CallOperand (erase l.1) true)
    (hr : CallOperand (erase r.1) true) (body : Schedule (instrTrg f :: β.toList) q L after) :
    ∃ s before, CasePaths (operandCalls (erase e.1) true) (operandCalls (erase l.1) true)
        (operandCalls (erase r.1) true) 0 0 before ∧
      Schedule β.toList s L (callPaths f before after) ∧
      Eqv pe β.toList (.let₁ (.op f (.case (erase e.1) (erase l.1) (erase r.1))) q) s L :=
  operand_schedule_proof e l r he hl hr body

/-- The actual guarded reification of the returned call also replays at
its original output label, including in a larger ordered interface. -/
theorem guarded_operand_schedule {i : Nat} (out : At L i (instrTrg f))
    (e : Operand Φ β (Ty.coprod A B)) (l : Operand Φ (β.snoc A) (instrSrc f))
    (r : Operand Φ (β.snoc B) (instrSrc f))
    (he : CallOperand (erase e.1) true) (hl : CallOperand (erase l.1) true)
    (hr : CallOperand (erase r.1) true) :
    ∃ s before, CasePaths (operandCalls (erase e.1) true) (operandCalls (erase l.1) true)
        (operandCalls (erase r.1) true) 0 0 before ∧
      Schedule β.toList s L (callPaths f before [([], i)]) ∧
      Eqv pe β.toList ((Code.ofLetCase (.op (f := f) (.case e.2 l.2 r.2))).guardedSSA i) s L :=
  operand_schedule e l r he hl hr (.ret out (.var (i := 0) rfl))

end Operands

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Continuation
