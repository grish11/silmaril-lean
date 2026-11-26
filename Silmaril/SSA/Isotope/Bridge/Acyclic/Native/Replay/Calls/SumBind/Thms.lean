module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind

/-! # Native case replay and typed request paths -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind

open Region (HasType ValueBranches)
open Region.Paper.RetainedCase (boundCase)
open Morphism.CaseSSA (erase)
open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂

section Native

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε]
  {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {p l l' r r' : Region Φ} {a b : Tm Φ}

theorem ofProducts (h : ProductBind.Eqv pe Γ p r L) : Eqv pe Γ p r L :=
  ofProducts_proof h

/-- A single guarded producer transfer feeds either typed arm at its original
outward interface. The two payload binders retain the original captures. -/
theorem bind_replay (ha : Tm.HasType Γ a (coprod A B)) (hp : ValueBranches Γ p [coprod A B])
    (producer : Eqv pe Γ ((Region.br 0 a).bindBranchArguments) p [coprod A B])
    (left : Eqv pe (A :: Γ) l l' L) (right : Eqv pe (B :: Γ) r r' L)
    (hl : ValueBranches (A :: Γ) l' L) (hr : ValueBranches (B :: Γ) r' L) :
    Eqv pe Γ (.case a l r) (p.lsubst (fun _ => boundCase l' r')) L :=
  bind_replay_proof ha hp producer left right hl hr

/-- Left case β followed by substitution of the constructor payload. -/
theorem constructor_left (ha : Tm.BranchValue Γ a A)
    (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
    Eqv pe Γ (.case (.inl a) l r) (l.substVars (Tm.singleSubst a)) L :=
  constructor_left_proof ha hl hr

/-- Right case β followed by substitution of the constructor payload. -/
theorem constructor_right (hb : Tm.BranchValue Γ b B)
    (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
    Eqv pe Γ (.case (.inr b) l r) (r.substVars (Tm.singleSubst b)) L :=
  constructor_right_proof hb hl hr

theorem Schedule.valueBranches {paths : List (List Φ × Nat)}
    (h : Schedule Γ p L paths) : ValueBranches Γ p L :=
  h.valueBranches_proof

/-- Preserve the two exact region arrows in the existing coherent
shared-tensor, central-unit strong Elgot Freyd class. -/
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
    (h : Eqv pe Γ p r L) (hp : HasType Γ p L) (hr : HasType Γ r L) :
    denoteRegion J M hp = denoteRegion J M hr :=
  sound_proof J M shared h hp hr

end Native

section Schedule

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {A B D E : Ty α} {i j : Nat}
  {p l r : Region Φ} {fs ls rs : List Φ}

/-- Splice a producer and both arms with their original outward labels.
A literal tag selects its arm. A sum reply held in a slot retains the case
and the two separately typed request paths. -/
theorem splice_schedule (exitL : At L i D) (exitR : At L j E)
    (producer : CallSchedule Γ p (Ty.coprod A B) fs)
    (left : CallSchedule (A :: Γ) l D ls) (right : CallSchedule (B :: Γ) r E rs) :
    ∃ s paths, Schedule Γ s L paths ∧ CasePaths fs ls rs i j paths ∧
      Eqv pe Γ (p.lsubst (fun _ => boundCase (l.renameLabels (fun _ => i)) (r.renameLabels (fun _ => j)))) s L :=
  splice_proof exitL exitR producer left right rfl

/-- Normalize the guarded finite-exit case and the case with its actual
reified arms to the same typed schedule at the original ordered exit list. -/
theorem operand_schedule {n : Nat} {β : BoundCtx (Ty α) n}
    (exitL : At L i D) (exitR : At L j E)
    (producer : Operand Φ β (Ty.coprod A B)) (left : Operand Φ (β.snoc A) D)
    (right : Operand Φ (β.snoc B) E)
    (hp : CallOperand (erase producer.1) true) (hl : CallOperand (erase left.1) true)
    (hr : CallOperand (erase right.1) true) :
    ∃ s paths, Schedule β.toList s L paths ∧
      CasePaths (operandCalls (erase producer.1) true) (operandCalls (erase left.1) true)
        (operandCalls (erase right.1) true) i j paths ∧
      Eqv pe β.toList
        (FiniteExit.case producer (.br exitL left) (.br exitR right)).toSSA.bindBranchArguments s L ∧
      Eqv pe β.toList
        (.case (erase producer.1) ((Code.ofLetCase left.2).guardedSSA i)
          ((Code.ofLetCase right.2).guardedSSA j)) s L :=
  operand_schedule_proof exitL exitR producer left right hp hl hr

end Schedule

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind
