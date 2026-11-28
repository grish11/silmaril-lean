module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind

/-! # Exact two-binder replay and scheduling -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind

open Region (HasType ValueBranches)
open Region.Paper.WithComputedCallReturns
open Morphism.CaseSSA (erase)
open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂

section Native

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε]
  {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {A B : τ}
  {r k k' : Region Φ} {a b : Tm Φ}

theorem ofPairs (h : OrderedPairs.Eqv pe Γ r k L) : Eqv pe Γ r k L :=
  ofPairs_proof h

/-- Reuse product binding in a contextual extension containing the native
binary-let binding step. -/
theorem bind_replay_with {seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (includeBind : ∀ {Δ K p q}, Region.BinaryLetBind.Step Δ p q K → seed Δ p q K)
    (ha : Tm.HasType Γ a (product A B)) (hr : ValueBranches Γ r [product A B])
    (producer : Region.Paper.Extension.Eqv seed Γ ((Region.br 0 a).bindBranchArguments) r [product A B])
    (body : Region.Paper.Extension.Eqv seed (B :: A :: Γ) k k' L) :
    Region.Paper.Extension.Eqv seed Γ (.let₂ a k) (r.lsubst (fun _ => unpack k')) L :=
  bind_replay_proof includeBind ha hr producer body

/-- Replay a computed product at the original ordered exits. The inserted
continuation names the product packet once and retains both field binders. -/
theorem bind_replay (ha : Tm.HasType Γ a (product A B)) (hr : ValueBranches Γ r [product A B])
    (producer : Eqv pe Γ ((Region.br 0 a).bindBranchArguments) r [product A B])
    (body : Eqv pe (B :: A :: Γ) k k' L) :
    Eqv pe Γ (.let₂ a k) (r.lsubst (fun _ => unpack k')) L :=
  bind_replay_with Or.inr ha hr producer body

/-- Contract a constructor pair at any typed continuation. Slot zero is
the right field, slot one is the left, and higher slots are the captures. -/
theorem constructor_beta (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B)
    (hk : HasType (B :: A :: Γ) k L) :
    Eqv pe Γ (.let₂ (.pair a b) k) (k.substVars (Tm.consSubst b (Tm.singleSubst a))) L :=
  .paper (.productBeta (.let₂Beta ha hb hk))

theorem Schedule.valueBranches {fs : List Φ} (h : Schedule Γ r L fs) : ValueBranches Γ r L :=
  h.valueBranches_proof

/-- The enlarged closure is sound for the same shared-tensor,
central-unit strong Elgot Freyd interpretations as the outward relation. -/
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
    (h : Eqv pe Γ r k L) (hr : HasType Γ r L) (hk : HasType Γ k L) :
    denoteRegion J M hr = denoteRegion J M hk :=
  sound_proof J M shared h hr hk

end Native

section Schedule

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {A B D : Ty α} {i : Nat}
  {r k : Region Φ} {fs gs : List Φ}

/-- Append a scheduled two-binder body at the selected original exit.
A constructor pair is substituted, and a product slot is unpacked once. -/
theorem splice_schedule (exit : At L i D) (p : CallSchedule Γ r (Ty.product A B) fs)
    (q : CallSchedule (B :: A :: Γ) k D gs) :
    ∃ s, Schedule Γ s L (fs ++ gs) ∧
      Eqv pe Γ (r.lsubst (fun _ => unpack (k.renameLabels (fun _ => i)))) s L :=
  splice_proof exit p q rfl

/-- The written guarded elimination and its actual LetCase reification
replay to the same schedule, with producer requests before body requests. -/
theorem operand_schedule {n : Nat} {β : BoundCtx (Ty α) n}
    (exit : At L i D) (producer : Operand Φ β (Ty.product A B))
    (body : Operand Φ ((β.snoc A).snoc B) D)
    (hp : CallOperand (erase producer.1) true) (hk : CallOperand (erase body.1) true) :
    ∃ s, Schedule β.toList s L
        (operandCalls (erase producer.1) true ++ operandCalls (erase body.1) true) ∧
      Eqv pe β.toList ((Code.let₂ producer (.br body)).guardedSSA i) s L ∧
      Eqv pe β.toList ((Code.ofLetCase (.let₂ producer.2 body.2)).guardedSSA i) s L :=
  operand_schedule_proof exit producer body hp hk

end Schedule

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind
