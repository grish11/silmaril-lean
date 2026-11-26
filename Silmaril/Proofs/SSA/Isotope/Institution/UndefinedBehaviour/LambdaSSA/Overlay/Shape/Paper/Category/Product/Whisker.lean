module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Representatives
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Product
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Literal

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product

open Silmaril Isotope LambdaSSA
open Silmaril.DeBruijn (lift)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.UB.Overlay (Outcome Behaviour nativeOutcomes extendModel)
open LambdaSSA.UB.Overlay.Shape.Category (repackage)
open LambdaSSA.Region (ValueBranches)
open LambdaSSA.Region.CfgEta.TypeCategory
  (whiskerLeftRegion whiskerRightRegion whiskerLeftRegion_typed whiskerRightRegion_typed)
open Silmaril.Isotope.Institution.Observational (Model)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category
  (ops outcomes_of_regionAt branch_outcomes literal_outcomes)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (PureValue)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent (vars let₂_pure)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {A B C X Y : Ty κ} {r : Region Φ}

private theorem at_singleton {i : Nat} {T : Ty κ} (h : At [A] i T) : i = 0 ∧ T = A :=
  ⟨by have := (List.getElem?_eq_some_iff.mp h).choose; simpa using this,
    List.mem_singleton.mp (List.mem_of_getElem? h)⟩

private theorem one_ren {Γ : List (Ty κ)} {ρ : Nat → Nat} (h : At Γ (ρ 0) A) : Ren [A] Γ ρ := by
  intro i T hi
  obtain ⟨rfl, rfl⟩ := at_singleton hi
  exact h

private theorem branch_family {Γ : List (Ty κ)} {q : Tm Φ} (ht : q.HasType (B :: Γ) C) :
    LambdaSSA.Region.LSubst.HasType Γ [B] [C] (fun _ => .br 0 q) :=
  fun _ _ hi => (at_singleton hi).2.symm ▸ .br (ℓ := 0) rfl ht

private theorem repack_outcomes {Γ : List (Ty κ)} {p : Region Φ} {q : Tm Φ}
    (M : Model.{u,w,x} Φ Γ.length) {env : Env M.α}
    (agree : Morphism.CaseSSA.EnvAgrees env M.bound) (hp : ValueBranches Γ p [B])
    (ht : q.HasType (B :: Γ) C) (pack : Value M.α → Value M.α)
    (pure : ∀ b, PureValue (ops M) (extend env b) q (pack b)) (s : M.σ) :
    (↑(nativeOutcomes ⟨p.lsubst (fun _ => .br 0 q), hp.hasType.lsubst (branch_family ht)⟩ M s) :
      Behaviour 1 M.α M.σ) =
      repackage (↑(nativeOutcomes ⟨p, hp.hasType⟩ M s)) pack := by
  rw [literal_outcomes hp (branch_family ht) M s, repackage, Behaviour.coe_bind]
  apply WithTop.coe_inj.mpr
  congr 1
  funext j b t
  have hj := Fin.eq_zero j
  subst j
  exact branch_outcomes (extendModel M b) (agree.extend b) ht (pure b) t

private abbrev unpackEnv (M : Model.{u,w,x} Φ 0) (l r : Value M.α) : Env M.α :=
  extend (extend (extend (envOfBound M.bound) (.pair l r)) l) r

private theorem whisker_outcomes (M : Model.{u,w,x} Φ 0) (l rv active : Value M.α)
    (hr : ValueBranches [A] r [B]) (ρ : Nat → Nat)
    (ren : Ren [A] [Y, X, .product X Y] ρ) (which : unpackEnv M l rv (ρ 0) = active)
    {q : Tm Φ} (ht : q.HasType [B, Y, X, .product X Y] C) (pack : Value M.α → Value M.α)
    (pure : ∀ b, PureValue (ops M) (extend (unpackEnv M l rv) b) q (pack b))
    (hh : (.let₂ (.var 0) ((r.renameVars ρ).lsubst (fun _ => .br 0 q)) : Region Φ).HasType
      [.product X Y] [C]) (s : M.σ) :
    (↑(nativeOutcomes ⟨_, hh⟩ (extendModel M (.pair l rv)) s) : Behaviour 1 M.α M.σ) =
      repackage (↑(nativeOutcomes ⟨r, hr.hasType⟩ (extendModel M active) s)) pack := by
  let M' := extendModel (extendModel (extendModel M (.pair l rv)) l) rv
  have agree := envOfBound_agrees M.bound
  have pairAgree := agree.extend (.pair l rv)
  have unpackAgree := (pairAgree.extend l).extend rv
  have hr' := hr.renameVars ren
  let body : UB.Typed (Φ := Φ) [Y, X, .product X Y] [C] :=
    ⟨(r.renameVars ρ).lsubst (fun _ => .br 0 q), hr'.hasType.lsubst (branch_family ht)⟩
  have unpacked : nativeOutcomes ⟨_, hh⟩ (extendModel M (.pair l rv)) s = nativeOutcomes body M' s :=
    outcomes_of_regionAt M ⟨_, hh⟩ body pairAgree unpackAgree
      (let₂_pure (PureValue.var 0) body.val) s
  rw [unpacked, repack_outcomes M' unpackAgree hr' ht pack pure]
  have actual : Morphism.CaseSSA.EnvAgrees (fun i => unpackEnv M l rv (ρ i)) (extendModel M active).bound := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    exact which
  have renamed : nativeOutcomes ⟨r.renameVars ρ, hr'.hasType⟩ M' s =
      nativeOutcomes ⟨r, hr.hasType⟩ (extendModel M active) s :=
    outcomes_of_regionAt M ⟨_, hr'.hasType⟩ ⟨_, hr.hasType⟩ unpackAgree actual
      (vars r (ρ := ρ) (fun _ => rfl)) s
  rw [renamed]

theorem left_outcomes (M : Model.{u,w,x} Φ 0) (l a : Value M.α)
    (hr : ValueBranches [A] r [B]) (s : M.σ) :
    (↑(nativeOutcomes ⟨whiskerLeftRegion r, (whiskerLeftRegion_typed X hr).hasType⟩
      (extendModel M (.pair l a)) s) : Behaviour 1 M.α M.σ) =
      repackage (↑(nativeOutcomes ⟨r, hr.hasType⟩ (extendModel M a) s)) (.pair l) :=
  whisker_outcomes M l a a hr (lift (Nat.succ ∘ Nat.succ)) (one_ren rfl) rfl
    (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)) (.pair l)
    (fun _ => (PureValue.var 2).pair (PureValue.var 0)) (whiskerLeftRegion_typed X hr).hasType s

theorem right_outcomes (M : Model.{u,w,x} Φ 0) (a rv : Value M.α)
    (hr : ValueBranches [A] r [B]) (s : M.σ) :
    (↑(nativeOutcomes ⟨whiskerRightRegion r, (whiskerRightRegion_typed X hr).hasType⟩
      (extendModel M (.pair a rv)) s) : Behaviour 1 M.α M.σ) =
      repackage (↑(nativeOutcomes ⟨r, hr.hasType⟩ (extendModel M a) s)) (fun b => .pair b rv) :=
  whisker_outcomes M a rv a hr (Nat.succ ∘ lift Nat.succ) (one_ren rfl) rfl
    (.pair (.var (i := 0) rfl) (.var (i := 1) rfl)) (fun b => .pair b rv)
    (fun _ => (PureValue.var 0).pair (PureValue.var 1)) (whiskerRightRegion_typed X hr).hasType s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product
