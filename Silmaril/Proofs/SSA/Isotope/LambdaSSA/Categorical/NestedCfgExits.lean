module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Square.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms

/-! # Exact graph comparison under an outward payload map -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgExits

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_postcomp)

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem routes {Γ : VCtx (Ty κ)} {L K : LCtx (Ty κ)} {Y : V}
    {left : labelObj M L ⟶ Y} {right : labelObj M K ⟶ Y} {r s : Region Φ}
    (pair : RegionConstructorRoutes M left right Γ r s) :
    RegionDenotes.Routes M left right J Γ r s := by
  intro _ _ f g d e
  induction pair with
  | br hl hr arg route =>
      cases d with
      | br da =>
          cases e with
          | br ea =>
              rename_i D _ _ hd E _ _ he
              have dType : D = _ := Option.some.inj (hd.symm.trans hl)
              have eType : E = _ := Option.some.inj (he.symm.trans hr)
              subst D E
              simp only [arg.denotes_eq J M da ea, Category.assoc, ← J.map_comp, route]
  | inl hl hr arg route =>
      cases d with
      | br da =>
          cases e with
          | br ea =>
              rename_i D _ _ hd E _ _ he
              have dType : D = _ := Option.some.inj (hd.symm.trans hl)
              have eType : E = _ := Option.some.inj (he.symm.trans hr)
              subst D E
              cases ea with
              | inl value =>
                  rw [arg.denotes_eq J M da value]
                  simp only [Category.assoc, ← J.map_comp, route]
  | inr hl hr arg route =>
      cases d with
      | br da =>
          cases e with
          | br ea =>
              rename_i D _ _ hd E _ _ he
              have dType : D = _ := Option.some.inj (hd.symm.trans hl)
              have eType : E = _ := Option.some.inj (he.symm.trans hr)
              subst D E
              cases ea with
              | inr value =>
                  rw [arg.denotes_eq J M da value]
                  simp only [Category.assoc, ← J.map_comp, route]
  | case uniq term _ _ ihl ihr =>
      cases d with
      | case da dl dr =>
          cases e with
          | case ea el er =>
              rename_i A₁ B₁ _ hd _ _ _ _ A₂ B₂ _ he _ _ _ _
              obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (uniq (.coprod A₁ B₁) hd)
              obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (uniq (.coprod A₂ B₂) he)
              rw [case_postcomp, case_postcomp, term.denotes_eq J M da ea, ihl dl el, ihr dr er]

set_option backward.isDefEq.respectTransparency false in
theorem dispatch {Γ : VCtx (Ty κ)} {L K : LCtx (Ty κ)} {n : Nat} (R : Fin (n + 1) → Ty κ)
    (out : labelObj M L ⟶ labelObj M K)
    {entry entry' : Region Φ} {blocks blocks' : Fin (n + 1) → Region Φ}
    (entryRoutes : RegionDenotes.Routes M
      (labelAppendSplit M (List.ofFn R) L ≫ coprod.map out (𝟙 _))
      (labelAppendSplit M (List.ofFn R) K) J Γ entry entry')
    (rowRoutes : ∀ i, RegionDenotes.Routes M
      (labelAppendSplit M (List.ofFn R) L ≫ coprod.map out (𝟙 _))
      (labelAppendSplit M (List.ofFn R) K) J (R i :: Γ) (blocks i) (blocks' i))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    {g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    (small : CfgDenotesAt J M R entry blocks f) (wide : CfgDenotesAt J M R entry' blocks' g) :
    g = f ≫ J.map out := by
  let cut := J.map (labelAppendSplit M (List.ofFn R) L)
  let cut' := J.map (labelAppendSplit M (List.ofFn R) K)
  let route := J.map (coprod.map out (𝟙 (labelObj M (List.ofFn R))))
  obtain ⟨_, _, e, _, all, se, sb, sc, rfl⟩ := small
  obtain ⟨_, _, e', _, all', we, wb, wc, rfl⟩ := wide
  have entry_eq : e ≫ cut ≫ route = e' ≫ cut' := by
    simpa only [J.map_comp] using entryRoutes se we
  have rows_eq : all ≫ cut ≫ route = all' ≫ cut' := by
    apply collective_ext J M n Γ R
    intro i
    rw [← Category.assoc _ all, sc.restrict i, ← Category.assoc _ all', wc.restrict i]
    simpa only [J.map_comp] using rowRoutes i (sb i) (wb i)
  have all_map : all' ≫ J.map (labelAppendSplit M (List.ofFn R) K) = all ≫ cut ≫ route := rows_eq.symm
  unfold cfgDispatchArrow
  rw [← entry_eq, all_map]
  simpa only [Category.assoc] using cfgDispatch_postmap J out (e ≫ cut)
    (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫ all ≫ cut)

theorem dispatch_exit_state_square {E A B D X : V} (out : B ⟶ D) (h : A ⟶ X)
    (entry : J.obj E ⟶ J.obj (B ⨿ A))
    (small : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A))
    (wide : J.obj (E ⊗ X) ⟶ J.obj (D ⨿ X))
    (comm : small ≫ J.map (coprod.map out h) = J.map (E ◁ h) ≫ wide) :
    caseWithContext J (entry ≫ J.map (coprod.map out h)) (J.map (snd E D)) (contextualLoop J wide) =
      caseWithContext J entry (J.map (snd E B)) (contextualLoop J small) ≫ J.map out := by
  have routing : J.map (coprod.map out (𝟙 A)) ≫ J.map (coprod.map (𝟙 D) h) =
      J.map (coprod.map out h) := by
    rw [← J.map_comp]
    congr 1
    apply coprod.hom_ext <;> simp only [coprod.inl_map, coprod.inr_map,
      coprod.inl_map_assoc, coprod.inr_map_assoc, Category.id_comp]
  have step : (small ≫ J.map (coprod.map out (𝟙 A))) ≫ J.map (coprod.map (𝟙 D) h) =
      J.map (E ◁ h) ≫ wide := by
    rw [Category.assoc, routing, comm]
  have replay := cfgDispatch_of_state_square J h (entry ≫ J.map (coprod.map out (𝟙 A))) _ wide step
  rw [Category.assoc, routing] at replay
  exact replay.symm.trans (cfgDispatch_postmap J out entry small)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgExits
