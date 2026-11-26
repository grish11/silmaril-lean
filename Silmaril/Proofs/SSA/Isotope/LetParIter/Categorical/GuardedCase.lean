module

public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Environment
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Laws
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Purity
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Renaming

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Parallel (Derivation Pure)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj envSnocIso dropSlot case_postcomp)

universe v₁ v₂ u₁ u₂ u v w q

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

set_option backward.isDefEq.respectTransparency false in
private theorem weakened_branch {p : Tm ν Φ n} {D A : τ} (dp : Derivation Φ Γ β p D) :
    J.map (envSnocIso M Γ β A).hom ≫ denote J P M (Typing.lift dp) =
      J.map (fst (envObj M Γ β) (M.obj A)) ≫ denote J P M dp := by
  rw [Typing.lift, denote_rename_proof, envRenameMap_succ_proof, ← J.map_comp_assoc]
  simp only [dropSlot, Iso.hom_inv_id_assoc]

variable (L : Laws J P) {ε : Type q} [HasEff Φ ε] {pe : ε}
  (pureInstr : ∀ f : Φ, IsPure pe f →
    ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
  {e p : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D E : τ}

include L pureInstr

set_option backward.isDefEq.respectTransparency false in
theorem parCaseLeft_sound_proof (de : Derivation Φ Γ β e (coprod A B)) (he : Pure pe e)
    (dl : Derivation Φ Γ (.snoc β A) l D) (dr : Derivation Φ Γ (.snoc β B) r D)
    (dp : Derivation Φ Γ β p E) :
    denote J P M (.par (.case (h := hasCase) de dl dr) dp) =
      denote J P M
        (.case (h := hasCase) de (.par dl (Typing.lift dp)) (.par dr (Typing.lift dp))) := by
  obtain ⟨s, ds⟩ := denote_pure_proof J P M pureInstr de he
  simp only [denote, ds, ← J.map_comp]
  rw [L.case_left, case_postcomp]
  simp only [← Category.assoc (J.map (envSnocIso M Γ β _).hom), P.par_reindex,
    weakened_branch J P M dp]

set_option backward.isDefEq.respectTransparency false in
theorem parCaseRight_sound_proof (de : Derivation Φ Γ β e (coprod A B)) (he : Pure pe e)
    (dl : Derivation Φ Γ (.snoc β A) l D) (dr : Derivation Φ Γ (.snoc β B) r D)
    (dp : Derivation Φ Γ β p E) :
    denote J P M (.par dp (.case (h := hasCase) de dl dr)) =
      denote J P M
        (.case (h := hasCase) de (.par (Typing.lift dp) dl) (.par (Typing.lift dp) dr)) := by
  obtain ⟨s, ds⟩ := denote_pure_proof J P M pureInstr de he
  simp only [denote, ds, ← J.map_comp]
  rw [par_case_right_proof J P L, case_postcomp]
  simp only [← Category.assoc (J.map (envSnocIso M Γ β _).hom), P.par_reindex,
    weakened_branch J P M dp]

end Silmaril.Isotope.LetParIter.Categorical
