module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Denotation graph uniqueness under determined intermediate typing -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.Coherence

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_inl_context)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend duplicate)
open CartesianMonoidalCategory (snd)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)
  {κ : Type u} (M : TypeModel (Ty κ) V)
  {Φ : Type v} [HasTy Φ (Ty κ)]

section Term

variable [DistributiveFreydCategory J] [InstructionModel J M Φ]

theorem term_unique {Γ : VCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (rigid : DeterminedTerm Γ a A) {t : Tm.HasType Γ a A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M t f) (e : Denotes J M t g) : f = g := by
  induction rigid with
  | var h => cases d; cases e; rfl
  | unit => cases d; cases e; rfl
  | op _ ih => cases d; cases e; congr 1; exact ih ‹Denotes J M _ _› ‹Denotes J M _ _›
  | pair _ _ iha ihb =>
      cases d with
      | pair da db =>
          cases e with
          | pair ea eb => rw [iha da ea, ihb db eb]
  | inl _ ih =>
      cases d with
      | inl da => cases e with
        | inl ea => rw [ih da ea]
  | inr _ ih =>
      cases d with
      | inr db => cases e with
        | inr eb => rw [ih db eb]
  | abort _ ih =>
      cases d with
      | abort da => cases e with
        | abort ea => rw [ih da ea]
  | let₁ uniq _ _ iha ihb =>
      cases d with
      | let₁ da db =>
          cases e with
          | let₁ ea eb =>
              rename_i D _ hd _ _ E _ he _ _
              cases uniq D hd
              cases uniq E he
              rw [iha da ea, ihb db eb]
  | let₂ uniq _ _ iha ihb =>
      cases d with
      | let₂ da db =>
          cases e with
          | let₂ ea eb =>
              rename_i A₁ B₁ _ hd _ _ A₂ B₂ _ he _ _
              obtain ⟨rfl, rfl⟩ := Ty.product.inj (uniq (.product A₁ B₁) hd)
              obtain ⟨rfl, rfl⟩ := Ty.product.inj (uniq (.product A₂ B₂) he)
              rw [iha da ea, ihb db eb]
  | case uniq _ _ _ iha ihl ihr =>
      cases d with
      | case da dl dr =>
          cases e with
          | case ea el er =>
              rename_i A₁ B₁ _ hd _ _ _ _ A₂ B₂ _ he _ _ _ _
              obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (uniq (.coprod A₁ B₁) hd)
              obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (uniq (.coprod A₂ B₂) he)
              rw [iha da ea, ihl dl el, ihr dr er]

end Term

section Region

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [InstructionModel J M Φ]

theorem region_unique {Γ : VCtx (Ty κ)} {r : Region Φ} {L : LCtx (Ty κ)}
    (rigid : DeterminedRegion Γ r L) {t : Region.HasType Γ r L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) (e : RegionDenotes J M t g) : f = g := by
  induction rigid with
  | br h term =>
      cases d with
      | br da =>
          cases e with
          | br ea =>
              rename_i D _ _ hd E _ _ he
              have dType : D = _ := Option.some.inj (hd.symm.trans h)
              have eType : E = _ := Option.some.inj (he.symm.trans h)
              subst D E
              rw [term_unique J M term da ea]
  | let₁ uniq term _ ih =>
      cases d with
      | let₁ da db =>
          cases e with
          | let₁ ea eb =>
              rename_i D _ hd _ _ E _ he _ _
              cases uniq D hd
              cases uniq E he
              rw [term_unique J M term da ea, ih db eb]
  | let₂ uniq term _ ih =>
      cases d with
      | let₂ da db =>
          cases e with
          | let₂ ea eb =>
              rename_i A₁ B₁ _ hd _ _ A₂ B₂ _ he _ _
              obtain ⟨rfl, rfl⟩ := Ty.product.inj (uniq (.product A₁ B₁) hd)
              obtain ⟨rfl, rfl⟩ := Ty.product.inj (uniq (.product A₂ B₂) he)
              rw [term_unique J M term da ea, ih db eb]
  | case uniq term _ _ ihl ihr =>
      cases d with
      | case da dl dr =>
          cases e with
          | case ea el er =>
              rename_i A₁ B₁ _ hd _ _ _ _ A₂ B₂ _ he _ _ _ _
              obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (uniq (.coprod A₁ B₁) hd)
              obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (uniq (.coprod A₂ B₂) he)
              rw [term_unique J M term da ea, ihl dl el, ihr dr er]
  | @cfg Γ L n entry blocks R uniq _ _ ihe ihb =>
      cases n with
      | zero =>
          cases d with
          | cfgZero hd hb de =>
              cases e with
              | cfgZero he hb' ee =>
                  rename_i Rd Re
                  cases uniq Rd hd hb
                  cases uniq Re he hb'
                  exact ihe de ee
      | succ n =>
          cases d with
          | cfg hd hb de db dc =>
              cases e with
              | cfg he hc ee eb ec =>
                  rename_i Rd _ _ _ Re _ _ _
                  cases uniq Rd hd hb
                  cases uniq Re he hc
                  have entry_eq := ihe de ee
                  have collective_eq := collective_ext J M n Γ R fun i =>
                    (dc.restrict i).trans ((ihb i (db i) (eb i)).trans (ec.restrict i).symm)
                  rw [entry_eq, collective_eq]

set_option backward.isDefEq.respectTransparency false in
theorem cfg_exit {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {n i : Nat}
    {a : Tm Φ} {blocks : Fin (n + 1) → Region Φ} {A : Ty κ}
    (exit : At L i A) [FreydCategory.CentralUnit J]
    {t : Region.HasType Γ (.cfg (.br (n + 1 + i) a) (n + 1) blocks) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) :
    ∃ (ta : Tm.HasType Γ a A) (arg : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)),
      Denotes J M ta arg ∧ f = arg ≫ J.map (labelInject M i exit) := by
  cases d with
  | cfg he hb de db dc =>
      rename_i R _ _ _
      cases de with
      | br da =>
          rename_i D arg ha hi
          have typed : At (List.ofFn R ++ L) (n + 1 + i) A := by
            change (List.ofFn R ++ L)[n + 1 + i]? = some A
            have outside : (List.ofFn R).length ≤ n + 1 + i := by
              rw [List.length_ofFn]
              omega
            rw [List.getElem?_append_right outside, List.length_ofFn]
            simpa [At] using exit
          have eq : D = A := Option.some.inj (hi.symm.trans typed)
          subst D
          refine ⟨ha, arg, da, ?_⟩
          rw [Category.assoc, ← J.map_comp, labelAppendSplit_exit M R L exit hi, J.map_comp,
            ← Category.assoc arg, case_inl_context]
          unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
          simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
            Category.id_comp, Category.assoc]
          rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
          simp [duplicate]

end Region

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.Coherence
