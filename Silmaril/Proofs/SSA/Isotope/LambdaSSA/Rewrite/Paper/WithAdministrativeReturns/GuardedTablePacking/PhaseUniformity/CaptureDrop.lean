module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.FlatSource
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Projection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Bekic.Thms

/-! # Dropping a captured input that the rows of a dispatcher do not use -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.TypeCategory (iterate_roll)
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open CfgEta.TypeCategory (productSndBranches whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.TypeCategory (whiskerLeft whiskerLeft_comp whiskerLeft_id whiskerLeft_ofRegion whiskerLeftFunctor
  tensorObj leftCoproductComparisonIso leftCoproductComparisonIso_hom leftCoproductComparisonIso_inv
  leftCoproductDistributor)
open Paper.TypeCategory.Projection (productSnd iterate_projected_whiskerLeft)

section Drop

variable {X B A : Ty Empty}

local notation "Z" => ofType (Φ := signature.Instr) X

/-! ## The tail of a lifted step -/

theorem sndInl_typed :
    ValueBranches [Silmaril.product X B] (.let₂ (.var 0) (.br 0 (.inl (.var 0))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
  .let₂ (A := X) (B := B) (.var rfl) (.br rfl (.inl (.var rfl)))

theorem inrKeep_typed :
    ValueBranches [Silmaril.product X A] (.br 0 (.inr (.var 0)) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
  .br rfl (.inr (.var rfl))

/-- `dropCase` is the distributor followed by the projection on the
return side. Product β and the native case on a constructor. -/
theorem dropCase_eqv :
    Paper.Eqv [Silmaril.product X (Silmaril.coprod B A)] dropCase
      (seqRegion distributorRegion (.case (.var 0) (.let₂ (.var 0) (.br 0 (.inl (.var 0))))
        (.br 0 (.inr (.var 0)))))
      [Silmaril.coprod B (Silmaril.product X A)] := by
  have hsnd : Region.HasType [Silmaril.product X B, B, Silmaril.coprod B A, X,
      Silmaril.product X (Silmaril.coprod B A)]
      (.let₂ (.var 0) (.br 0 (.inl (.var 0))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.let₂ (A := X) (B := B) (.var rfl) (.br rfl (.inl (.var rfl)))).hasType
  have hkeepL : Region.HasType [Silmaril.product X A, B, Silmaril.coprod B A, X,
      Silmaril.product X (Silmaril.coprod B A)]
      (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.var rfl))).hasType
  have hsndR : Region.HasType [Silmaril.product X B, A, Silmaril.coprod B A, X,
      Silmaril.product X (Silmaril.coprod B A)]
      (.let₂ (.var 0) (.br 0 (.inl (.var 0))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.let₂ (A := X) (B := B) (.var rfl) (.br rfl (.inl (.var rfl)))).hasType
  have hkeepR : Region.HasType [Silmaril.product X A, A, Silmaril.coprod B A, X,
      Silmaril.product X (Silmaril.coprod B A)]
      (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.var rfl))).hasType
  have hbody : Region.HasType [B, X, B, Silmaril.coprod B A, X, Silmaril.product X (Silmaril.coprod B A)]
      (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inl (.var rfl))).hasType
  have left : Paper.Eqv [B, Silmaril.coprod B A, X, Silmaril.product X (Silmaril.coprod B A)]
      (.case (.inl (.pair (.var 2) (.var 0))) (.let₂ (.var 0) (.br 0 (.inl (.var 0))))
        (.br 0 (.inr (.var 0))))
      (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod B (Silmaril.product X A)] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInl (A := Silmaril.product X B) (B := Silmaril.product X A)
      (.pair (.var rfl) (.var rfl)) hsnd hkeepL)))).trans
      ((Paper.Eqv.cfgEta (.native (.letValue (.pair (.var rfl) (.var rfl)) hsnd))).trans
        (.productBeta (.let₂Beta (A := X) (B := B) (.var rfl) (.var rfl) hbody)))
  have right : Paper.Eqv [A, Silmaril.coprod B A, X, Silmaril.product X (Silmaril.coprod B A)]
      (.case (.inr (.pair (.var 2) (.var 0))) (.let₂ (.var 0) (.br 0 (.inl (.var 0))))
        (.br 0 (.inr (.var 0))))
      (.br 0 (.inr (.pair (.var 2) (.var 0))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInr (A := Silmaril.product X B) (B := Silmaril.product X A)
      (.pair (.var rfl) (.var rfl)) hsndR hkeepR)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) (.pair (.var rfl) (.var rfl)) (.inr (.var rfl)) rfl))))
  exact .symm (.let₂ (A := X) (B := Silmaril.coprod B A) (.var rfl)
    (.case (A := B) (B := A) (.var rfl) left right))

/-- The arrow of `dropCase`: the inverse comparison of the fixed left
factor followed by the projection on the return side. -/
theorem dropCase_arrow :
    ofRegion (dropCase_typed (X := X) (B := B) (A := A)) ≫
        (sumIso (Φ := signature.Instr) B (Silmaril.product X A)).hom =
      whiskerLeft Z (sumIso (Φ := signature.Instr) B A).hom ≫
        ((leftCoproductComparisonIso Z (ofType B) (ofType A)).inv ≫
          coprod.map (productSnd Z (ofType B)) (𝟙 (tensorObj Z (ofType A)))) := by
  have hl := sndInl_typed (X := X) (B := B) (A := A)
  have hr := inrKeep_typed (X := X) (B := B) (A := A)
  have inlB : ValueBranches [B] (.br 0 (.inl (.var 0)) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] := .br rfl (.inl (.var rfl))
  have e : ofRegion (dropCase_typed (X := X) (B := B) (A := A)) =
      ofRegion (seqValueBranches (distributorRegion_typed X B A) (caseValueBranches hl hr)) :=
    (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr dropCase_eqv
  have c := ofRegion_comp (distributorRegion_typed X B A) (caseValueBranches hl hr)
    (seqValueBranches (distributorRegion_typed X B A) (caseValueBranches hl hr))
  have d := coprod_desc_ofRegion hl hr
  have l₀ : ofRegion inlB = coprod.inl ≫ (sumIso (Φ := signature.Instr) B (Silmaril.product X A)).inv :=
    (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id B)).trans (Category.id_comp _))
  have l : ofRegion hl = productSnd Z (ofType B) ≫ coprod.inl ≫
      (sumIso (Φ := signature.Instr) B (Silmaril.product X A)).inv :=
    (ofRegion_comp (productSndBranches X B) inlB hl).symm.trans (congrArg (productSnd Z (ofType B) ≫ ·) l₀)
  have r : ofRegion hr = coprod.inr ≫ (sumIso (Φ := signature.Instr) B (Silmaril.product X A)).inv :=
    (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id (Silmaril.product X A))).trans (Category.id_comp _))
  have w : whiskerLeft Z (sumIso (Φ := signature.Instr) B A).hom ≫
      whiskerLeft Z (sumIso (Φ := signature.Instr) B A).inv = 𝟙 _ := by
    rw [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id]
  have rhs : whiskerLeft Z (sumIso (Φ := signature.Instr) B A).hom ≫
      ((leftCoproductComparisonIso Z (ofType B) (ofType A)).inv ≫
        coprod.map (productSnd Z (ofType B)) (𝟙 (tensorObj Z (ofType A)))) =
      ofRegion (distributorRegion_typed X B A) ≫
        (sumIso (Φ := signature.Instr) (Silmaril.product X B) (Silmaril.product X A)).hom ≫
          coprod.map (productSnd Z (ofType B)) (𝟙 (tensorObj Z (ofType A))) := by
    rw [leftCoproductComparisonIso_inv]
    change whiskerLeft Z (sumIso (Φ := signature.Instr) B A).hom ≫
      ((whiskerLeft Z (sumIso (Φ := signature.Instr) B A).inv ≫
        ofRegion (τ := Ty Empty) (distributorRegion_typed X B A) ≫
        (sumIso (Φ := signature.Instr) (Silmaril.product X B) (Silmaril.product X A)).hom) ≫ _) = _
    rw [Category.assoc, ← Category.assoc (whiskerLeft Z (sumIso (Φ := signature.Instr) B A).hom), w,
      Category.id_comp, Category.assoc]
  rw [rhs, e, ← c, ← d, l, r]
  simp only [Category.assoc]
  congr 2
  apply coprod.hom_ext <;> simp <;> first | rfl | exact (Category.id_comp _).symm

/-- Left whiskering of a copair at an exact sum: distribute, then whisker
each side. -/
theorem whisker_sum {A₀ A₁ : Ty Empty} {W : Paper.TypeCategory (τ := Ty Empty) signature.Instr}
    (u : ofType (Φ := signature.Instr) A₀ ⟶ W) (v : ofType (Φ := signature.Instr) A₁ ⟶ W) :
    whiskerLeft Z ((sumIso (Φ := signature.Instr) A₀ A₁).hom ≫ coprod.desc u v) =
      (ofRegion (distributorRegion_typed X A₀ A₁) ≫
        (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₀) (Silmaril.product X A₁)).hom) ≫
        coprod.desc (whiskerLeft Z u) (whiskerLeft Z v) := by
  have w : whiskerLeft Z (sumIso (Φ := signature.Instr) A₀ A₁).hom ≫
      whiskerLeft Z (sumIso (Φ := signature.Instr) A₀ A₁).inv = 𝟙 _ := by
    rw [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id]
  have d : ofRegion (distributorRegion_typed X A₀ A₁) ≫
      (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₀) (Silmaril.product X A₁)).hom =
      whiskerLeft Z (sumIso (Φ := signature.Instr) A₀ A₁).hom ≫
        (leftCoproductComparisonIso Z (ofType A₀) (ofType A₁)).inv := by
    rw [leftCoproductComparisonIso_inv]
    change _ = whiskerLeft Z (sumIso (Φ := signature.Instr) A₀ A₁).hom ≫
      (whiskerLeft Z (sumIso (Φ := signature.Instr) A₀ A₁).inv ≫
        ofRegion (τ := Ty Empty) (distributorRegion_typed X A₀ A₁) ≫
        (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₀) (Silmaril.product X A₁)).hom)
    rw [← Category.assoc, w, Category.id_comp]
  have k : whiskerLeft Z (coprod.desc u v) =
      (leftCoproductComparisonIso Z (ofType A₀) (ofType A₁)).inv ≫
        coprod.desc (whiskerLeft Z u) (whiskerLeft Z v) := by
    rw [Iso.eq_inv_comp, leftCoproductComparisonIso_hom]
    apply coprod.hom_ext
    · exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ whiskerLeft Z (coprod.desc u v))
          (inl_coprodComparison (whiskerLeftFunctor Z) (ofType A₀) (ofType A₁))).trans
          ((whiskerLeft_comp Z _ _).symm.trans (congrArg (whiskerLeft Z) (coprod.inl_desc u v))))).trans
        (coprod.inl_desc _ _).symm
    · exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ whiskerLeft Z (coprod.desc u v))
          (inr_coprodComparison (whiskerLeftFunctor Z) (ofType A₀) (ofType A₁))).trans
          ((whiskerLeft_comp Z _ _).symm.trans (congrArg (whiskerLeft Z) (coprod.inr_desc u v))))).trans
        (coprod.inr_desc _ _).symm
  rw [whiskerLeft_comp, k, d, Category.assoc]
  rfl

/-- Two regions on a captured input paired with the empty type are equal. -/
theorem tensor_empty_ext {D : Ty Empty} {r s : Region signature.Instr}
    (hr : ValueBranches [Silmaril.product X Silmaril.empty] (.let₂ (.var 0) r) [D])
    (hs : ValueBranches [Silmaril.product X Silmaril.empty] (.let₂ (.var 0) s) [D]) :
    ofRegion hr = ofRegion hs := by
  apply (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
  cases hr with
  | let₂ ha hr' =>
    cases hs with
    | let₂ hb hs' =>
      cases ha with
      | var hi =>
        cases hi
        cases hb with
        | var hj =>
          cases hj
          exact .let₂ (.var rfl)
            (.cfgEta (.native (.initial (a := .var 0) (.var rfl) hr'.hasType hs'.hasType)))

/-! ## The tail at a constructor exit -/

variable {Γ : VCtx (Ty Empty)} {i : Nat} {d t : Tm signature.Instr}

/-- On a returned value the tail drops the captured input. -/
theorem drop_inl (hi : At Γ i X) (hd : Tm.BranchValue Γ d B) :
    Paper.Eqv Γ
      (.let₂ (.pair (.var i) (.inl d))
        (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.pair (.var 2) (.var 0))))))
      (.br 0 (.inl d) : Region signature.Instr) [Silmaril.coprod B (Silmaril.product X A)] := by
  have hl : Region.HasType (B :: Γ) (.br 0 (.inl (.var 0)) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inl (.var rfl))).hasType
  have hr : Region.HasType (A :: Γ) (.br 0 (.inr (.pair (.var (i + 1)) (.var 0))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.br (Γ := A :: Γ) (ℓ := 0) rfl
      (.inr (.pair (.var (i := i + 1) (show At (A :: Γ) (i + 1) X from hi)) (.var (i := 0) rfl)))).hasType
  have hbody : Region.HasType (Silmaril.coprod B A :: X :: Γ)
      (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.pair (.var 2) (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.case (A := B) (B := A) (.var rfl) (.br rfl (.inl (.var rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.var rfl))))).hasType
  exact (Paper.Eqv.productBeta (.let₂Beta (A := X) (B := Silmaril.coprod B A) (.var hi) (.inl hd) hbody)).trans
    ((Paper.Eqv.cfgEta (.native (.base (.caseInl (A := B) (B := A) hd.hasType hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) hd (.inl (.var rfl)) rfl)))))

/-- On a repeated state the tail keeps the captured input. -/
theorem drop_inr (hi : At Γ i X) (ht : Tm.BranchValue Γ t A) :
    Paper.Eqv Γ
      (.let₂ (.pair (.var i) (.inr t))
        (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.pair (.var 2) (.var 0))))))
      (.br 0 (.inr (.pair (.var i) t)) : Region signature.Instr) [Silmaril.coprod B (Silmaril.product X A)] := by
  have hl : Region.HasType (B :: Γ) (.br 0 (.inl (.var 0)) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inl (.var rfl))).hasType
  have hr : Region.HasType (A :: Γ) (.br 0 (.inr (.pair (.var (i + 1)) (.var 0))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.br (Γ := A :: Γ) (ℓ := 0) rfl
      (.inr (.pair (.var (i := i + 1) (show At (A :: Γ) (i + 1) X from hi)) (.var (i := 0) rfl)))).hasType
  have hbody : Region.HasType (Silmaril.coprod B A :: X :: Γ)
      (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.pair (.var 2) (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod B (Silmaril.product X A)] :=
    (ValueBranches.case (A := B) (B := A) (.var rfl) (.br rfl (.inl (.var rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.var rfl))))).hasType
  exact (Paper.Eqv.productBeta (.let₂Beta (A := X) (B := Silmaril.coprod B A) (.var hi) (.inr ht) hbody)).trans
    ((Paper.Eqv.cfgEta (.native (.base (.caseInr (A := B) (B := A) ht.hasType hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) ht (.inr (.pair (.var hi) (.var rfl))) rfl)))))

end Drop

section TwoRows

variable {X A₀ A₁ D : Ty Empty} {ρ₀ ρ₁ dR β₀ β₁ : Region signature.Instr}

local notation "Z" => ofType (Φ := signature.Instr) X
local notation "P" => Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)
local notation "S" => Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))
set_option quotPrecheck false in
local notation "T" => (leftCoproductComparisonIso Z (ofType D) (ofType P)).inv ≫
  coprod.map (productSnd Z (ofType D)) (𝟙 (tensorObj Z (ofType P)))

/-- A lifted row: the capture-free row whiskered by the input, then the tail. -/
theorem lifted_row {A : Ty Empty} {β : Region signature.Instr} (hβ : ValueBranches [A] β [Silmaril.coprod D P]) :
    whiskerLeft Z (ofRegion hβ ≫ (sumIso (Φ := signature.Instr) D P).hom) ≫ T =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ) (dropCase_typed (X := X) (B := D) (A := P))) ≫
        (sumIso (Φ := signature.Instr) D S).hom := by
  rw [whiskerLeft_comp, whiskerLeft_ofRegion, Category.assoc, ← dropCase_arrow, ← Category.assoc,
    ofRegion_comp (whiskerLeftRegion_typed X hβ) (dropCase_typed (X := X) (B := D) (A := P))
      (seqValueBranches (whiskerLeftRegion_typed X hβ) (dropCase_typed (X := X) (B := D) (A := P)))]

/-- The dead row of the empty tail. -/
theorem lifted_dead (hd : ValueBranches [Silmaril.empty] dR [Silmaril.coprod D S]) :
    whiskerLeft Z ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType D ⨿ ofType P)) ≫ T =
      ofRegion (seqValueBranches (productSndBranches X Silmaril.empty) hd) ≫
        (sumIso (Φ := signature.Instr) D S).hom := by
  obtain ⟨k, hk, ek⟩ := Paper.TypeCategory.exists_ofRegion
    ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType D ⨿ ofType P) ≫
      (sumIso (Φ := signature.Instr) D P).inv)
  have e : (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType D ⨿ ofType P) =
      ofRegion hk ≫ (sumIso (Φ := signature.Instr) D P).hom := by
    rw [← ek, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [e, lifted_row hk]
  exact congrArg (· ≫ (sumIso (Φ := signature.Instr) D S).hom)
    (tensor_empty_ext (seqValueBranches (whiskerLeftRegion_typed X hk) (dropCase_typed (X := X) (B := D) (A := P)))
      (seqValueBranches (productSndBranches X Silmaril.empty) hd))

/-- A dispatcher of two rows that thread a captured input without using
it iterates as the capture-free step after the input is dropped. Default
Paper: distribution over the tags, the projection law of iteration, and
initiality of the empty tail. -/
theorem two_row_drop (hρ₀ : ValueBranches [Silmaril.product X A₀] ρ₀ [Silmaril.coprod D S])
    (hρ₁ : ValueBranches [Silmaril.product X A₁] ρ₁ [Silmaril.coprod D S])
    (hd : ValueBranches [Silmaril.empty] dR [Silmaril.coprod D S])
    (hβ₀ : ValueBranches [A₀] β₀ [Silmaril.coprod D P])
    (hβ₁ : ValueBranches [A₁] β₁ [Silmaril.coprod D P])
    (e₀ : ofRegion hρ₀ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₀)
      (dropCase_typed (X := X) (B := D) (A := P))))
    (e₁ : ofRegion hρ₁ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₁)
      (dropCase_typed (X := X) (B := D) (A := P))))
    (hdisp : ValueBranches [S] (twoRows ρ₀ ρ₁ dR) [Silmaril.coprod D S]) :
    iterate (ofRegion hdisp ≫ (sumIso (Φ := signature.Instr) D S).hom) =
      productSnd Z (ofType P) ≫ iterate (freeStep hβ₀ hβ₁) := by
  have hdead := seqValueBranches (productSndBranches X Silmaril.empty) hd
  have hin := caseValueBranches hρ₁ hdead
  have hmid := seqValueBranches (distributorRegion_typed X A₁ Silmaril.empty) hin
  have hout := caseValueBranches hρ₀ hmid
  have left : ofRegion hdisp ≫ (sumIso (Φ := signature.Instr) D S).hom =
      (ofRegion (τ := Ty Empty) (distributorRegion_typed X A₀ (Silmaril.coprod A₁ Silmaril.empty)) ≫
        (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₀)
          (Silmaril.product X (Silmaril.coprod A₁ Silmaril.empty))).hom) ≫
        coprod.desc (ofRegion hρ₀ ≫ (sumIso (Φ := signature.Instr) D S).hom)
          ((ofRegion (τ := Ty Empty) (distributorRegion_typed X A₁ Silmaril.empty) ≫
            (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₁)
              (Silmaril.product X Silmaril.empty)).hom) ≫
            coprod.desc (ofRegion hρ₁ ≫ (sumIso (Φ := signature.Instr) D S).hom)
              (ofRegion hdead ≫ (sumIso (Φ := signature.Instr) D S).hom)) := by
    rw [← ofRegion_comp (distributorRegion_typed X A₀ (Silmaril.coprod A₁ Silmaril.empty)) hout hdisp,
      ← coprod_desc_ofRegion hρ₀ hmid, ← ofRegion_comp (distributorRegion_typed X A₁ Silmaril.empty) hin hmid,
      ← coprod_desc_ofRegion hρ₁ hdead]
    simp only [Category.assoc, coprod.desc_comp]
  have right : (whiskerLeft Z (freeStep hβ₀ hβ₁) ≫ (leftCoproductComparisonIso Z (ofType D) (ofType P)).inv) ≫
      coprod.map (productSnd Z (ofType D)) (𝟙 (tensorObj Z (ofType P))) =
      (ofRegion (τ := Ty Empty) (distributorRegion_typed X A₀ (Silmaril.coprod A₁ Silmaril.empty)) ≫
        (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₀)
          (Silmaril.product X (Silmaril.coprod A₁ Silmaril.empty))).hom) ≫
        coprod.desc (ofRegion hρ₀ ≫ (sumIso (Φ := signature.Instr) D S).hom)
          ((ofRegion (τ := Ty Empty) (distributorRegion_typed X A₁ Silmaril.empty) ≫
            (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₁)
              (Silmaril.product X Silmaril.empty)).hom) ≫
            coprod.desc (ofRegion hρ₁ ≫ (sumIso (Φ := signature.Instr) D S).hom)
              (ofRegion hdead ≫ (sumIso (Φ := signature.Instr) D S).hom)) := by
    rw [e₀, e₁, ← lifted_row hβ₀, ← lifted_row hβ₁, ← lifted_dead hd]
    unfold freeStep
    rw [whisker_sum, whisker_sum]
    simp only [Category.assoc, coprod.desc_comp]
  rw [left, ← right]
  exact iterate_projected_whiskerLeft Z (freeStep hβ₀ hβ₁)

end TwoRows

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
