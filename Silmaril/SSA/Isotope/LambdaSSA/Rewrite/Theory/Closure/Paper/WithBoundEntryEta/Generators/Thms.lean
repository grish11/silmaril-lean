module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators

/-! # Exact generator characterization of once-bound CFG η -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The five structural moves generate exactly the contextual once-bound
CFG η relation at every exact region interface. -/
theorem iff_bound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} :
    Eqv Γ r s L ↔ WithBoundEntryEta.Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators.iff_bound

/-- The structural moves prove once-bound re-entry for arbitrary exactly
typed entries and local rows. -/
theorem reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {bs : Fin n → Region Φ} (R : Fin n → τ)
    (hr : HasType Γ r (List.ofFn R ++ L))
    (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg r n bs) (r.bindBranchArguments.lsubst (cfgEntryContinuations bs)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators.reentry R hr hb

/-- Once-bound η moves a table under a case while retaining its exact
discriminator, including effects. -/
theorem caseEntry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    {bs : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.coprod A B))
    (hl : HasType (A :: Γ) l (List.ofFn R ++ L))
    (hr : HasType (B :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
    WithBoundEntryEta.Eqv Γ (.cfg (.case a l r) n bs)
      (.case a (.cfg l n (weakenRows bs)) (.cfg r n (weakenRows bs))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators.caseEntry R ha hl hr hb

/-- A nested entry can keep its own local labels and apply the outer table
on its outward edges by lifted continuation substitution. -/
theorem nested {m n : Nat} {Γ : VCtx τ} {L : LCtx τ} {e : Region Φ}
    {inner : Fin m → Region Φ} {outer : Fin n → Region Φ} (S : Fin m → τ) (R : Fin n → τ)
    (he : HasType Γ e (List.ofFn S ++ (List.ofFn R ++ L)))
    (hi : ∀ j, HasType (S j :: Γ) (inner j) (List.ofFn S ++ (List.ofFn R ++ L)))
    (ho : ∀ j, HasType (R j :: Γ) (outer j) (List.ofFn R ++ L)) :
    WithBoundEntryEta.Eqv Γ (.cfg (.cfg e m inner) n outer)
      (.cfg (e.lsubst (liftLSubstN m (cfgEntryContinuations outer))) m
        (fun j => (inner j).lsubst (liftLSubstVars (liftLSubstN m (cfgEntryContinuations outer))))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators.nested S R he hi ho

/-- #4152 and unary entry sequencing derive the case-entry equation when
the arms and rows are guarded. The discriminator itself may be effectful. -/
theorem candidate_caseEntry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    {bs : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.coprod A B))
    (hl : ValueBranches (A :: Γ) l (List.ofFn R ++ L))
    (hr : ValueBranches (B :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
    Extension.Eqv Candidate Γ (.cfg (.case a l r) n bs)
      (.case a (.cfg l n (weakenRows bs)) (.cfg r n (weakenRows bs))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators.candidate_caseEntry R ha hl hr hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators
