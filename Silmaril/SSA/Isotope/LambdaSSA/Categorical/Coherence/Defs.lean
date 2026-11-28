module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Exact syntax with determined intermediate typing -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

universe u v

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

/-- The exact type of this term is forced by its syntax and input context. -/
@[expose] def TypeDetermined (Γ : VCtx (Ty κ)) (a : Tm Φ) (A : Ty κ) : Prop :=
  ∀ D, a.HasType Γ D → D = A

/-- At a fixed result type, every local type choice made by the term is forced.
An injection can use the expected sum type even when it has no unique type
in isolation. -/
inductive DeterminedTerm : VCtx (Ty κ) → Tm Φ → Ty κ → Prop where
  | var {Γ i A} : At Γ i A → DeterminedTerm Γ (.var i) A
  | op {Γ a} {p : Φ} : DeterminedTerm Γ a (instrSrc p) → DeterminedTerm Γ (.op p a) (instrTrg p)
  | unit {Γ} : DeterminedTerm Γ .unit .unit
  | pair {Γ a b A B} : DeterminedTerm Γ a A → DeterminedTerm Γ b B →
      DeterminedTerm Γ (.pair a b) (.product A B)
  | inl {Γ a A B} : DeterminedTerm Γ a A → DeterminedTerm Γ (.inl a) (.coprod A B)
  | inr {Γ b A B} : DeterminedTerm Γ b B → DeterminedTerm Γ (.inr b) (.coprod A B)
  | abort {Γ a A} : DeterminedTerm Γ a .empty → DeterminedTerm Γ (.abort a) A
  | let₁ {Γ a b A B} : TypeDetermined Γ a A → DeterminedTerm Γ a A →
      DeterminedTerm (A :: Γ) b B → DeterminedTerm Γ (.let₁ a b) B
  | let₂ {Γ a b A B D} : TypeDetermined Γ a (.product A B) → DeterminedTerm Γ a (.product A B) →
      DeterminedTerm (B :: A :: Γ) b D → DeterminedTerm Γ (.let₂ a b) D
  | case {Γ a l r A B D} : TypeDetermined Γ a (.coprod A B) → DeterminedTerm Γ a (.coprod A B) →
      DeterminedTerm (A :: Γ) l D → DeterminedTerm (B :: Γ) r D → DeterminedTerm Γ (.case a l r) D

/-- The simultaneous exact typing constraints on the entry and all blocks
force this internal label family. -/
@[expose] def LabelsDetermined (Γ : VCtx (Ty κ)) (L : LCtx (Ty κ)) {n : Nat} (entry : Region Φ)
    (blocks : Fin n → Region Φ) (R : Fin n → Ty κ) : Prop :=
  ∀ S : Fin n → Ty κ, entry.HasType Γ (List.ofFn S ++ L) →
    (∀ i, (blocks i).HasType (S i :: Γ) (List.ofFn S ++ L)) → S = R

/-- Local type choices are forced at fixed value and label contexts, recursively
including the entry and every block of a CFG. -/
inductive DeterminedRegion : VCtx (Ty κ) → Region Φ → LCtx (Ty κ) → Prop where
  | br {Γ L i a A} : At L i A → DeterminedTerm Γ a A → DeterminedRegion Γ (.br i a) L
  | let₁ {Γ L a b A} : TypeDetermined Γ a A → DeterminedTerm Γ a A →
      DeterminedRegion (A :: Γ) b L → DeterminedRegion Γ (.let₁ a b) L
  | let₂ {Γ L a b A B} : TypeDetermined Γ a (.product A B) → DeterminedTerm Γ a (.product A B) →
      DeterminedRegion (B :: A :: Γ) b L → DeterminedRegion Γ (.let₂ a b) L
  | case {Γ L a l r A B} : TypeDetermined Γ a (.coprod A B) → DeterminedTerm Γ a (.coprod A B) →
      DeterminedRegion (A :: Γ) l L → DeterminedRegion (B :: Γ) r L →
      DeterminedRegion Γ (.case a l r) L
  | cfg {Γ L n entry blocks} {R : Fin n → Ty κ} :
      LabelsDetermined Γ L entry blocks R →
      DeterminedRegion Γ entry (List.ofFn R ++ L) →
      (∀ i, DeterminedRegion (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
      DeterminedRegion Γ (.cfg entry n blocks) L

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
