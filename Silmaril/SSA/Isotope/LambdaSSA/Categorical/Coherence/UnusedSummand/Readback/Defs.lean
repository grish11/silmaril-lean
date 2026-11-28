module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs

/-! # Local label constraints in a typed unused-summand CFG -/

@[expose] public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

/-- A local label occurs as a written jump target in a row. Both case arms
contribute typing constraints. -/
def Row.targets (i : Fin n) : {Δ : VCtx (Ty κ)} → Row (Φ := Φ) R L Δ → Prop
  | _, .jump j _ => j = i
  | _, .exit .. => False
  | _, .let₁ _ body => body.targets i
  | _, .let₂ _ body => body.targets i
  | _, .case _ left right => left.targets i ∨ right.targets i

/-- The label has an incoming jump in the written entry or a written row. -/
def Program.targets (p : Program (Φ := Φ) R L Γ) (i : Fin n) : Prop :=
  p.entry.targets i ∨ ∃ j, (p.blocks j).targets i

/-- The written entry and rows supply a local-jump typing constraint
for every internal label. -/
def Program.targetsEveryLabel (p : Program (Φ := Φ) R L Γ) : Prop :=
  ∀ i, p.targets i

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (M : TypeModel (Ty κ) V)
  [InstructionModel J M Φ]

/-- A witness whose actual internal label family is the common family
or the indicated widened family. -/
abbrev Program.denotesAt {k : Nat} {P : Fin (k + 1) → Ty κ}
    (p : Program (Φ := Φ) P L Γ) (tails : Option (Fin (k + 1) → Ty κ))
    (f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)) : Prop :=
  CfgDenotesAt J M (family P tails) (p.entry.region tails.isSome id)
    (fun i => (p.blocks i).region tails.isSome Nat.succ) f

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
