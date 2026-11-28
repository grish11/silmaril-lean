module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection

/-! # Tripling on retained Bit by native block elimination -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ
local notation "T" => BitState (τ := τ) (Φ := Φ)

/-- Read the written three-phase schedule from its first injection. -/
theorem iterate_cycle_at_first {A B : P} (g : A ⟶ B ⨿ A) :
    coprod.inl ≫ iterate (cycle g) = iterate (thenOnRepeat g (thenOnRepeat g g)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.triple_at_first g

/-- An isomorphism of state objects transports the native iterate at the
same outward object. -/
theorem iterate_change_state {A D B : P} (e : A ≅ D) (g : A ⟶ B ⨿ A) :
    iterate g = e.hom ≫ iterate (e.inv ≫ g ≫ coprod.map (𝟙 B) e.hom) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.iteration_change e g

/-- Running a second round on recurrence commutes with state transport. -/
theorem transport_thenOnRepeat {A D B : P} (e : A ≅ D) (g h : D ⟶ B ⨿ D) :
    thenOnRepeat (transport e g) (transport e h) = transport e (thenOnRepeat g h) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection.transport_batch e g h

/-- Iterate a round in transported state coordinates. -/
theorem iterate_transport {A D B : P} (e : A ≅ D) (f : D ⟶ B ⨿ D) :
    iterate (transport e f) = e.hom ≫ iterate f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection.iterate_transport e f

/-- Either tag may take any recursive or outward route. Reset absorption
only concerns the two Unit payloads of the Bit. -/
theorem iterate_triple {B : P} (g : T ⟶ B ⨿ T)
    (input : resetPayloads ≫ g = g) (output : g ≫ coprod.map (𝟙 B) resetPayloads = g) :
    iterate (thenOnRepeat g (thenOnRepeat g g)) = iterate g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.iterate_triple g input output

/-- A mixed Bit round with literal Unit payloads satisfies tripling in standard Paper. -/
theorem iterate_normalize {B : P} (g : T ⟶ B ⨿ T) :
    iterate (thenOnRepeat (normalize g) (thenOnRepeat (normalize g) (normalize g))) =
      iterate (normalize g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.iterate_normalize g

section PhaseInterleave

universe w z
variable {C : Type w} [Category.{z} C] [HasBinaryCoproducts C]

local notation "Copies" A:max => (A ⨿ (A ⨿ A))

/-- Group three copies of a binary sum by summand, preserving the phase
order inside each summand. This uses only the chosen coproducts. -/
noncomputable def phaseInterleave (A D : C) : Copies (A ⨿ D) ≅ Copies A ⨿ Copies D :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.phaseInterleave A D

theorem phaseInterleave_hom (A D : C) : (phaseInterleave A D).hom =
  coprod.desc (coprod.map coprod.inl coprod.inl)
    (coprod.desc (coprod.map (coprod.inl ≫ coprod.inr) (coprod.inl ≫ coprod.inr))
      (coprod.map (coprod.inr ≫ coprod.inr) (coprod.inr ≫ coprod.inr))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.phaseInterleave_hom A D

theorem phaseInterleave_inv (A D : C) : (phaseInterleave A D).inv =
    coprod.desc (coprod.map coprod.inl (coprod.map coprod.inl coprod.inl))
      (coprod.map coprod.inr (coprod.map coprod.inr coprod.inr)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.phaseInterleave_inv A D

end PhaseInterleave

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Bit" => ofType Seed (Silmaril.coprod (Silmaril.unit : τ) Silmaril.unit)

/-- Projecting a short-circuit sequence preserves both of its written rounds. -/
theorem projectStep_thenOnRepeat {A B : Paper.TypeCategory (τ := τ) Φ} (g h : A ⟶ B ⨿ A) :
    projectStep Seed (Paper.TypeCategory.ComponentTripling.thenOnRepeat g h) =
      projectStep Seed g ≫ coprod.desc coprod.inl (projectStep Seed h) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection.project_batch Seed g h

/-- Unit η lets the native component proof apply to every quotient round
at the exact Bit state, including rounds with mixed effectful recurrence. -/
theorem triple_step_bit
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {B : Q} (g : Bit ⟶ B ⨿ Bit) :
    iterateChosen Seed (triple g) = iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection.triple_step_bit
    Seed includeUnit g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
