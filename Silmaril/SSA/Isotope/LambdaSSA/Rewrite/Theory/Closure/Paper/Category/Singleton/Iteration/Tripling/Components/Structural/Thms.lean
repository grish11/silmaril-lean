module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTripling

/-! # Exact tripling transport on finite structural recurrence types -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

/-- The written short-circuit sequence transports only its recurrence object. -/
theorem transport_three_rounds {A D B : P} (e : A ≅ D) (g : D ⟶ B ⨿ D) :
    thenOnRepeat (transport e g) (thenOnRepeat (transport e g) (transport e g)) =
      transport e (thenOnRepeat g (thenOnRepeat g g)) := by
  rw [transport_thenOnRepeat, transport_thenOnRepeat]

/-- Native tripling transports along an exact state isomorphism with the
original outward object. In particular it applies to pure state changes. -/
theorem iterate_triple_transport_iff {A D B : P} (e : A ≅ D) (g : D ⟶ B ⨿ D) :
    iterate (thenOnRepeat (transport e g) (thenOnRepeat (transport e g) (transport e g))) =
      iterate (transport e g) ↔
    iterate (thenOnRepeat g (thenOnRepeat g g)) = iterate g := by
  rw [transport_three_rounds, iterate_transport, iterate_transport, cancel_epi]

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

open Paper.TypeCategory.ComponentTripling (StructuralState)
variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Obj" => ofType (Φ := Φ) Seed

/-- The written expansion transports in the contextual quotient as well. -/
theorem transport_triple {A D B : Q} (e : A ≅ D) (g : D ⟶ B ⨿ D) :
    triple (transportStep Seed e g) = transportStep Seed e (triple g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTripling.transport_triple Seed e g

/-- Invertible state changes preserve and reflect tripling in the quotient. -/
theorem triple_transport_iff {A D B : Q} (e : A ≅ D) (g : D ⟶ B ⨿ D) :
    iterateChosen Seed (triple (transportStep Seed e g)) = iterateChosen Seed (transportStep Seed e g) ↔
      iterateChosen Seed (triple g) = iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTripling.triple_transport_iff Seed e g

/-- Normalize the original recurrence type with guarded distributors, empty
elimination and Unit insertion/projection. The inverse equations for the
unitors use the existing Unit η equations. -/
noncomputable def structuralStateIso
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    (t : StructuralState) :
    Obj t.ty ≅ Obj t.tree.ty :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTripling.stateIso Seed includeUnit t

/-- The same written step and its short-circuit three-round expansion have
equal iteration at the original state and outward objects. -/
theorem triple_step_structural
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    (t : StructuralState) {B : Q} (g : Obj t.ty ⟶ B ⨿ Obj t.ty) :
    iterateChosen Seed (triple g) = iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTripling.triple_step Seed includeUnit t g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
