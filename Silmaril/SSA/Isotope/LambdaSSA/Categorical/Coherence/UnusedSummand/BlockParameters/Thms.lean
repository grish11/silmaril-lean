module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.Typing
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.Dispatch

/-! # Witness agreement for determined, reachable block parameters -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

/-- A synthesizing entry jump fixes the first parameter type. Each later
written jump from a reached block fixes the next one in that exact context.
The conclusion covers each label with such a path. -/
theorem Program.type_at_reached {R S : Fin n → Ty κ} (p : Program (Φ := Φ) R L Γ)
    (he : (p.entry.region false id).HasType Γ (List.ofFn S ++ L))
    (hb : ∀ i, (p.blocks i).region.HasType (S i :: Γ) (List.ofFn S ++ L))
    {i : Fin n} (path : p.Reaches i) : S i = R i :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.type_at_reached
    p he hb path

/-- A direct outward branch returning the block parameter also constrains
its type, through the exact outward label interface. -/
theorem outward_parameter_type {S : Fin n → Ty κ} {i : Fin n} {j : Nat} {A : Ty κ} (exit : At L j A)
    (typed : (Region.br (n + j) (.var 0) : Region Φ).HasType (S i :: Γ) (List.ofFn S ++ L)) :
    S i = A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.outward_parameter_type
    exit typed

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty κ) V) [InstructionModel J M Φ]

/-- Read the actual graph family and recover the type of each reached
parameter from that graph's exact entry and rows. -/
theorem Program.denotes_readback {k : Nat} {R : Fin (k + 1) → Ty κ}
    (p : Program (Φ := Φ) R L Γ) {t : p.region.HasType Γ L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M t f) :
    ∃ S : Fin (k + 1) → Ty κ,
      CfgDenotesAt J M S (p.entry.region false id) (fun i => (p.blocks i).region) f ∧
      ∀ i, p.Reaches i → S i = R i :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.readback_reached
    J M p d

/-- Compare arbitrary exact graph witnesses. Their live input types are
recovered from the witnessed entry and rows. Rolling restricts dispatch to
written targets and retains the original ordered outward interface. -/
theorem Program.denotes_eq {k : Nat} {R : Fin (k + 1) → Ty κ}
    (p : Program (Φ := Φ) R L Γ) (roll : IterationRolling C) (closed : p.ReachableParameters)
    {t : p.region.HasType Γ L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) (e : RegionDenotes J M t g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.compare
    J M p roll closed d e

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters
