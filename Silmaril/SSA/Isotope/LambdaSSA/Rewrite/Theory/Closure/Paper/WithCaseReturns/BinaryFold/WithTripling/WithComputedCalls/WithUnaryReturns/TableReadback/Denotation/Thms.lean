module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Denotation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Denotation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Denotation

/-! # Categorical validity of the written live-table packing equation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [HasFiniteCoproducts C] [Iteration C]

/-- Ordinary rolling supplies conjugacy for every invertible pure state map. -/
theorem PureIsoIteration.of_rolling (J : V ⥤ C) (roll : IterationRolling C) : PureIsoIteration J :=
  fun p f g square =>
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.iterate_iso_of_rolling
      roll (J.mapIso p) f g square

variable [CartesianMonoidalCategory V] [HasFiniteCoproducts V] [DistributiveTensor V]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)

/-- The finite coproduct of captured row packets is purely isomorphic to
the exact written dispatcher state. Each packet carries its own row type. -/
noncomputable def packetStateIso {n : Nat} (X : τ) (R : Fin (n + 1) → τ) :
    (∐ fun i => ctxObj M [X] ⊗ M.obj (R i)) ≅
      M.obj (Silmaril.product X (packedExitType (List.ofFn R))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.packetStateIso M X R

/-- Each coproduct injection becomes the original tag paired with the
unchanged capture. -/
theorem packetStateIso_row {n : Nat} (X : τ) (R : Fin (n + 1) → τ) (i : Fin (n + 1))
    (hi : At (List.ofFn R) i (R i)) :
    Sigma.ι (fun j => ctxObj M [X] ⊗ M.obj (R j)) i ≫ (packetStateIso M X R).hom =
      (ctxObj M [X] ◁ packedLabelInject M i hi) ≫
        ((λ_ (M.obj X)).hom ▷ M.obj (packedExitType (List.ofFn R))) ≫
          (M.productIso X (packedExitType (List.ofFn R))).inv :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.packetStateIso_leg
    M X R i hi

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [DistributivePremonoidalCategory C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ U W : V, ∃ h : J.obj U ⊗ J.obj W = J.obj (U ⊗ W),
    Functor.StrongPremonoidal.tensorIso (J := J) U W = eqToIso h)
include shared

/-- The actual typed CFG and its literal singleton dispatcher agree in
the model. The final feedback comparison uses only pure iso transport. -/
theorem denote_packed_table_of_iso_transport (transport : PureIsoIteration J)
    {n : Nat} (R : Fin (n + 1) → τ) {X D : τ} {e : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    denoteSingletonRegion J M (ValueBranches.cfg R he hb).hasType =
      denoteSingletonRegion J M (packedReadbackRep R he hb).property.hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.denote_packed_table
    J M shared R he hb transport

/-- Rolling alone handles the final change of feedback coordinates. -/
theorem denote_packed_table_of_rolling (roll : IterationRolling C)
    {n : Nat} (R : Fin (n + 1) → τ) {X D : τ} {e : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    denoteSingletonRegion J M (ValueBranches.cfg R he hb).hasType =
      denoteSingletonRegion J M (packedReadbackRep R he hb).property.hasType :=
  denote_packed_table_of_iso_transport M J shared (PureIsoIteration.of_rolling J roll) R he hb

/-- The existing strong Elgot Freyd model interface supplies the pure
isomorphism instance needed by the captured table theorem. -/
theorem denote_packed_table {n : Nat} (R : Fin (n + 1) → τ) {X D : τ}
    {e : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    denoteSingletonRegion J M (ValueBranches.cfg R he hb).hasType =
      denoteSingletonRegion J M (packedReadbackRep R he hb).property.hasType :=
  denote_packed_table_of_iso_transport M J shared
    (fun p f g square => ElgotFreydCategory.pure_uniformity J f g p.hom square) R he hb

/-- The original and packed arrows have equal images under the supported
denotation of the unchanged unary-return quotient. -/
theorem denoteFunctor_map_packed_table {ε : Type*} [HasEff Φ ε] (pe : ε)
    {n : Nat} (R : Fin (n + 1) → τ) {X D : τ} {e : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    let S := Step (τ := τ) (Φ := Φ) pe
    let F := denoteFunctor (Φ := Φ) pe J M shared
    F.map (Paper.Extension.Singleton.ofRegion S (ValueBranches.cfg R he hb)) =
      F.map (Paper.Extension.Singleton.ofRegion S (packedReadbackRep R he hb).property) := by
  change (Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)).map _ =
    (Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)).map _
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion, Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  exact denote_packed_table M J shared R he hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
