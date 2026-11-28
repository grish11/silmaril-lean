module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Coherence.Thms

/-! # The remaining strong Elgot law for the chosen extended syntax -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

universe u v w
variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)] {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "T" => Step (τ := Ty κ) (Φ := Φ) pe
local notation "inc" => inclusion T
local notation "Val" => Paper.Extension.Singleton.StructuralValues.ValueCategory T

local instance : Fact (IncludesUnitEta T) :=
  ⟨fun h => .inl (.inl (Paper.WithCaseReturns.includeUnit pe h))⟩

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive guardedIteration guardedElgot
attribute [local instance] Paper.Extension.Singleton.StructuralValues.hasFiniteCoproducts

/-- The existing chosen syntax structures supply the strong Elgot model
interface exactly when its structural-state uniformity law is available. -/
theorem chosen_strongElgot_iff :
    Nonempty (StrongElgotFreydCategory (inc)) ↔ StructuralUniformity T :=
  ⟨fun ⟨laws⟩ => fun f g h square => laws.toElgotFreydCategory.uniformity f g h square,
    fun uniform => ⟨strongElgotOfStructuralUniformity T uniform⟩⟩

/-- The conditional model uses the canonical shared tensor comparison. -/
theorem sharedTensor_of_uniformity (uniform : StructuralUniformity T) (X Y : Val) :
    letI := strongElgotOfStructuralUniformity T uniform
    ∃ h : (inc).obj X ⊗ (inc).obj Y = (inc).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := inc) X Y = eqToIso h := by
  change letI := (distributiveFreyd T).toFreydCategory
    ∃ h : (inc).obj X ⊗ (inc).obj Y = (inc).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := inc) X Y = eqToIso h
  rw [distributiveFreyd_toFreydCategory]
  exact sharedTensor T X Y

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
