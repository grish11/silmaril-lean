module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs

/-! # Bind-first exact-sum iteration at a normalized seed -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton

open CategoryTheory
open OrderedPairSingleton (Rep iterateRep)
open Paper.Extension.Singleton (ofRegion iterateSum_map)
open SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (S : NormalizedSeed τ Φ)
  {A B : τ}

theorem normalize_iterateRep (r : Rep (Φ := Φ) A (coprod B A)) :
    normalizeHom S (Quotient.mk _ (iterateRep r)) =
      Extension.Singleton.iterateSum S.step (normalizeHom S (Quotient.mk _ r)) := by
  change normalizeHom S (rawClass S (iterateRegion_valueBranches r.property.bindBranchArguments).hasType) =
    Extension.Singleton.iterateSum S.step (ofRegion S.step r.property.bindBranchArguments)
  rw [normalize_guarded, iterateSum_map, Paper.TypeCategory.iterateSum_ofRegion]

/-- Take the class of the literal bind-first feedback CFG. -/
def iterateSum (f : RawHom S A (coprod B A)) : RawHom S A B :=
  Quotient.map iterateRep (fun r s h => Quotient.exact
    (normalizeHom_injective S (by
      rw [normalize_iterateRep, normalize_iterateRep, congrArg (normalizeHom S) (Quotient.sound h)]))) f

theorem normalize_iterateSum (f : RawHom S A (coprod B A)) :
    normalizeHom S (iterateSum S f) = Extension.Singleton.iterateSum S.step (normalizeHom S f) :=
  Quotient.inductionOn f (normalize_iterateRep S)

/-- The typed primitive is a raw branch on the instruction result. -/
def primitive (p : Φ) : RawHom S (instrSrc (τ := τ) p) (instrTrg (τ := τ) p) :=
  rawClass S (.br (ℓ := 0) rfl (.op (f := p) (.var (i := 0) rfl)))

theorem normalize_primitive (p : Φ) :
    normalizeHom S (primitive S p) = (Extension.Singleton.projection S.step).map (Paper.TypeCategory.primitiveReturn p) :=
  rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton
