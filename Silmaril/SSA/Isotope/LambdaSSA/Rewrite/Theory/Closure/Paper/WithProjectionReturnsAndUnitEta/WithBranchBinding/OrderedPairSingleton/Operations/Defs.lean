module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs

/-! # Literal fixed-factor, case and structural operations on raw singleton representatives -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

open Silmaril CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType ofRegion)

open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory (whiskerLeftRegion whiskerRightRegion whiskerLeftRegion_typed
  whiskerRightRegion_typed productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Raw" => RawTypeCategory (τ := τ) Φ pe
local notation "H" => RawHom (Φ := Φ) pe

variable {A B D : τ}

/-- Bind the step's exits before substituting the paired return on the right. -/
def whiskerLeftRep (X : τ) (r : Rep (Φ := Φ) A B) :
    Rep (Φ := Φ) (product X A) (product X B) :=
  ⟨whiskerLeftRegion r.val.bindBranchArguments,
    (whiskerLeftRegion_typed X r.property.bindBranchArguments).hasType⟩

/-- Bind the step's exits before substituting the paired return on the left. -/
def whiskerRightRep (X : τ) (r : Rep (Φ := Φ) A B) :
    Rep (Φ := Φ) (product A X) (product B X) :=
  ⟨whiskerRightRegion r.val.bindBranchArguments,
    (whiskerRightRegion_typed X r.property.bindBranchArguments).hasType⟩

/-- Select the arm on the input tag and weaken it past the retained sum. -/
def copairRep (r : Rep (Φ := Φ) A D) (s : Rep (Φ := Φ) B D) :
    Rep (Φ := Φ) (coprod A B) D :=
  ⟨.case (.var 0) (r.val.renameVars (lift Nat.succ)) (s.val.renameVars (lift Nat.succ)),
    .case (.var (i := 0) rfl) (r.property.renameVars ((Ren.wk [] (coprod A B)).lift A))
      (s.property.renameVars ((Ren.wk [] (coprod A B)).lift B))⟩

/-- The raw singleton primitive branches directly on the instruction result. -/
def primitive (p : Φ) : H (instrSrc (τ := τ) p) (instrTrg (τ := τ) p) :=
  rawClass pe (.br (ℓ := 0) rfl (.op (f := p) (.var (i := 0) rfl)))

def discard (A : τ) : H A Silmaril.unit :=
  rawClass pe (.br (ℓ := 0) rfl .unit)

def diagonal (A : τ) : H A (product A A) :=
  rawClass pe (.br (ℓ := 0) rfl (.pair (.var (i := 0) rfl) (.var (i := 0) rfl)))

def productFst (A B : τ) : H (product A B) A :=
  rawClass pe (productFstBranches A B).hasType

def productSnd (A B : τ) : H (product A B) B :=
  rawClass pe (productSndBranches A B).hasType

def sumInl (A B : τ) : H A (coprod A B) :=
  rawClass pe (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))

def sumInr (A B : τ) : H B (coprod A B) :=
  rawClass pe (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))

def fromEmpty (A : τ) : H Silmaril.empty A :=
  rawClass pe (Paper.TypeCategory.emptyRegion_typed A).hasType

def braid (A B : τ) : H (product A B) (product B A) :=
  rawClass pe (Paper.TypeCategory.braidBranches A B).hasType

def associate (A B C : τ) : H (product (product A B) C) (product A (product B C)) :=
  rawClass pe (Paper.TypeCategory.associate_typed A B C).hasType

def unassociate (A B C : τ) : H (product A (product B C)) (product (product A B) C) :=
  rawClass pe (Paper.TypeCategory.unassociate_typed A B C).hasType

def leftUnitSection (A : τ) : H A (product Silmaril.unit A) :=
  rawClass pe (.br (ℓ := 0) rfl (.pair .unit (.var (i := 0) rfl)))

def rightUnitSection (A : τ) : H A (product A Silmaril.unit) :=
  rawClass pe (.br (ℓ := 0) rfl (.pair (.var (i := 0) rfl) .unit))

/-- The exact syntax sum with its literal raw injections. -/
def sumCofan (A B : τ) : BinaryCofan (⟨A⟩ : Raw) ⟨B⟩ :=
  BinaryCofan.mk (P := ⟨coprod A B⟩) (sumInl pe A B) (sumInr pe A B)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations
