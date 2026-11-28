module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Defs

/-! # Executable refinement at every typed caller packet -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

/-- An explicit exhaustive list of values at the exact caller type. -/
structure CallerEnumeration (A : Syntax.Ty) where
  packets : List (Syntax.Payload A)
  complete : ∀ input, input ∈ packets

structure InterfaceCounterexample (S : RequestSignature Φ) (A : Syntax.Ty) where
  input : Syntax.Payload A
  length : Nat
  probe : Prefix S.replies length

inductive InterfaceVerdict (S : RequestSignature Φ) (A : Syntax.Ty) where
  | refines
  | counterexample (witness : InterfaceCounterexample S A)

/-- Attach the caller packet to a pointwise rejection. -/
def Verdict.counterexampleAt {A : Syntax.Ty} (input : Syntax.Payload A) :
    Verdict S → Option (InterfaceCounterexample S A)
  | .refines => none
  | .counterexample n probe => some ⟨input, n, probe⟩

/-- Check both original CFGs once, even at an empty caller interface.
For checked CFGs, return the first packet and feasible prefix that fail. -/
def Table.compareInterface? [DecidableEq Φ] {R₀ R₁ : List Syntax.Ty}
    (g₀ : Table S R₀) (g₁ : Table S R₁) (replies : ReplyEnumeration S)
    (raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits)
    (raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits)
    (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (callers : CallerEnumeration (R₀.get g₀.entry)) :
    Option (InterfaceVerdict S (R₀.get g₀.entry)) :=
  if left : g₀.check raw₀ = true then
    if right : g₁.check raw₁ = true then
      let failure := callers.packets.findSome? fun input =>
        let p := g₀.extract (g₀.checked_rank left) input
        let q := g₁.extract (g₁.checked_rank right) (cast (congrArg Syntax.Payload same) input)
        (p.compare replies q).counterexampleAt input
      some (match failure with
        | none => .refines
        | some witness => .counterexample witness)
    else none
  else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
