module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Defs

/-! # Finite comparisons and arbitrary-store guarded refinement -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open Syntax (Payload StatePrimitives)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {n : Nat}

def EntryVerdict.accepted : EntryVerdict Φ A n → Bool
  | .refines => true
  | .counterexample _ => false

/-- Boolean projection of the shared-entry checker. Unsupported readback
still returns none. -/
def Table.checkEntries? [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (callers : CallerEnumeration A)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (stores : StateInventory n) : Option Bool :=
  (g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores).map EntryVerdict.accepted

/-- Pointwise native shaped refinement for all deterministic interpretations
on store types in universe `v`. Exact readback is a separate checker premise. -/
def Table.DeterministicRefines (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (decodeLeft : Payload A → Payload (R.get g.entry)) (decodeRight : Payload A → Payload (T.get h.entry)) : Prop :=
  ∀ (σ : Type v) (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ),
    Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s

/-- The carrier bound from the finite derivations of a concrete pair of
runs. The infinite-sided constructors count only the other run's queries. -/
inductive RefutationBound {σ : Type v} (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (prim : StatePrimitives Φ σ) (s : σ) :
    Nat → Prop where
  | finite {rows₀ rows₁ stop₀ stop₁ size}
      (lower : FiniteRun g a prim ⟨g.entry, a⟩ s rows₀ stop₀)
      (upper : FiniteRun h b prim ⟨h.entry, b⟩ s rows₁ stop₁)
      (bound : size ≤ 1 + rows₀.length + rows₁.length) : RefutationBound g h a b prim s size
  | infiniteLeft {rows stop size}
      (lower : Feedback.Infinite (g.feedback a prim) (blockPoint ⟨g.entry, a⟩ s))
      (upper : FiniteRun h b prim ⟨h.entry, b⟩ s rows stop)
      (bound : size ≤ 1 + rows.length) : RefutationBound g h a b prim s size
  | infiniteRight {rows stop size}
      (lower : FiniteRun g a prim ⟨g.entry, a⟩ s rows stop)
      (upper : Feedback.Infinite (h.feedback b prim) (blockPoint ⟨h.entry, b⟩ s))
      (bound : size ≤ 1 + rows.length) : RefutationBound g h a b prim s size

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
