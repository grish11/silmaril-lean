module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Defs

/-! # Executable comparison of payload-indexed request trees -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

/-- Each list exhausts the dependent sum of reply positions and their typed
payloads for one opcode. Repeated entries are allowed. -/
structure ReplyEnumeration (S : RequestSignature Φ) where
  packets : (f : Φ) → List (CFG.Dependent.Packet (S.replies f))
  complete : ∀ f packet, packet ∈ packets f

inductive Verdict (S : RequestSignature Φ) where
  | refines
  | counterexample (length : Nat) (probe : Prefix S.replies length)

def Verdict.accepted : Verdict S → Bool
  | .refines => true
  | .counterexample .. => false

/-- Keep the first failed branch in the supplied order and record the
actual reply before the rest of its distinguishing prefix. -/
def Tree.compare [DecidableEq Φ] (replies : ReplyEnumeration S) : Tree S → Tree S → Verdict S
  | .stop a, .stop b =>
    if b = .ub ∨ a = b then .refines else .counterexample 0 (.stop none)
  | .ask _ _ _, .stop .ub => .refines
  | .ask f arg arms, .ask g arg' next =>
    if same : (f, arg.val) = (g, arg'.val) then
      let keys : f = g := congrArg Prod.fst same
      let failed := (replies.packets f).findSome? fun reply =>
        let target : CFG.Dependent.Packet (S.replies g) := keys ▸ reply
        match (arms reply.1 reply.2).compare replies (next target.1 target.2) with
        | .refines => none
        | .counterexample n probe =>
          some (.counterexample (n + 1) (.step f arg.val reply.1 reply.2 probe))
      failed.getD .refines
    else .counterexample 0 (.stop (some (f, arg.val)))
  | _, _ => .counterexample 0 (.stop none)

/-- Compare the original typed CFGs at a supplied caller packet after the
exact re-emission and rank checks. An absent verdict signals failed extraction. -/
def Table.compare? [DecidableEq Φ] {R₀ R₁ : List Syntax.Ty}
    (g₀ : Table S R₀) (g₁ : Table S R₁) (replies : ReplyEnumeration S)
    (raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits)
    (raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits)
    (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (input : Syntax.Payload (R₀.get g₀.entry)) : Option (Verdict S) := do
  let p ← g₀.extract? raw₀ input
  let q ← g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input)
  return p.compare replies q

/-- A Boolean refinement verdict for a successfully checked pair of CFGs. -/
def Table.checkRefinement? [DecidableEq Φ] {R₀ R₁ : List Syntax.Ty}
    (g₀ : Table S R₀) (g₁ : Table S R₁) (replies : ReplyEnumeration S)
    (raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits)
    (raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits)
    (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (input : Syntax.Payload (R₀.get g₀.entry)) : Option Bool :=
  (g₀.compare? g₁ replies raw₀ raw₁ same input).map Verdict.accepted

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
