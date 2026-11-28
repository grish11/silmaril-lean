module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Defs

/-! # Pointwise refinement of payload-indexed request trees -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

/-- Compare the opcode and evaluated argument, then compare continuations on
every actual typed reply. A pending request can fault or diverge before
returning any reply. -/
def Tree.Refines : Tree S → Tree S → Prop
  | .stop a, .stop b => a.Refines b
  | .ask _ _ _, .stop .ub => True
  | .ask f arg arms, .ask g arg' next => ∃ same : f = g,
      arg.val = arg'.val ∧ ∀ i a,
        let reply : CFG.Dependent.Packet (S.replies g) := same ▸ (⟨i, a⟩ : CFG.Dependent.Packet (S.replies f))
        (arms i a).Refines (next reply.1 reply.2)
  | _, _ => False

/-- The prefix records replies that both trees can take, up to the last
state where it tests their difference. -/
inductive Tree.Follows : {n : Nat} → Tree S → Prefix S.replies n → Prop
  | stop (t : Tree S) (test : Option (Φ × Value Unit)) : Follows t (.stop test)
  | step {n : Nat} {f : Φ} {arg : Syntax.Payload (instrSrc f)}
      {arms : (i : Fin (S.replies f).length) → Syntax.Payload ((S.replies f).get i) → Tree S}
      {i : Fin (S.replies f).length} {a : Syntax.Payload ((S.replies f).get i)}
      {rest : Prefix S.replies n} :
      Follows (arms i a) rest → Follows (.ask f arg arms) (.step f arg.val i a rest)

/-- A uniform request budget, stated without enumerating reply values. -/
def Tree.Fits : Tree S → Nat → Prop
  | .stop _, _ => True
  | .ask _ _ _, 0 => False
  | .ask _ _ arms, n + 1 => ∀ i a, (arms i a).Fits n

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
