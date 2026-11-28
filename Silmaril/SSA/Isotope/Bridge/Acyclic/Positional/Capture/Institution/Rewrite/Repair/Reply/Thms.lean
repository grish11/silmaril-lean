module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Normalize

/-! # Replaying the effectful reply-tree normal form -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open Isotope.LetCase.LocallyNameless (AbortEquiv)

/-- The replay leaves the selected return operand at each leaf intact. -/
theorem Tree.normalize_operandWith {R : Type} {A : Sorts} (ret : ReturnOperand R A)
    (p : Tree R) {n : Nat} (β : BoundCtx Sorts n) :
    AbortEquiv false (Ctx.nil : Ctx Empty Sorts) β
      (p.operandWith ret β).1 (p.normal.render.operandWith ret β).1 A :=
  normalize_operand_proof ret p β

/-- Replay native `bindCase` at an effectful discriminator, then normalize
each selected continuation under its payload binder. -/
theorem Tree.normalize_operand (p : Tree) {n : Nat} (β : BoundCtx Sorts n) :
    AbortEquiv false (Ctx.nil : Ctx Empty Sorts) β
      (p.operand β).1 (p.normal.render.operand β).1 Ty.unit :=
  p.normalize_operandWith unitReturn β

theorem repaired_of_normal (tail : List Sorts) (p q : Tree) (h : p.normal = q.normal) :
    Repaired false (equation tail p q) :=
  repaired_of_normal_proof tail p q h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
