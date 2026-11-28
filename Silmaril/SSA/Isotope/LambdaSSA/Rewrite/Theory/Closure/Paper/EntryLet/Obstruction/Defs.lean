module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Resumption.Thms

/-! # A terminating observation for flat CFG sequencing -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction

open SequencingObstruction (Instruction)

abbrev U : Ty Empty := .unit

/-- A terminating run records its exact exit, payload, and diagnostic bits. -/
structure Observation where
  label : Nat
  payload : Value Empty
  effect : Bool
  marked : Bool

/-- Acyclic forwarding from local label zero through label one to the outward exit. -/
def blocks : Fin 2 → Region Instruction :=
  Fin.cases (.br 1 (.var 0)) (fun _ => .br 2 (.var 0))

def request : Tm Instruction := .op .tick (.var 0)

def flatRequest : Region Instruction := .cfg (.let₁ request (.br 0 (.var 0))) 2 blocks

def movedRequest : Region Instruction :=
  .let₁ request (.cfg (.br 0 (.var 0)) 2
    (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift Nat.succ)))

/-- Return a recurrent Unit packet after the two local transfers. -/
def flatRecurringRequest : Region Instruction :=
  compLSubst (fun _ => flatRequest) (fun _ => .br 0 (.inr .unit)) 0

def movedRecurringRequest : Region Instruction :=
  compLSubst (fun _ => movedRequest) (fun _ => .br 0 (.inr .unit)) 0

/-- Sequence two requests through an outward-only one-label continuation. -/
def sequenceRequests (p q : Region Instruction) : Region Instruction :=
  CfgEta.singleCfg p
    ((q.renameVars (Silmaril.DeBruijn.lift Nat.succ)).renameLabels Nat.succ)

def twoFlatRequests : Region Instruction := sequenceRequests flatRequest flatRecurringRequest

def firstRequestMoved : Region Instruction := sequenceRequests movedRequest flatRecurringRequest

def secondRequestMoved : Region Instruction := sequenceRequests flatRequest movedRecurringRequest

def bothRequestsMoved : Region Instruction := sequenceRequests movedRequest movedRecurringRequest

/-- The input substitution produced by precomposing with a Unit return. -/
def discardInput : Nat → Tm Instruction :=
  Tm.singleSubst .unit ∘ Silmaril.DeBruijn.lift Nat.succ

/-- A native case expansion copies the discarded-input request into both arms. -/
def duplicatedRequest : Region Instruction :=
  .case (.var 0) ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ)
    ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ)

/-- Move the request out of its local CFG in just the first copy. -/
def oneMovedRequest : Region Instruction :=
  .case (.var 0) ((movedRecurringRequest.substVars discardInput).renameVars Nat.succ)
    ((flatRecurringRequest.substVars discardInput).renameVars Nat.succ)

def unaryBlock : Region Instruction := .br 1 (.var 0)

/-- Run the request under a unary binder before the two local transfers. -/
def nestedRequest : Region Instruction :=
  .cfg (CfgEta.singleCfg (.let₁ request (.br 0 (.var 0))) unaryBlock) 2 blocks

/-- Move the let within the outer scope using the unary sequencing equation. -/
def nestedMoved : Region Instruction :=
  .cfg (.let₁ request (CfgEta.singleCfg (.br 0 (.var 0))
    (unaryBlock.renameVars (Silmaril.DeBruijn.lift Nat.succ)))) 2 blocks

def unitEnv : Semantics.Env Empty := fun _ => .unit

def finish (mark : Bool) : Observation := ⟨0, .unit, true, mark⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction
