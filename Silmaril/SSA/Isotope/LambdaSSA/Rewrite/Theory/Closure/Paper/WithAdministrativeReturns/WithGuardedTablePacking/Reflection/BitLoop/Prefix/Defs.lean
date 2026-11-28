module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Defs

/-! # A request-prefix observation model

The monad, value category and iterator are those of the four-reply model.
Only the primitive changes: a request can also be observed after it is
sent and before any reply. That observation carries the request's label
and the log of the exchanges completed before it.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace request Op)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions regionCoherent)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

/-- All four replies of the complete-run model, and one incomplete
observation tagged with the label of the pending request. -/
def prefixRequest (label : Bool) (q : value Bit) : Trace (value Answer) :=
  Tagged.withIncomplete label {1} (request label q)

def prefixModel : _root_.Silmaril.Isotope.Semantics.InstructionModel value signature.Instr Trace where
  eval
    | .ask label => prefixRequest label

/-- Every primitive of the signature is effectful, so this condition is vacuous. -/
theorem prefix_respectsPure :
    _root_.Silmaril.Isotope.Semantics.InstructionModel.RespectsPure (ε := Bool) prefixModel := by
  intro f h
  cases f; cases h

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

/-- Region typing coherence, from the structural coherence of ordered-trace
Kleisli models. The fallback for ill-typed inputs has no observation. -/
theorem prefixCoherent :
    letI := instructions prefixModel
    RegionTypingCoherent (Φ := signature.Instr) J M :=
  regionCoherent prefixModel prefix_respectsPure (Tagged.ofOutcomes ∅)

noncomputable local instance : InstructionModel J M signature.Instr := instructions prefixModel
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

/-- The dispatcher step at the exact packed representative, in this model. -/
noncomputable def prefixStep (p : Program) : value State → Trace (value Bit ⊕ value State) :=
  fun s => (denoteSingletonRegion J M p.typed.packExits.hasType).of (Sum.elim id PEmpty.elim s)

/-- Observations of the literal loop in this model: complete returns and
pending requests. -/
noncomputable def prefixObservations (p : Program) (g : Bool) : Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (loop_typed p).hasType).of (Sum.inl (bit g))).outcomes

/-- One request on the state. Each reply side either repeats with the
payload or returns it. Polls and `askSpin` have this form. -/
def oneAsk (label repeatLeft repeatRight : Bool) : Program :=
  .ask label (.read 0) (.ret (if repeatLeft then 1 else 0) 0) (.ret (if repeatRight then 1 else 0) 0)

def leafValue (again : Bool) (a : value Bit) : value Bit ⊕ value State :=
  if again then .inr (.inl a) else .inl a

def route (repeatLeft repeatRight : Bool) : value Answer → value Bit ⊕ value State
  | .inl a => leafValue repeatLeft a
  | .inr a => leafValue repeatRight a

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix
