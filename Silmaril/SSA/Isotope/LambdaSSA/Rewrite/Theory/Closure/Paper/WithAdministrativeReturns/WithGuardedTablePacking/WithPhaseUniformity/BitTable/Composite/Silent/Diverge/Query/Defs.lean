module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Defs

/-! # The query-aware request-prefix model

The request-prefix model records a pending request with its label and
the log of the exchanges completed before it. The query of the request
appears only in the event of a completed exchange.

`queryRequest` adds the query to the pending observation: the log of a
pending request ends with `pendingWord label query`, the mark of that
request. The monad, the values, the iterator and the completed exchanges
are those of the request-prefix model. `queryModel` interprets the
request by `queryRequest`, and `queryCoherent` is its region typing
coherence, by the same structural fact as for the request-prefix model.
So it is one of the supported models.

`Router.queryObservations` are the observations of a router table in
this model, and `Router.QueryCont` what follows a first exchange.

`blindLabel` and `blindAct s` are a labelled row that repeats with the
query `s` to a blind request, all of whose replies lead to a silent row.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (request queryBit)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (regionCoherent)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Answer)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

variable {K : Nat}

/-- The mark of a pending request: its label and its query. -/
def pendingWord (label query : Bool) : Word := FreeMonoid.of (event label query (false, false))

/-- All four replies of the complete-run model, and one incomplete
observation tagged with the label of the pending request, whose log is
the mark of that request. -/
def queryRequest (label : Bool) (q : value Bit) : Trace (value Answer) :=
  Tagged.withIncomplete label {pendingWord label (queryBit q)} (request label q)

def queryModel : _root_.Silmaril.Isotope.Semantics.InstructionModel value signature.Instr Trace where
  eval
    | .ask label => queryRequest label

/-- Every primitive of the signature is effectful, so this condition is vacuous. -/
theorem query_respectsPure :
    _root_.Silmaril.Isotope.Semantics.InstructionModel.RespectsPure (ε := Bool) queryModel := by
  intro f h
  cases f; cases h

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

/-- Region typing coherence, from the structural coherence of ordered-trace
Kleisli models, as for the request-prefix model. -/
theorem queryCoherent :
    letI := instructions queryModel
    RegionTypingCoherent (Φ := signature.Instr) J M :=
  regionCoherent queryModel query_respectsPure (Tagged.ofOutcomes ∅)

noncomputable local instance routerQueryInstructions : InstructionModel J M signature.Instr :=
  instructions queryModel
local instance routerQueryCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := queryCoherent

/-- The dispatcher step in the query-aware model. -/
noncomputable def Router.queryStepM (t : Router K) : value (States K) → Trace (value Bit ⊕ value (States K)) :=
  fun v => (denoteSingletonRegion J M (dispatch_typed K t.rows_typed).hasType).of v

/-- Observations in the query-aware model: complete runs as `ok`, and for
each request that is sent the log before it followed by the mark of the
request, as `error` with the request's label. -/
noncomputable def Router.queryObservations (t : Router K) (i : Fin (K + 1)) (g : Bool) :
    Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (t.entered_typed i).hasType).of (Sum.inl (bit g))).outcomes

/-- What follows the first event of an observation, by the action taken. -/
def Router.QueryCont (t : Router K) : Act K → Except Bool (value Bit) → Word → Prop
  | .ret c, r, v => r = .ok (bit c) ∧ v = 1
  | .go j q, r, v => (r, v) ∈ t.queryObservations j q

/-! ## Regression tables -/

/-- A labelled row in front of a blind request and a silent row. -/
def blindLabel (m l : Bool) (i : Fin 3) : Option Bool :=
  match i with
  | 0 => some m
  | 1 => some l
  | 2 => none

/-- Row zero repeats to the blind request with the query `s`. Every reply
of the blind request leads to the silent row. -/
def blindAct (s : Bool) (i : Fin 3) (_ _ : Bool) : Act 2 :=
  match i with
  | 0 => .go 1 s
  | 1 => .go 2 false
  | 2 => .go 2 false

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
