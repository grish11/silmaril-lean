module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Prefix.Defs

/-! # Router tables in the request-prefix model

The request-prefix model has the monad, values and iterator of the
four-reply interpreter. Its request can also be observed after it is sent
and before any reply. That observation is tagged with the request's label
and carries the log of the exchanges completed before it.

So a router table has two kinds of observation here: complete runs, with
their returned Bit, and open prefixes, one for every request that is
sent. A run that never returns still has its open prefixes.
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

variable {K : Nat}
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance routerPrefixInstructions : InstructionModel J M signature.Instr :=
  instructions prefixModel
local instance routerPrefixCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

/-- The dispatcher step in the request-prefix model. -/
noncomputable def Router.prefixStepM (t : Router K) : value (States K) → Trace (value Bit ⊕ value (States K)) :=
  fun v => (denoteSingletonRegion J M (dispatch_typed K t.rows_typed).hasType).of v

/-- Observations in the request-prefix model: complete runs as `ok`, and
for each request that is sent the log before it, as `error` with the
request's label. -/
noncomputable def Router.prefixObservations (t : Router K) (i : Fin (K + 1)) (g : Bool) :
    Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (t.entered_typed i).hasType).of (Sum.inl (bit g))).outcomes

/-- What follows the first event of an observation, by the action taken. -/
def Router.PrefixCont (t : Router K) : Act K → Except Bool (value Bit) → Word → Prop
  | .ret c, r, v => r = .ok (bit c) ∧ v = 1
  | .go j q, r, v => (r, v) ∈ t.prefixObservations j q

/-! ## Regression tables -/

/-- Two states without returning replies: state zero moves to state one,
which repeats into itself. -/
def chainAct (_ : Fin 2) (_ pl : Bool) : Act 1 := .go 1 pl

def chainLabel (a b : Bool) (i : Fin 2) : Bool :=
  match i with
  | 0 => a
  | 1 => b

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
