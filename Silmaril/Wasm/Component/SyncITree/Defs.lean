module

public import Silmaril.Wasm.Component.Reference.SessionStrat.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs

/-! # Interaction-tree bodies for ready, closed simple components

The input grammar is `Reference.Simple`: one import-free Core module with direct
canonical lifts. Its mutually recursive `ValTy` record and variant grammar has
no stream or future constructor at any depth. `Ready` further requires
`Simple.Adequate` (float-free, flat arities, and the ready instance used by the
reference adequacy theorems). The instance witness excludes a Core start
function. Calls are sequential and non-reentrant. There is no import at which
to reenter. Startup is outside the body, at the chosen instance store. A trap
completes the current round with the store it left, as in the reference
machine's resumable-session extension.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Component.SyncITree

open Silmaril.Games
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Elgot

/-- A successfully instantiated component in the closed, direct-lift fragment. -/
structure Ready (c : Simple) where
  adequate : c.Adequate
  inst : ScalarInstance
  isInst : c.mod.IsInst inst

/-- Select the ready instance supplied by the adequacy witness. -/
def Ready.ofAdequate {c : Simple} (h : c.Adequate) : Ready c :=
  ⟨h, h.inst.inst.choose, h.inst.inst.choose_spec⟩

/-- Component values checked against an exact list of component types. -/
abbrev Values (ts : List ValTy) := {vs : List Val // ValTy.checkList ts vs = true}

/-- An environment question at a particular export, with well-typed arguments. -/
structure Question (c : Simple) where
  exportIdx : Fin c.exports.length
  args : Values c.exports[exportIdx].ty.params

variable {c : Simple}

/-- The component's answer to this question. `none` is a trap. -/
abbrev Question.Answer (q : Question c) := Option (Values c.exports[q.exportIdx].ty.results)

/-- The game of typed export questions and their dependent answers. Its import
side is `sigN 0`. -/
def exportSig (c : Simple) : Sig.{0} := ⟨Question c, Question.Answer⟩

/-- A question at the existing reference session interface. -/
def Question.erase (q : Question c) : Fin c.exports.length × List Val := (q.exportIdx, q.args.val)

/-- A typed question as an operation of the existing component IR game. -/
def Question.gameOp (q : Question c) : (sigN c.toComp.exports.length).Op :=
  (⟨q.exportIdx, by simp [Simple.toComp]⟩, .vals q.args.val)

/-- The terminal Core/ABI judgement for an export body. Both branches retain
the final Core store. -/
def Finishes (o : GrowOracle) (r : Ready c) (q : Question c) (s : Store Nat)
    (a : q.Answer) (s' : Store Nat) : Prop :=
  match a with
  | some ws => RetAt (profile o) c r.inst c.exports[q.exportIdx] q.args.val s ws.val s'
  | none => TrapAt (profile o) c r.inst c.exports[q.exportIdx] q.args.val s s'

/-- The tree's completion. `noOutcome` records absence of both a terminal
Core/ABI judgement and a witnessed infinite internal run. It never answers the
export in the session observer. -/
inductive Completion (q : Question c) where
  | reply (a : q.Answer)
  | noOutcome

open Classical in
/-- The body of an export, from the caller's current store. There is no fuel.
A witnessed infinite internal run is represented by weak ITree divergence.
A trap is represented by an export reply carrying its final store. The body
uses an empty exception channel. -/
def body (o : GrowOracle) (r : Ready c) (q : Question c) :
    Body.BodyM (sigN 0) (ULift.{1} (Store Nat)) (PEmpty.{2}) (ULift.{1} (Completion q)) :=
  fun s => ExceptT.mk <|
    if h : ∃ p : q.Answer × Store Nat, Finishes o r q s.down p.1 p.2 then
      ITree.ret (.ok (⟨.reply h.choose.1⟩, ⟨h.choose.2⟩))
    else if DivAt (profile o) r.inst c.exports[q.exportIdx] q.args.val s.down then
      ITree.diverge
    else
      ITree.ret (.ok (⟨.noOutcome⟩, s))

/-- One body observation using the existing abstract Wasm observer. Only an
export reply finishes a session round. -/
def Responds (o : GrowOracle) (r : Ready c) (q : Question c) (s : Store Nat)
    (a : (exportSig c).Ar q) (s' : Store Nat) : Prop :=
  ([], .ret ⟨.reply a⟩ ⟨s'⟩) ∈
    BodyTrace.toAFun (fun _ : PUnit.{2} => body o r q) ⟨s⟩ PUnit.unit

/-- Completed rounds of body observations, threading the store after both
returns and traps. The outcome list uses the existing session convention. -/
inductive Runs (o : GrowOracle) (r : Ready c) :
    Store Nat → List (exportSig c).Op → List (Option (List Val)) → Store Nat → Prop
  | nil (s) : Runs o r s [] [] s
  | cons {s s' s'' qs outs} {q : Question c} {a : q.Answer} :
      Responds o r q s a s' → Runs o r s' qs outs s'' →
      Runs o r s (q :: qs) (a.map Subtype.val :: outs) s''

/-- The completed observations of a session from the ready instance. -/
def Completes (o : GrowOracle) (r : Ready c) (qs : List (Question c))
    (outs : List (Option (List Val))) : Prop :=
  ∃ s, Runs o r r.inst.store qs outs s

/-- A session whose completed rounds are followed by a silently diverging
export activation. -/
def Quiet (o : GrowOracle) (r : Ready c) (qs : List (Question c))
    (outs : List (Option (List Val))) (q : Question c) : Prop :=
  ∃ s, Runs o r r.inst.store qs outs s ∧ ((body o r q).run ⟨s⟩).run = ITree.diverge

end Silmaril.Wasm.Component.SyncITree
