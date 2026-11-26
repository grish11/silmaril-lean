module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.ABI.Thms
public import Silmaril.Wasm.Abstract.BodyTrace.Defs

/-! # Interaction trees for ready, nonreentrant synchronous components

This is the open flat-ABI `Reference.SimpleI` fragment at a deterministic
Core profile. An activation has one Core cursor. At a canonical import
callout, the tree exposes the component question and retains that cursor
in its continuation. The host may supply a typed result or report a trap.
While it waits, the tree has a visible event. The host cannot call back
into the component through this continuation.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Component.SyncImportITree

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game Silmaril.Elgot
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle Thread profile resumeResult ofFlat toFlat?)

/-- A ready instance of the start-free, flat, float-free importer fragment. -/
structure Ready (c : SimpleI) where
  good : c.Good
  arity : c.Arity
  floatFree : c.FloatFree
  inst : ScalarInstance
  isInst : c.mod.IsInst inst

/-- Component values checked against the list of interface types. -/
abbrev Values (ts : List ValTy) := {vs : List Val // ValTy.checkList ts vs = true}

/-- A call of a particular function with its checked arguments. The same
definition serves the import and export interfaces. -/
structure Question (fs : Iface) where
  index : Fin fs.length
  args : Values fs[index].2.params

/-- `none` signals a trap. Ordinary replies must match this function's result types. -/
abbrev Question.Answer {fs : Iface} (q : Question fs) := Option (Values fs[q.index].2.results)

/-- A component interface with dependent answer types. -/
def signature (fs : Iface) : Sig.{0} := ⟨Question fs, Question.Answer⟩

/-- The interface used by the lifted exports, in component order. -/
def exportIface (c : SimpleI) : Iface := c.exports.map fun e => (e.name, e.ty)

abbrev Cursor := Store Nat × Thread

variable {c : SimpleI}

/-- The canonical lift's export entry in the scalar Core game. -/
def entry (r : Ready c) (q : Question (exportIface c)) : Option r.inst.F.Op :=
  let i : Fin c.exports.length := Fin.cast (by simp [exportIface]) q.index
  let e := c.exports[i]
  ifaceOp? r.inst.exports e.core ((lowerArgs (exportIface c)[q.index].2.params q.args.val).map ofFlat)

/-- The next Core game move, retaining the paused activation or the final store. -/
inductive Cut (I : ScalarInstance) (f : I.F.Op) where
  | request (e : I.E.Op) (paused : Cursor)
  | reply (a : I.F.Ar f) (store : Store Nat)

/-- The existing Core game transition supplies the cut. -/
def ReachesCut (o : GrowOracle) (I : ScalarInstance) (f : I.F.Op) (x : Cursor) :
    Cut I f → Prop
  | .request e p => I.Trans (profile o) (.running f x.1 x.2) (.inl (.ask e))
      (.waiting f p.1 p.2 e)
  | .reply a s => I.Trans (profile o) (.running f x.1 x.2) (.inr (.ans f a)) (.idle s)

/-- A witnessed infinite host-free Core run from the current activation. -/
def Silent (o : GrowOracle) (x : Cursor) : Prop :=
  Silmaril.InfiniteTrace (InternalP (profile o)) x

/-- The observation at the next component boundary. An unavailable Core move
or missing interface entry has no legal observation. -/
inductive Front (c : SimpleI) (q : Question (exportIface c)) where
  | request (m : Question c.imports) (resume : m.Answer → Cursor)
  | reply (a : q.Answer) (store : Store Nat)
  | quiet
  | unavailable

/-- Lift all flat values and retain the type-check certificate. -/
def liftValues (ts : List ValTy) (xs : List Flat) : Option (Values ts) :=
  (liftArgs ts xs).pmap Subtype.mk fun _ h => checkList_of_liftArgs h

/-- Read one Core game move at the component ABI. A failed argument lift
traps at the cut, before the host is called. A failed result lift, Core trap
or uncaught Core exception also reports a component trap. -/
def cutFront (r : Ready c) (q : Question (exportIface c)) {f : r.inst.F.Op} :
    Cut r.inst f → Front c q
  | .reply a s =>
    .reply ((answerPayload a).bind fun
      | .flat ys => liftValues (exportIface c)[q.index].2.results ys
      | .vals _ => none) s
  | .request e p =>
    if hi : e.1.val < c.imports.length then
      let i : Fin c.imports.length := ⟨e.1.val, hi⟩
      let lifted : Option (Values c.imports[i].2.params) :=
        liftValues c.imports[i].2.params (e.2.val.filterMap toFlat?)
      match lifted with
      | none => .reply none p.1
      | some args =>
        let m : Question c.imports := ⟨i, args⟩
        .request m fun a =>
          let payload := (a.map (fun vs => Payload.vals (Subtype.val vs))).bind (Adapter.lower c.imports[i].2).up
          let core := payloadAnswer (r.inst.imports.get e.1) payload
          (p.1, resumeResult p.1 p.2 core.toResult)
    else .unavailable

/-- The next component front justified by a Core move or infinite host-free run. -/
def ReachesFront (o : GrowOracle) (r : Ready c) (q : Question (exportIface c))
    (f : r.inst.F.Op) (x : Cursor) (front : Front c q) : Prop :=
  (∃ cut, ReachesCut o r.inst f x cut ∧ cutFront r q cut = front) ∨
    (Silent o x ∧ front = .quiet)

open Classical in
/-- Select the next boundary of a deterministic Core activation. This
selection uses only the next Core game move, even for a nonterminating
activation that keeps making imports. -/
def head (o : GrowOracle) (r : Ready c) (q : Question (exportIface c))
    (f : r.inst.F.Op) (x : Cursor) : Front c q :=
  if h : ∃ cut, ReachesCut o r.inst f x cut then cutFront r q h.choose
  else if Silent o x then .quiet else .unavailable

/-- `reply none` is a trap and retains the reached Core store. -/
inductive Completion {fs : Iface} (q : Question fs) where
  | reply (answer : q.Answer)
  | noOutcome

abbrev BodyResult {fs : Iface} (q : Question fs) :=
  Except PEmpty.{2} (ULift.{1} (Completion q) × ULift.{1} (Store Nat))

/-- A guarded iteration step. The recursive state is passed only after the
typed answer has resumed the suspended Core cursor. -/
def unfoldStep (o : GrowOracle) (r : Ready c) (q : Question (exportIface c)) (f : r.inst.F.Op)
    (x : ULift.{1} Cursor) :
    ITree.Tree (Body.SigEv (signature c.imports)) (BodyResult q ⊕ ULift.{1} Cursor) :=
  match head o r q f x.down with
  | .request m resume => ITree.vis (R := m.Answer) ⟨m, rfl⟩
      fun a => pure (.inr ⟨resume a⟩)
  | .reply a s => pure (.inl (.ok (⟨.reply a⟩, ⟨s⟩)))
  | .quiet => ITree.diverge
  | .unavailable => pure (.inl (.ok (⟨.noOutcome⟩, ⟨x.down.1⟩)))

/-- The residual body at a Core cursor, including one resumed after an import. -/
def tree (o : GrowOracle) (r : Ready c) (q : Question (exportIface c))
    (f : r.inst.F.Op) (x : Cursor) : ITree.Tree (Body.SigEv (signature c.imports)) (BodyResult q) :=
  Silmaril.Elgot.iter (unfoldStep o r q f) ⟨x⟩

/-- Run the export body from the supplied persistent store. -/
def body (o : GrowOracle) (r : Ready c) (q : Question (exportIface c)) :
    Body.BodyM (signature c.imports) (ULift.{1} (Store Nat)) PEmpty.{2}
      (ULift.{1} (Completion q)) :=
  fun s => ExceptT.mk <| match entry r q with
    | some f => tree o r q f (s.down, r.inst.initThread f)
    | none => ITree.ret (.ok (⟨.noOutcome⟩, s))

/-- What a finite sequence of answered imports ends at. -/
inductive Observation {c : SimpleI} (q : Question (exportIface c)) where
  | reply (a : q.Answer) (store : Store Nat)
  | pending (m : Question c.imports)
  | quiet

/-- The existing finite tree observer, with pending and terminal observations
in one type. A trap is recorded by a reply carrying `none` and the store. -/
def Sees {q : Question (exportIface c)}
    (t : ITree.Tree (Body.SigEv (signature c.imports)) (BodyResult q))
    (cs : List (Call (signature c.imports))) : Observation q → Prop
  | .reply a s => BodyTrace.Path t cs (.val (.ok (⟨.reply a⟩, ⟨s⟩)))
  | .pending m => BodyTrace.Pend t cs m
  | .quiet => BodyTrace.Path t cs .div

/-- A finite Core/ABI observation. Requests are justified at the suspended
cursor, and each answered request continues at its own resumed cursor. -/
inductive Observes (o : GrowOracle) (r : Ready c) (q : Question (exportIface c)) (f : r.inst.F.Op) :
    Cursor → List (Call (signature c.imports)) → Observation q → Prop where
  | reply {x a s} : ReachesFront o r q f x (.reply a s) → Observes o r q f x [] (.reply a s)
  | pending {x m k} : ReachesFront o r q f x (.request m k) → Observes o r q f x [] (.pending m)
  | quiet {x} : Silent o x → Observes o r q f x [] .quiet
  | answer {x m k cs obs} (a : m.Answer) :
      ReachesFront o r q f x (.request m k) → Observes o r q f (k a) cs obs →
      Observes o r q f x (⟨m, a⟩ :: cs) obs

end Silmaril.Wasm.Component.SyncImportITree
