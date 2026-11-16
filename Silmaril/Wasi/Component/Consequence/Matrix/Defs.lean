module

public import Silmaril.Wasi.Component.Consequence.Thms
public import Silmaril.Wasi.Component.Consequence.Checkers.Thms
public import Silmaril.Wasi.Component.Consequence.Stateful.Thms

/-! # The interpretation matrix of the consequence protocols

A **regular** matrix: one cell for every protocol, state policy and observation boundary
(`cell p s b`, `cells`), each either supported — with the reading, the theorems that carry its
evidence (checked Lean names: the double-backtick syntax fails on a missing declaration) and
what that evidence rests on — or unsupported with the reason. One-shot protocols have no
state; stateful ones have no `oneShot` cell. Export queries are always observed at their
return, so for protocol 1 the boundary is irrelevant and both boundary cells are the same.

What the evidence rests on (`Evidence`):

* `definitions`: the reading is defined for **every** component (any trace set); the theorems
  are general laws (status classification, epochs, transport under structural closure of the
  target). No component is shown to have any property.
* `specStrategy`: in addition, specification strategies defined in Lean
  (`Silmaril.Wasi.Component.Consequence.Checkers.Defs`) have exact theorems. They are not
  compiled components and no compiled binary or core module is claimed.

Gaps (`gaps`): no compiled component binary, no component over a core module (the empty and the
byte-membership checkers exist as verified core modules, `Silmaril.Wasm.Examples.EmptyCheck` and
`Silmaril.Wasm.Examples.MemberCheck`, unwrapped), a
specification strategy only for protocol 2 (list policy, call boundary), and divergence is the
absence of an answer, not an answer.

This is metadata, independent of any serialization; the project registry may publish it.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence.Matrix

open Lean (Name)

/-- The four protocols. -/
inductive Protocol where
  /-- Exported `check(ax, stmt) -> bool`. -/
  | exportCheck
  /-- Exported `axiom(v)` / `check(stmt) -> bool`, optional `reset()`. -/
  | exportStateful
  /-- Imported `assert(ax, stmt)`. -/
  | importAssert
  /-- Imported `assume(v)` / `assert(stmt)`, optional `reset()`. -/
  | importStateful
  deriving DecidableEq, Repr

/-- The state of the assumptions. -/
inductive StateShape where
  /-- No state: the assumptions are an argument. -/
  | oneShot
  /-- `Policy.list`. -/
  | list
  /-- `Policy.finset`. -/
  | finset
  /-- `Policy.count`. -/
  | count
  /-- `Policy.named` (last write wins). -/
  | named
  /-- `Policy.namedFirst` (first write wins). -/
  | namedFirst
  deriving DecidableEq, Repr

/-- What the evidence of a supported cell rests on. -/
inductive Evidence where
  /-- The reading for every component, with general laws. -/
  | definitions
  /-- Also exact theorems for specification strategies (no compiled component). -/
  | specStrategy
  deriving DecidableEq, Repr

/-- The support of a cell. -/
inductive Support where
  | supported (reading : Name) (policy : Option Name) (theorems : List Name) (evidence : Evidence)
  | unsupported (reason : String)
  deriving Repr

/-- One cell. -/
structure Cell where
  protocol : Protocol
  state : StateShape
  boundary : Boundary
  support : Support
  deriving Repr

def Protocol.all : List Protocol := [.exportCheck, .exportStateful, .importAssert, .importStateful]
def StateShape.all : List StateShape := [.oneShot, .list, .finset, .count, .named, .namedFirst]
def Boundary.all : List Boundary := [.call, .answer]

/-- A protocol is stateful. -/
def Protocol.stateful : Protocol → Bool
  | .exportStateful | .importStateful => true
  | _ => false

/-- The policy of a state shape. -/
def StateShape.policy : StateShape → Option Name
  | .oneShot => none
  | .list => some ``Policy.list
  | .finset => some ``Policy.finset
  | .count => some ``Policy.count
  | .named => some ``Policy.named
  | .namedFirst => some ``Policy.namedFirst

/-- The general laws of every reading. -/
def generalLaws : List Name :=
  [``nonempty_acceptWitness_iff, ``accepted_iff_sat, ``classify_holds, ``accepted_iff_classify,
    ``execProblem_cax_iff, ``execProblem_thm_iff, ``execProblem_csa_iff, ``thm_of_cax,
    ``accepted_of_thm, ``accepted_mono, ``existsHost_accepted, ``forallHosts_existsHost]

/-- The laws of the stateful readings for a state shape. -/
def stateLaws : StateShape → List Name
  | .oneShot => []
  | .list => [``epochState_append_reset, ``sound_perm_closure]
  | .finset => [``epochState_append_reset, ``Policy.listToFinset, ``accepted_stateful_hom,
      ``finset_sound_of_mem_closed]
  | .count => [``epochState_append_reset, ``Policy.listToCount, ``accepted_stateful_hom,
      ``sound_hom]
  | .named => [``epochState_append_reset, ``Policy.listToNamed, ``accepted_stateful_hom,
      ``sound_hom]
  | .namedFirst => [``epochState_append_reset]

/-- **The matrix.** -/
def cell (p : Protocol) (s : StateShape) (b : Boundary) : Cell :=
  ⟨p, s, b, match p, s with
  | .exportCheck, .oneShot => .supported ``exportCheck none (generalLaws ++
      [``accepted_memberU32, ``status_memberU32, ``status_emptyU32, ``status_silentChecker,
        ``thm_silentChecker, ``memberChecker_sound, ``memberChecker_complete]) .specStrategy
  | .importAssert, .oneShot => .supported ``importAssert none
      (generalLaws ++ match b with
        | .call => [``importAssert_call_thm]
        | .answer => []) .definitions
  | .exportStateful, .oneShot | .importStateful, .oneShot =>
      .unsupported "A stateful protocol accumulates its assumptions; it has no one-shot reading."
  | .exportCheck, _ | .importAssert, _ =>
      .unsupported "A one-shot protocol takes its assumptions as an argument; it has no state."
  | .exportStateful, .list => match b with
      | .call => .supported ``exportStateful (some ``Policy.list) (generalLaws ++ stateLaws .list ++
          [``accepted_statefulMember, ``status_statefulMember, ``accepted_statefulMemberU32])
          .specStrategy
      | .answer => .supported ``exportStateful (some ``Policy.list) (generalLaws ++ stateLaws .list)
          .definitions
  | .exportStateful, s => .supported ``exportStateful s.policy (generalLaws ++ stateLaws s)
      .definitions
  | .importStateful, s => .supported ``importStateful s.policy (generalLaws ++ stateLaws s)
      .definitions⟩

/-- Every cell, in order. -/
def cells : List Cell :=
  Protocol.all.flatMap fun p => StateShape.all.flatMap fun s => Boundary.all.map (cell p s)

/-- Whether a cell is supported. -/
def Cell.supported (c : Cell) : Bool :=
  match c.support with
  | .supported .. => true
  | .unsupported _ => false

/-- **Gaps**: what no cell provides. -/
def gaps : List (String × String) := [
  ("compiled component",
    "No compiled component binary implements any protocol: the catalog's `compiledComponent` " ++
    "shape is unsupported, and the checkers here are specification strategies."),
  ("core module",
    "Two verified core modules: the empty checker (`Silmaril.Wasm.Examples.EmptyCheck`) and " ++
    "the byte-membership checker (`Silmaril.Wasm.Examples.MemberCheck`, exact acceptance of " ++
    "`c :: as` with `c ∈ as`). No component wraps them: the canonical-ABI correspondence to " ++
    "`exportCheck` is not established."),
  ("stateful specification component",
    "Only protocol 2 with the list policy at the call boundary has a specification strategy " ++
    "(`statefulMember`); the other stateful cells have general laws only."),
  ("divergence",
    "Finite plays: a call that never returns has no answer event. Divergence is not an answer; " ++
    "infinite plays are not used."),
  ("structural rules",
    "No reading assumes weakening, exchange, contraction or cut; transport between policies " ++
    "takes closure of the target as a hypothesis.")]

end Silmaril.Wasi.Consequence.Matrix
