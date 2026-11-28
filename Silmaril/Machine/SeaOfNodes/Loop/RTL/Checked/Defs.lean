module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! # Checked admission of a native one-word loop -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp inputs word)
open Silmaril.Machine.RTL.SSA (Prog)
open Silmaril.Machine.Lir (Word)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow ValueSort)
open Silmaril.SSA.SeaOfNodes.Loop (Graph headerPorts)
open Silmaril.SSA.RVSDG (Address Wires)

abbrev Header (past sigs : List (List PortTy)) :=
  Dataflow WordOp (headerPorts inputs [word]) past sigs

def decodeUpdate {ins : List (ValueSort Unit)} : WordOp ins word → Option Update
  | .add => some .add
  | .sub => some .sub
  | .const _ => none

def decodeLimit {ins : List (ValueSort Unit)} : WordOp ins word → Option Word
  | .const limit => some limit
  | .add | .sub => none

def decodeGuard {ins : List (ValueSort Unit)} : WordOp ins .predicate → Guard
  | .eq => .eq
  | .ne => .ne
  | .slt => .slt

/-- Recover the candidate operation schedule. Admission also checks every
operand provenance against the candidate's canonical graph. -/
def decodeSchedule {args : List PortTy} : Dataflow WordOp args [] headerSigs → Option Profile
  | .cons update _ (.cons limit _ (.cons guard _ .nil)) =>
    match decodeUpdate update, decodeLimit limit with
    | some arithmetic, some value => some ⟨arithmetic, value, decodeGuard guard⟩
    | _, _ => none

/-- The admitted three producers with caller-supplied typed operand wires. -/
def schedule (p : Profile) {args : List PortTy}
    (update : Wires args [] [.value word, .value word])
    (guard : Wires args [[.value word], [.value word]] [.value word, .value word]) :
    Dataflow WordOp args [] headerSigs :=
  .cons p.update.source update (.cons (.const p.limit) .nil (.cons p.guard.source guard .nil))

def scheduleAddresses {args : List PortTy} {past sigs : List (List PortTy)} :
    Dataflow WordOp args past sigs → List (List Address)
  | .nil => []
  | .cons _ operands rest => operands.addresses :: scheduleAddresses rest

/-- Address comparisons take place in their original typed scope.
Entry and feedback addresses have distinct fields. -/
structure Provenance where
  producers : List (List Address)
  entry : List Address
  feedback : List Address
  predicate : Address
  result : Address
  deriving DecidableEq

def provenance {input carried : List (ValueSort Unit)}
    (g : Graph WordOp input carried [] headerSigs word) : Provenance :=
  ⟨scheduleAddresses g.header, (g.phiInputs .entry).addresses, (g.phiInputs .backedge).addresses,
    g.predicate.address, g.result.address⟩

/-- Check the native graph and recover its profile. Merely having the right
signatures does not establish that a guard or feedback operand is supported. -/
def recognize (g : WordLoop) : Option Profile :=
  match decodeSchedule g.header with
  | none => none
  | some p => if provenance g = provenance p.graph then some p else none

/-- Emit actual machine RTL only after checking operations and provenance. -/
def lower (g : WordLoop) : Option (Prog Reg) := (recognize g).map Profile.lower

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked
