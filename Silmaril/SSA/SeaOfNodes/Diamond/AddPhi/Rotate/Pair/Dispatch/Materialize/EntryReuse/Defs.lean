module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs

/-! Reuse a shared entry add at the inner add of a right-materialized diamond. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse

open Pure.SubZero (model word wordPort)
open GVN (Key Producer keepOrigin)
open GVN.Elimination (Routing dropNewest routeSuffix)
open RVSDG (Address Origin Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- This reference belongs to the common table that executes before either arm. -/
abbrev EntryAdd (p : Program inputs sigs [word]) := Producer p.diamond.shared word

abbrev SharedWord (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) :=
  Origin (dataPorts inputs) (extend [] sigs) wordPort

def addKey {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    (lhs rhs : Origin args past wordPort) : Key Pure.SubZero.Opcode args past word :=
  ⟨[word, word], .add, .cons lhs (.cons rhs .nil)⟩

def addOperands? {args : List (Ty Unit)} {past : List (List (Ty Unit))} :
    (key : Key Pure.SubZero.Opcode args past word) →
      Option {pair : Origin args past wordPort × Origin args past wordPort //
        key = addKey pair.1 pair.2}
  | ⟨_, .add, .cons lhs (.cons rhs .nil)⟩ => some ⟨(lhs, rhs), rfl⟩
  | _ => none

/-- Test the shared wire in the actual scope of the selected occurrence. -/
def forwards (p : Program inputs sigs [word]) (rhs : SharedWord inputs sigs) (slot : Slot) : Bool :=
  let arm := p.diamond.arms slot
  decide ((arm.outputs.get .head).address = (keepOrigin arm.dataflow rhs).address)

/-- Match an ordered add against the capture and one actual Phi use. -/
def matchesAt (p : Program inputs sigs [word]) (lhs rhs : SharedWord inputs sigs)
    (slot : Slot) : Bool :=
  decide (lhs.address = (Origin.arg p.residual : SharedWord inputs sigs).address) &&
    forwards p rhs slot

/-- The existing typed producer key must name the capture first and the
same exact shared word that both original Phi occurrences forward second. -/
def check (p : Program inputs sigs [word]) (rep : EntryAdd p) : Bool :=
  match addOperands? rep.key with
  | none => false
  | some ⟨(lhs, rhs), _⟩ =>
    matchesAt p lhs rhs .first && forwards p rhs .second

/-- Numbered nominations resolve only inside the common entry table. -/
def findEntry? (p : Program inputs sigs [word]) (address : Address) : Option (EntryAdd p) :=
  (Pure.RightIdentityPass.wordProducers p.diamond.shared).find? fun rep =>
    decide (rep.origin.address = address)

abbrev Suffix := Pure.Program Pure.SubZero.Opcode [word, word] word
abbrev OldArgs := dataPorts [word, word]
abbrev NewArgs := dataPorts [word, word, word]
abbrev Row := [wordPort]

/-- Check the actual emitted suffix's opcodes, ordered wires and return. -/
def rightValue? : (p : Suffix) → Option {value : BitVec 64 // p = suffix .right value}
  | ⟨.cons (.literal value) .nil
      (.cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .add (.cons (.output ⟨1, _⟩ .head) (.cons (.output ⟨0, _⟩ .head) .nil)) .nil)),
      .output ⟨2, _⟩ .head⟩ => some ⟨value, rfl⟩
  | _ => none

/-- Insert the representative after the old capture, keeping the old Phi. -/
def liftArgs : Routing OldArgs [] [] NewArgs
  | _, .arg .head => .arg .head
  | _, .arg (.tail port) => .arg (.tail (.tail port))
  | _, .output i _ => i.elim0

def routeInner : Routing OldArgs [Row, Row] [Row] NewArgs :=
  fun wire => dropNewest (.arg (.tail .head)) (Routing.push (Routing.push liftArgs Row) Row wire)

def outer : Dataflow Pure.SubZero.Opcode OldArgs [Row, Row] [Row] :=
  .cons .add (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)) .nil

/-- Keep the actual outer operation and route its ordered operands. -/
def route : Routing OldArgs [Row, Row, Row] [Row, Row] NewArgs :=
  (routeSuffix outer routeInner).2

def shortened (value : BitVec 64) : Pure.Program Pure.SubZero.Opcode [word, word, word] word where
  dataflow := .cons (.literal value) .nil (routeSuffix outer routeInner).1
  result := route (.output (2 : Fin 3) .head)

/-- Forward the shared representative on both edges. Every original
arm binding and its old output wire remain in the same occurrence. -/
def capture (p : Program inputs sigs [word]) (rep : EntryAdd p) :
    Arms.Graph Pure.SubZero.Opcode inputs sigs [word, word] where
  shared := p.diamond.shared
  predicate := p.diamond.predicate
  merge := p.diamond.merge
  arms := fun slot =>
    let arm := p.diamond.arms slot
    ⟨arm.sigs, arm.dataflow, .cons (keepOrigin arm.dataflow rep.origin) arm.outputs⟩

def emit (p : Program inputs sigs [word]) (rep : EntryAdd p) (value : BitVec 64) :
    Program inputs sigs [word, word] :=
  ⟨p.residual, capture p rep, shortened value⟩

/-- The actual arguments at this predecessor occurrence. -/
def slotArgs {joined : List (ValueSort Unit)} (p : Program inputs sigs joined)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    Tuple (Val model.value) (dataPorts (word :: joined)) :=
  .cons (entry.get p.residual)
    ((p.diamond.arms slot).eval model entry (p.diamond.shared.eval model entry PUnit.unit))

/-- A representative has the old inner sum's value at each occurrence,
for every typed entry. This is the semantic premise used by the shared emitter. -/
def RepresentativeAgrees (p : Program inputs sigs [word]) (rep : EntryAdd p) : Prop :=
  ∀ (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot),
    let shared := p.diamond.shared.eval model entry PUnit.unit
    read model rep.origin entry shared =
      BitVec.add (entry.get p.residual) (((p.diamond.arms slot).eval model entry shared).get .head)

def rewrite? (p : Program inputs sigs [word]) (rep : EntryAdd p) : Option (Program inputs sigs [word, word]) := do
  let value ← rightValue? p.suffix
  if check p rep then some (emit p rep value.val) else none

def rewriteAt? (p : Program inputs sigs [word]) (address : Address) : Option (Program inputs sigs [word, word]) :=
  (findEntry? p address).bind (rewrite? p)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
