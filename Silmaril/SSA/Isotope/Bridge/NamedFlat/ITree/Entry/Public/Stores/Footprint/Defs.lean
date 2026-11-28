module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {leftCapture rightCapture : V} {leftType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : Seeded signature source exits fields leftCapture leftType outputs)
  (right : Seeded signature target exits fields rightCapture rightType outputs)

/-- Initial register reads of the checked pure entry expression.
The attached internal rows are packet-closed, including their reads of
selected live-outs. -/
def Seeded.initialCaptures : Finset V :=
  left.provenance.seed.fv.image (fun _ => leftCapture)

/-- The executable enumeration uses the admitted literal-read or closed
structural seed fragment. -/
abbrev Seeded.LiteralOrClosed : Prop :=
  left.provenance.seed = .var (0 : Fin 1) ∨ left.provenance.seed.fv = ∅

/-- Install the candidate value for a register read at entry. -/
def Seeded.installCapture (packet : Denote leftType) (initial : V → Value Atom) : V → Value Atom :=
  if leftCapture ∈ left.initialCaptures then
    upd initial leftCapture (PacketType.encode leftType packet)
  else initial

/-- Enumerate the existing typed packets and retain only pairs realized by
one shared store. In particular, two reads of an aliased capture must
agree on its value. Registers outside the footprint are filled with unit. -/
def Seeded.footprintStores : List (V → Value Atom) :=
  (leftType.enumerate.product rightType.enumerate).filterMap fun (leftPacket, rightPacket) =>
    let initial := right.installCapture rightPacket (left.installCapture leftPacket (fun _ => .unit))
    if left.checkSeed initial leftPacket && right.checkSeed initial rightPacket then some initial else none

/-- Compare all well-typed initial stores for the literal-or-closed seed
fragment by enumerating representatives of the exact capture footprint. -/
def Seeded.refinementOverCaptures? [DecidableEq F] : Option Bool :=
  if left.LiteralOrClosed ∧ right.LiteralOrClosed then
    let stores := left.footprintStores right
    left.refinementOverStores? right (fun i : Fin stores.length => stores[i.val])
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
