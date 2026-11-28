module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Ranked.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Reachable.Defs

/-! # Named ordered live-outs with checked silent identity self-transfers -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestRow requestTypes TypedRoutes)
open PayloadRecognition (Incoming guardedControl)

attribute [local instance] requestTypes

/-- The leading decoder binds the packet component at index one. -/
def loopRow {Φ : Type} (i : Fin 3) : Flat Φ 5 2 :=
  .let₂ (.bv 0) (.br (i.castAdd 2) (.pair (.bv 1) .unit))

inductive Row (Φ : Type) (hasBit : Bool) where
  | ret (i : Tag) (fields : Fields Φ hasBit)
  | loop

def Row.Agrees {Φ : Type} {hasBit : Bool} (r : Row Φ hasBit) (literals : Φ → Option Bool) : Prop :=
  match r with
  | .ret _ fields => fields.Agrees literals
  | .loop => True

def Row.flat {Φ : Type} {hasBit : Bool} (r : Row Φ hasBit) (i : Fin 3) : Flat Φ 5 2 :=
  match r with
  | .ret tag fields => fields.row tag
  | .loop => loopRow i

def Row.output {Φ : Type} {hasBit : Bool} (r : Row Φ hasBit) :
    Syntax.Expr [if hasBit then Bit else .unit, Bit] PayloadType :=
  match r with
  | .ret _ fields => fields.output
  | .loop => recordExpr (bitExpr false) (bitExpr false)

def Row.control {Φ : Type} {hasBit : Bool} (r : Row Φ hasBit) :
    LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Row
      (Recognize.signature Φ) Incoming [if hasBit then Bit else .unit, Bit] :=
  match r with
  | .ret i _ => .exit i
  | .loop => .diverge

def readRow {Φ : Type} (literals : Φ → Option Bool) (hasBit : Bool) (i : Fin 3) (flat : Flat Φ 5 2) :
    Option {r : Row Φ hasBit // r.Agrees literals} :=
  match flat with
  | .let₂ (.bv _) (.br target (.pair (.bv _) .unit)) =>
    if target = i.castAdd 2 then some ⟨.loop, trivial⟩ else none
  | _ => (readFields literals hasBit flat).map fun (tag, fields) =>
    ⟨.ret tag fields.val, fields.property⟩

structure Profile (Φ : Type) where
  routes : TypedRoutes Incoming.get
  bit : Row Φ true
  unit : Row Φ false

def Profile.Agrees {Φ : Type} (p : Profile Φ) (literals : Φ → Option Bool) : Prop :=
  p.bit.Agrees literals ∧ p.unit.Agrees literals

def Profile.expected {Φ : Type} (op : Φ) (p : Profile Φ) : FiniteCFG Φ 3 2 1 :=
  ⟨.br 0 (.pair (.bv 0) .unit), Fin.cases (motive := fun _ : Fin 3 => Flat Φ 5 2)
    (requestRow op p.routes.destination)
    (Fin.cases (motive := fun _ : Fin 2 => Flat Φ 5 2)
      (p.bit.flat 1) (fun _ => p.unit.flat 2))⟩

def readProfile {Φ : Type} (literals : Φ → Option Bool) (table : FiniteCFG Φ 3 2 1) :
    Option {p : Profile Φ // p.Agrees literals} := do
  let routes ← Recognize.readTypedRoutes Incoming.get (table.block 0)
  let bit ← readRow literals true 1 (table.block 1)
  let unit ← readRow literals false 2 (table.block 2)
  return ⟨⟨routes, bit.val, unit.val⟩, bit.property, unit.property⟩

abbrev Profile.endpoint {Φ : Type} (p : Profile Φ) (op : Φ) (selected : Tag → Bool) :
    Endpoint (Recognize.signature Φ) Incoming PayloadType where
  control := { guardedControl p.routes op 0 1 selected with
    row := Fin.cases (motive := fun i : Fin 3 =>
      LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Row
        (Recognize.signature Φ) Incoming [Incoming.get i, Bit]) ((guardedControl p.routes op 0 1 selected).row 0)
      (Fin.cases p.bit.control (Fin.cases p.unit.control (fun i => Fin.elim0 i))) }
  output := Fin.cases (motive := fun i : Fin 3 => Syntax.Expr [Incoming.get i, Bit] PayloadType)
    (recordExpr (bitExpr false) (bitExpr false))
    (Fin.cases (motive := fun i : Fin 2 => Syntax.Expr [Incoming.get i.succ, Bit] PayloadType)
      p.bit.output (Fin.cases p.unit.output (fun i => Fin.elim0 i)))

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed first second : V} {names : Fin 5 ≃ K}
  {source target : CFG V K P.Instr}

structure Checked (a : Admission P (interface seed names) (fields first second) source) (op : P.Instr)
    (literals : P.Instr → Option Bool) where
  profile : Profile P.Instr
  readback : Recognize.Readback a (profile.expected op)
  literals_agree : profile.Agrees literals

/-- The inferred silent row is accepted only if the actual named versioned
readback has the exact label, decoder, and carried variable. -/
def recognize [DecidableEq P.Instr]
    (a : Admission P (interface seed names) (fields first second) source)
    (op : P.Instr) (literals : P.Instr → Option Bool) : Option (Checked a op literals) :=
  (Recognize.checkReadback a (readProfile literals) (fun p => p.val.expected op)).map
    fun ⟨p, readback⟩ => ⟨p.val, readback, p.property⟩

/-- Compare the represented constructor of the shared caller with the
actual seed in the named store. -/
def matchesCaller (caller : Syntax.Payload Bit) (value : Value Runtime) : Bool :=
  match caller.val, value with
  | .inl .unit, .inl .unit | .inr .unit, .inr .unit => true
  | _, _ => false

open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed)

/-- Compare at the reachable product cutoff after checking the named
recognizers, both caller bindings, and the original native readbacks. -/
def compare? [DecidableEq P.Instr]
    {a : Admission P (interface seed names) (fields first second) source}
    {b : Admission P (interface seed names) (fields first second) target}
    {op op' : P.Instr} {literals : P.Instr → Option Bool}
    (left : Option (Checked a op literals)) (right : Option (Checked b op' literals))
    (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
    (caller : Syntax.Payload Bit) (store store' : V → Value Runtime) : Option Bool := do
  let l ← left
  let r ← right
  if matchesCaller caller (store seed) && matchesCaller caller (store' seed) then
    (l.profile.endpoint op selected).checkReachable? (r.profile.endpoint op' selected')
      raw raw' outputCodes caller caller replyPackets configurations configurations
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent
