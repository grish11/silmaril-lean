module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms

/-! # Checked packet-local constructor-bit returns -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ReplyEnumeration ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head Table Row)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint Exits exit_type)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestRow requestTypes TypedRoutes)
open LiveBit (PayloadType payloadExpr)

attribute [local instance] requestTypes

abbrev Incoming : List Syntax.Ty := [Bit, Bit, .unit]
abbrev Outputs := Exits PayloadType

/-- A terminal row can assign a literal or observe its unchanged bit parameter. -/
inductive Write (Φ : Type) : Bool → Type
  | read : Write Φ true
  | literal {hasBit : Bool} (op : Φ) (value : Bool) : Write Φ hasBit

def Write.row {Φ : Type} {hasBit : Bool} (tag : Tag) : Write Φ hasBit → Flat Φ 5 2
  | .read => .let₂ (.bv 0) (.br (tag.natAdd 3) (.pair .unit (.pair (.bv 1) .unit)))
  | .literal op _ => Recognize.exitRow (tag.natAdd 3) (some op)

def Write.output {Φ : Type} {hasBit : Bool} :
    Write Φ hasBit → Syntax.Expr [if hasBit then Bit else .unit, Bit] PayloadType
  | .read => .pair .unit (.pair (.var 0) .unit)
  | .literal _ value => payloadExpr value

structure Profile (Φ : Type) where
  routes : TypedRoutes Incoming.get
  bitTag : Tag
  fromBit : Write Φ true
  unitTag : Tag
  fromUnit : Write Φ false

def Profile.expected {Φ : Type} (op : Φ) (p : Profile Φ) : FiniteCFG Φ 3 2 1 :=
  ⟨.br 0 (.pair (.bv 0) .unit), Fin.cases (motive := fun _ : Fin 3 => Flat Φ 5 2)
    (requestRow op p.routes.destination)
    (Fin.cases (motive := fun _ : Fin 2 => Flat Φ 5 2)
      (p.fromBit.row p.bitTag) (fun _ => p.fromUnit.row p.unitTag))⟩

def terminalTagAt {d : Nat} (label : Fin (d + 2)) : Option Tag :=
  if h : d ≤ label.val then some ⟨label.val - d, by omega⟩ else none

abbrev terminalTag (label : Fin 5) : Option Tag := terminalTagAt label

/-- The literal table and its scope are checked before any interpreter comparison. -/
def Write.Agrees {Φ : Type} {b : Bool} (write : Write Φ b) (literals : Φ → Option Bool) : Prop :=
  match write with
  | .read => True
  | .literal op value => literals op = some value

def Profile.Agrees {Φ : Type} (p : Profile Φ) (literals : Φ → Option Bool) : Prop :=
  p.fromBit.Agrees literals ∧ p.fromUnit.Agrees literals

def readWrite {Φ : Type} (literals : Φ → Option Bool) (hasBit : Bool) :
    Flat Φ 5 2 → Option (Tag × {w : Write Φ hasBit // w.Agrees literals})
  | .let₂ _ (.let₁ (.op op .unit) (.br label _)) => do
    let tag ← terminalTag label
    match h : literals op with
    | none => none
    | some bit => some (tag, ⟨.literal op bit, h⟩)
  | .let₂ _ (.br label _) => by
    cases hasBit
    · exact none
    · exact (terminalTag label).map fun i => (i, ⟨.read, trivial⟩)
  | _ => none

def readProfile {Φ : Type} (literals : Φ → Option Bool) (table : FiniteCFG Φ 3 2 1) :
    Option {p : Profile Φ // p.Agrees literals} := do
  let routes ← Recognize.readTypedRoutes Incoming.get (table.block 0)
  let (bitTag, fromBit) ← readWrite literals true (table.block 1)
  let (unitTag, fromUnit) ← readWrite literals false (table.block 2)
  return ⟨⟨routes, bitTag, fromBit.val, unitTag, fromUnit.val⟩, fromBit.property, fromUnit.property⟩

abbrev guardedControl {Φ : Type} (routes : TypedRoutes Incoming.get) (op : Φ)
    (bitTag unitTag : Tag) (selected : Tag → Bool) : Table (Recognize.signature Φ) Incoming where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row (Recognize.signature Φ) Incoming [Incoming.get i, Bit])
    (.request op (.var 0) routes.destination routes.packet)
    (Fin.cases (motive := fun i : Fin 2 => Row (Recognize.signature Φ) Incoming [Incoming.get i.succ, Bit])
      (.exit bitTag) (fun _ => .exit unitTag))
  selected := selected

abbrev Profile.endpoint {Φ : Type} (p : Profile Φ) (op : Φ) (selected : Tag → Bool) :
    Endpoint (Recognize.signature Φ) Incoming PayloadType where
  control := guardedControl p.routes op p.bitTag p.unitTag selected
  output := Fin.cases (motive := fun i : Fin 3 => Syntax.Expr [Incoming.get i, Bit] PayloadType)
    (payloadExpr false)
    (Fin.cases (motive := fun i : Fin 2 => Syntax.Expr [Incoming.get i.succ, Bit] PayloadType)
      p.fromBit.output (Fin.cases p.fromUnit.output (fun i => Fin.elim0 i)))

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed reg : V} {names : Fin 5 ≃ K}
  {source : CFG V K P.Instr}

structure Checked (a : Admission P (interface seed names) (LiveBit.fields reg) source) (op : P.Instr)
    (literals : P.Instr → Option Bool) where
  profile : Profile P.Instr
  readback : Recognize.Readback a (profile.expected op)
  literals_agree : profile.Agrees literals

/-- Infer routes, terminal tags, and the projected bit expression. Success
checks the reconstruction against all rows of the existing admission. -/
def recognize [DecidableEq P.Instr]
    (a : Admission P (interface seed names) (LiveBit.fields reg) source)
    (op : P.Instr) (literals : P.Instr → Option Bool) : Option (Checked a op literals) :=
  (Recognize.checkReadback a (readProfile literals) (fun p => p.val.expected op)).map
    fun ⟨p, readback⟩ => ⟨p.val, readback, p.property⟩

abbrev Phase (A : Syntax.Ty) := ULift.{1} (Packet (Exits A) ⊕ Packet Incoming)

def packetValue {A : Syntax.Ty} (p : Packet (Exits A)) : Value Runtime := Recognize.encodeValue ULift.up p.2.val

def encodePhase {A : Syntax.Ty} (names : Fin 5 ≃ K) (phase : Phase A) : K × Value Runtime :=
  match phase.down with
  | .inl p => (names (p.1.natAdd 3), packetValue p)
  | .inr p => (names (p.1.castAdd 2), .pair (Recognize.encodeValue ULift.up p.2.val) .unit)

def payloadStep {Φ : Type} {A : Syntax.Ty} (g : Endpoint (Recognize.signature Φ) Incoming A)
    (caller : Syntax.Payload (Incoming.get g.control.entry)) (phase : Phase A) :
    Tree (Request Φ) (Transfer Runtime ⊕ Phase A) :=
  match phase.down with
  | .inl result => pure (.inl (packedReturn result))
  | .inr p =>
    match g.control.head caller p with
    | .exit i _ => pure (.inr ⟨.inl (g.returnPacket caller p i)⟩)
    | .diverge => Silmaril.Elgot.ITree.diverge
    | .request f arg next => query f arg >>= fun r => pure (.inr ⟨.inr (next r.down.1 r.down.2)⟩)

noncomputable def packetTree {Φ : Type} {A : Syntax.Ty} (g : Endpoint (Recognize.signature Φ) Incoming A)
    (caller : Syntax.Payload (Incoming.get g.control.entry)) (p : Packet Incoming) : RunTree Φ :=
  iter (m := Tree (Request Φ)) (payloadStep g caller) ⟨.inr p⟩

/-- A local row yields the numbered original transfer and its checked payload. -/
def rowTransfer {Φ : Type} {A : Syntax.Ty} (g : Endpoint (Recognize.signature Φ) Incoming A)
    (caller : Syntax.Payload (Incoming.get g.control.entry)) (p : Packet Incoming) :
    Tree (Request Φ) (Transfer Runtime) :=
  match g.control.head caller p with
  | .exit i _ => pure ((i.natAdd 3).val, packetValue (g.returnPacket caller p i))
  | .diverge => Silmaril.Elgot.ITree.diverge
  | .request f arg next => query f arg >>= fun r =>
    let q := next r.down.1 r.down.2
    pure (q.1.val, .pair (Recognize.encodeValue ULift.up q.2.val) .unit)

def outputPacket (tag : Tag) (bit : Bool) : Packet Outputs :=
  ⟨tag, cast (congrArg Syntax.Payload (exit_type tag).symm)
    ((payloadExpr bit).eval Syntax.emptyBindings)⟩


/-- Run the existing fixed-carrier comparison once both named recognizers and
both exact native readbacks accept. `none` denotes failed admission or readback. -/
def compare? [DecidableEq P.Instr] {target : CFG V K P.Instr}
    {a : Admission P (interface seed names) (LiveBit.fields reg) source}
    {b : Admission P (interface seed names) (LiveBit.fields reg) target}
    {op op' : P.Instr} {literals : P.Instr → Option Bool} {states results : Nat}
    (left : Option (Checked a op literals)) (right : Option (Checked b op' literals))
    (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
    (codec : Fin results ≃ Packet Outputs) (caller caller' : Syntax.Payload Bit)
    (replies : ReplyEnumeration (Recognize.signature P.Instr))
    (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states) : Option Bool := do
  let l ← left
  let r ← right
  let g := l.profile.endpoint op selected
  let h := r.profile.endpoint op' selected'
  g.checkAllInterpreters? h raw raw' codec caller caller' replies configs configs stores

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition
