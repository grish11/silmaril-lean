module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Recognize.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Decode.Thms

/-! # Ordered two-bit projections on packet-local guarded programs -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ReplyEnumeration ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint Exits exit_type)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestRow requestTypes TypedRoutes)
open PayloadRecognition (Incoming Write guardedControl terminalTagAt)

attribute [local instance] requestTypes

abbrev PayloadType : Syntax.Ty := .product .unit (.product Bit (.product Bit .unit))
abbrev Outputs := Exits PayloadType

/-- The result keeps the old unit followed by these two typed slots in order. -/
def fields {κ V K : Type 1} (first second : V) : K → List (V × Ty κ) :=
  fun _ => [(first, .coprod .unit .unit), (second, .coprod .unit .unit)]

def bitExpr {Γ : List Syntax.Ty} (bit : Bool) : Syntax.Expr Γ Bit :=
  if bit then .inr .unit else .inl .unit

def recordExpr {Γ : List Syntax.Ty} (first second : Syntax.Expr Γ Bit) : Syntax.Expr Γ PayloadType :=
  .pair .unit (.pair first (.pair second .unit))

def outputPacket (i : Tag) (first second : Bool) : Packet Outputs :=
  ⟨i, cast (congrArg Syntax.Payload (exit_type i).symm)
    ((recordExpr (bitExpr first) (bitExpr second)).eval Syntax.emptyBindings)⟩

/-- A read refers to the actual bit block parameter. A write is the same
pure unit-to-bit operation as in the one-field profile. -/
structure Fields (Φ : Type) (hasBit : Bool) where
  first : Write Φ hasBit
  second : Write Φ hasBit

def Fields.Agrees {Φ : Type} {hasBit : Bool} (f : Fields Φ hasBit) (literals : Φ → Option Bool) : Prop :=
  f.first.Agrees literals ∧ f.second.Agrees literals

def fieldExpr {Φ : Type} {hasBit : Bool} :
    Write Φ hasBit → Syntax.Expr [if hasBit then Bit else .unit, Bit] Bit
  | .read => .var 0
  | .literal _ b => bitExpr b

def Fields.output {Φ : Type} {hasBit : Bool} (f : Fields Φ hasBit) :
    Syntax.Expr [if hasBit then Bit else .unit, Bit] PayloadType :=
  recordExpr (fieldExpr f.first) (fieldExpr f.second)

def finishAt {Φ : Type} {d n : Nat} (i : Tag) (first second : Fin n) : Flat Φ (d + 2) n :=
  .br (i.natAdd d) (.pair .unit (.pair (.bv first) (.pair (.bv second) .unit)))

/-- The two slots are assembled after the leading decoder. Literal writes
occur in slot order; retained parameters are shifted past each write. -/
def Fields.rowAt {Φ : Type} {d : Nat} {hasBit : Bool} (f : Fields Φ hasBit) (i : Tag) : Flat Φ (d + 2) 2 :=
  .let₂ (.bv 0) <| match f.first, f.second with
  | .read, .read => finishAt i 1 1
  | .literal op _, .read => .let₁ (.op op .unit) (finishAt i 0 2)
  | .read, .literal op _ => .let₁ (.op op .unit) (finishAt i 2 0)
  | .literal op _, .literal other _ => .let₁ (.op op .unit) (.let₁ (.op other .unit) (finishAt i 1 0))

abbrev finish {Φ : Type} {n : Nat} (i : Tag) (first second : Fin n) : Flat Φ 5 n :=
  finishAt i first second

abbrev Fields.row {Φ : Type} {hasBit : Bool} (f : Fields Φ hasBit) (i : Tag) : Flat Φ 5 2 :=
  f.rowAt i

def readField {Φ : Type} (literals : Φ → Option Bool) (hasBit : Bool) (op : Option Φ) :
    Option {w : Write Φ hasBit // w.Agrees literals} :=
  match op with
  | none =>
    if h : hasBit = true then by
      subst hasBit
      exact some ⟨.read, trivial⟩
    else none
  | some op =>
    match h : literals op with
    | none => none
    | some b => some ⟨.literal op b, h⟩

def terminalShape {Φ : Type} {d : Nat} : Flat Φ (d + 2) 2 → Option (Tag × Option Φ × Option Φ)
  | .let₂ _ (.br label _) => (terminalTagAt label).map fun i => (i, none, none)
  | .let₂ _ (.let₁ (.op first .unit) (.let₁ (.op second .unit) (.br label _))) =>
    (terminalTagAt label).map fun i => (i, some first, some second)
  | .let₂ _ (.let₁ (.op op .unit) (.br label (.pair _ (.pair (.bv first) _)))) =>
    (terminalTagAt label).map fun i => if first = 0 then (i, some op, none) else (i, none, some op)
  | _ => none

def readFields {Φ : Type} {d : Nat} (literals : Φ → Option Bool) (hasBit : Bool) (row : Flat Φ (d + 2) 2) :
    Option (Tag × {f : Fields Φ hasBit // f.Agrees literals}) := do
  let (i, first, second) ← terminalShape row
  let a ← readField literals hasBit first
  let b ← readField literals hasBit second
  return (i, ⟨⟨a.val, b.val⟩, a.property, b.property⟩)

structure Profile (Φ : Type) where
  routes : TypedRoutes Incoming.get
  bitTag : Tag
  atBit : Fields Φ true
  unitTag : Tag
  atUnit : Fields Φ false

def Profile.Agrees {Φ : Type} (p : Profile Φ) (literals : Φ → Option Bool) : Prop :=
  p.atBit.Agrees literals ∧ p.atUnit.Agrees literals

def Profile.expected {Φ : Type} (op : Φ) (p : Profile Φ) : FiniteCFG Φ 3 2 1 :=
  ⟨.br 0 (.pair (.bv 0) .unit), Fin.cases (motive := fun _ : Fin 3 => Flat Φ 5 2)
    (requestRow op p.routes.destination)
    (Fin.cases (motive := fun _ : Fin 2 => Flat Φ 5 2)
      (p.atBit.row p.bitTag) (fun _ => p.atUnit.row p.unitTag))⟩

def readProfile {Φ : Type} (literals : Φ → Option Bool) (table : FiniteCFG Φ 3 2 1) :
    Option {p : Profile Φ // p.Agrees literals} := do
  let routes ← Recognize.readTypedRoutes Incoming.get (table.block 0)
  let (bitTag, atBit) ← readFields literals true (table.block 1)
  let (unitTag, atUnit) ← readFields literals false (table.block 2)
  return ⟨⟨routes, bitTag, atBit.val, unitTag, atUnit.val⟩, atBit.property, atUnit.property⟩

abbrev Profile.endpoint {Φ : Type} (p : Profile Φ) (op : Φ) (selected : Tag → Bool) :
    Endpoint (Recognize.signature Φ) Incoming PayloadType where
  control := guardedControl p.routes op p.bitTag p.unitTag selected
  output := Fin.cases (motive := fun i : Fin 3 => Syntax.Expr [Incoming.get i, Bit] PayloadType)
    (recordExpr (bitExpr false) (bitExpr false))
    (Fin.cases (motive := fun i : Fin 2 => Syntax.Expr [Incoming.get i.succ, Bit] PayloadType)
      p.atBit.output (Fin.cases p.atUnit.output (fun i => Fin.elim0 i)))

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed first second : V} {names : Fin 5 ≃ K}
  {source target : CFG V K P.Instr}

structure Checked (a : Admission P (interface seed names) (fields first second) source) (op : P.Instr)
    (literals : P.Instr → Option Bool) where
  profile : Profile P.Instr
  readback : Recognize.Readback a (profile.expected op)
  literals_agree : profile.Agrees literals

/-- Check the complete reconstruction against the scoped named compiler output. -/
def recognize [DecidableEq P.Instr]
    (a : Admission P (interface seed names) (fields first second) source)
    (op : P.Instr) (literals : P.Instr → Option Bool) : Option (Checked a op literals) :=
  (Recognize.checkReadback a (readProfile literals) (fun p => p.val.expected op)).map
    fun ⟨p, readback⟩ => ⟨p.val, readback, p.property⟩

noncomputable def observeNamed {Φ : Type} {states : Nat}
    (source : CFG V K Φ) (names : Fin 5 ≃ K) (first second : V) (store : V → Value Runtime)
    (literals : Φ → Option Bool) (prim : Syntax.Primitives Φ states) (s : Fin states)
    (selected : Tag → Bool) : LambdaSSA.UB.Overlay.Behaviour 2 Unit (Fin states) :=
  decorate prim selected (FixedCarrier.observe prim
    (LiveOut.observeRaw (LiveBit.rawWithLiterals literals) [names 3, names 4]
      (fun _ => [first, second]) source store) s (constructorDecoder PayloadType)) PayloadType

/-- Unsupported programs or native readbacks give no verdict. Accepted
endpoints use the shared fixed-carrier decision on the complete exit packet. -/
def compare? [DecidableEq P.Instr]
    {a : Admission P (interface seed names) (fields first second) source}
    {b : Admission P (interface seed names) (fields first second) target}
    {op op' : P.Instr} {literals : P.Instr → Option Bool} {states results : Nat}
    (left : Option (Checked a op literals)) (right : Option (Checked b op' literals))
    (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
    (codec : Fin results ≃ Packet Outputs) (caller caller' : Syntax.Payload Bit)
    (replies : ReplyEnumeration (Recognize.signature P.Instr))
    (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states) : Option Bool := do
  let l ← left
  let r ← right
  (l.profile.endpoint op selected).checkAllInterpreters? (r.profile.endpoint op' selected')
    raw raw' codec caller caller' replies configs configs stores

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
