module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- Records and tuples align from the current cursor. Arrays advance at the
validated element stride; the canonical array body does not read the width
to place the next element. Indirect maps use a separate per-entry rule. -/
inductive Track where
  | fields
  | elements (stride : Nat)

def Track.slot (mode : Track) (width : AddrType) (item : Field) (cursor : Nat) : Nat × Nat :=
  match mode with
  | .fields =>
    let area := layout width item.type
    let start := alignTo cursor area.alignment
    (start, start + area.size)
  | .elements stride => (cursor, cursor + stride)

def Track.checked (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field)
    (index cursor : Nat) : Session grow sig (Except RecordLower.Issue Unit) :=
  match mode with
  | .fields => Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
      items cursor index
  | .elements stride => Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
      items stride cursor index

def Track.canonical (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field)
    (cursor : Nat) : Session grow sig Unit :=
  match mode with
  | .fields => CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width items cursor
  | .elements stride => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width items .value stride cursor

def Track.readLabels : Track → List (Label (core3 grow) (HostState sig))
  | .fields => [.tau]
  | .elements _ => []

abbrev CheckNext (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))

abbrev CanonNext (grow : SingleThreaded.GrowOracle) (sig : Signature) := Unit → Session grow sig (Ret (core3 grow))

abbrev Finish (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop

abbrev FieldComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Field → Nat → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
    Cursor (E := core3 grow) (HostState sig) → CheckNext grow sig → CanonNext grow sig → Finish grow sig → Prop

def FieldRule (compare : FieldComparison grow sig) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId) (item : Field) (address : Nat) : Prop :=
  ∀ index (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) left right check canon,
    ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width item index (.memory address) >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item (.memory address) >>= canonNext) →
    ∀ finish : Finish grow sig, (∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon) →
    compare item index address left right check canon checkNext canonNext finish

def Track.Slots (mode : Track) (width : AddrType) (rule : Field → Nat → Prop) : List Field → Nat → Prop
  | [], _ => True
  | item :: rest, cursor =>
    let (address, next) := mode.slot width item cursor
    rule item address ∧ mode.Slots width rule rest next

/-- A placed child interval, independent of the contents of guest memory. -/
def SlotFits (width : AddrType) (bytes : Nat) (item : Field) (address : Nat) : Prop :=
  address % (layout width item.type).alignment.bytes = 0 ∧ address + (layout width item.type).size ≤ bytes

/-- The checked aggregate guard wraps a child's typed error at the
enclosing field index, and does not turn a canonical trap into a result. -/
def aggregateNext (index : Nat) (next : CheckNext grow sig) : CheckNext grow sig :=
  fun result => next (result.mapError (.nested index))

def enterAggregate (destination : RecordDestination) (inst : InstId) (items : List Field) (index address : Nat)
    (left : State grow sig) (check : Cursor (E := core3 grow) (HostState sig)) (next : CheckNext grow sig) : State grow sig :=
  { left with ctl := check.control (Track.fields.checked destination inst items 0 address >>= aggregateNext index next) }

def checkTail (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (finish : CheckNext grow sig) : CheckNext grow sig
  | .error issue => finish (.error issue)
  | .ok () => mode.checked destination inst items index cursor >>= finish

def canonTail (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (cursor : Nat)
    (finish : CanonNext grow sig) : CanonNext grow sig := fun () => mode.canonical destination inst items cursor >>= finish

def focus (mode : Track) (destination : RecordDestination) (inst : InstId) (item : Field) (cursor : Nat)
    (right : State grow sig) (canon : Cursor (E := core3 grow) (HostState sig)) (finish : CanonNext grow sig) : State grow sig :=
  { right with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
    item (.memory (mode.slot destination.width item cursor).1) >>= finish) }

/-- Follow the actual memory programs in field order. With each sibling, the
canonical cursor read precedes the child; only common success starts the rest. -/
def Replay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (mode : Track) (destination : RecordDestination) (inst : InstId) (compare : FieldComparison grow sig)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig) :
    List Field → Nat → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, cursor, left, right, check, canon =>
    let slot := mode.slot destination.width item cursor
    let nextCheck := checkTail mode destination inst rest (index + 1) slot.2 checkNext
    let nextCanon := canonTail mode destination inst rest slot.2 canonNext
    let reference := focus mode destination inst item cursor right canon nextCanon
    Steps profile ready (specDispatch ready (host bindings)) right mode.readLabels reference ∧
    compare item index slot.1 left reference check canon nextCheck nextCanon
      (Replay profile ready bindings mode destination inst compare checkNext canonNext finish rest (index + 1) slot.2)

def MixedSlot (destination : RecordDestination) (bytes : Nat) (item : Field) (address : Nat) : Prop :=
  CanonicalHandle item ∨ StringField.Fits destination item ∧
    address % (layout destination.width item.type).alignment.bytes = 0 ∧ address + (layout destination.width item.type).size ≤ bytes

def mixed (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    FieldComparison grow sig := fun item index address left right check canon checkNext canonNext finish =>
  (CanonicalHandle item ∧ HandleFieldThen profile ready bindings item index (.memory address) left right check canon checkNext canonNext
    (fun () => finish)) ∨
  (∃ value : StringField, value.field = item ∧ StringFieldThen profile ready bindings older destination inst value.value (.memory address)
    left right check canon checkNext canonNext (fun () => finish))

/-- The depth bounds the certificate's structural descent, not callback
steps or the number of children in an aggregate. -/
inductive AggregateShape (stringLeaf : Field → Prop) : Nat → Field → Prop where
  | handle {depth item} : CanonicalHandle item → AggregateShape stringLeaf depth item
  | string {depth item} : stringLeaf item → AggregateShape stringLeaf depth item
  | aggregate {depth type items} : (∀ item ∈ items, AggregateShape stringLeaf depth item) →
      AggregateShape stringLeaf (depth + 1) (.aggregate type items)

def nested (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Nat → FieldComparison grow sig
  | 0 => mixed profile ready bindings older destination inst
  | depth + 1 => fun item index address left right check canon checkNext canonNext finish =>
    mixed profile ready bindings older destination inst item index address left right check canon checkNext canonNext finish ∨
      ∃ type children, item = .aggregate type children ∧
        let entered := enterAggregate destination inst children index address left check checkNext
        Steps profile ready (specDispatch ready (host bindings)) left [.tau] entered ∧
          Replay profile ready bindings .fields destination inst (nested profile ready bindings older destination inst depth)
            (aggregateNext index checkNext) canonNext finish children 0 address entered right check canon

abbrev ValueCheckNext (grow : SingleThreaded.GrowOracle) (sig : Signature) (output : Lower.Output) :=
  Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))

abbrev ValueCanonNext (grow : SingleThreaded.GrowOracle) (sig : Signature) (output : Lower.Output) :=
  output.Result → Session grow sig (Ret (core3 grow))

abbrev ValueFinish (grow : SingleThreaded.GrowOracle) (sig : Signature) (output : Lower.Output) :=
  output.Result → Finish grow sig

def publishChecked (destination : RecordDestination) (inst : InstId) (pointer count index : Nat) (output : Lower.Output)
    (next : ValueCheckNext grow sig output) : CheckNext grow sig
  | .error issue => next (.error (.nested index issue))
  | .ok () => ListLower.publish (destination.context inst) destination.width pointer count output >>= fun value => next (.ok value)

def publishCanonical (destination : RecordDestination) (inst : InstId) (pointer count : Nat) (output : Lower.Output)
    (next : ValueCanonNext grow sig output) : CanonNext grow sig :=
  fun () => ListLower.publish (destination.context inst) destination.width pointer count output >>= next

def DescriptorThen (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (output : Lower.Output) (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (next : ValueFinish grow sig output) : Finish grow sig := fun left right check canon =>
  let dispatch := specDispatch ready (host bindings)
  let lhs := fun store => localLeafEnd left left.host store check.thread check.frames check.rest (fun value => checkNext (.ok value))
  let rhs := fun store => localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext
  ∃ store verdict labels, LocalLeafLabels verdict labels ∧
    CoreGrowthSteps profile ready dispatch left labels (lhs store verdict) ∧
    CoreGrowthSteps profile ready dispatch right labels (rhs store verdict) ∧
    ∀ value, verdict = .ok value → next value (lhs store (.ok value)) (rhs store (.ok value)) check canon

/-- The actual admitted value-mode collection tail: strided entries followed
by the descriptor only on common success. Indirect maps do not use it. -/
def ValueListReplay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : TypeOf) (entries : List Field) (depth index pointer : Nat) (output : Lower.Output)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (next : ValueFinish grow sig output) : Finish grow sig :=
  Replay profile ready bindings (.elements (layout destination.width element).size) destination inst
    (nested profile ready bindings older destination inst depth)
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext)
    (DescriptorThen profile ready bindings output checkNext canonNext next) entries 0 pointer

def ValueListReturn (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (type element : TypeOf) (entries : List Field) (depth index : Nat) (output : Lower.Output)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (initial reference last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (pointer : Nat)
    (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  CollectionVisit.Outcome profile ready bindings older destination inst type (layout destination.width element) entries index pointer output
    initial reference last cursor checkNext canonNext seen
    (fun _ => ValueListReplay profile ready bindings older destination inst element entries depth index pointer output checkNext canonNext
      (fun value reached canonical check canon => ChildFrameOver older reached canonical check canon ∧
        Core3.Grows initial.store.core reached.store.core ∧ reached.ctl = check.control (checkNext (.ok value)) ∧
        canonical.ctl = canon.control (canonNext value)))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
