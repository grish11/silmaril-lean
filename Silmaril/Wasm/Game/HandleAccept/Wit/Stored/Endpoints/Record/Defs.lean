module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.List.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element)

inductive Issue where
  | preflight (issue : Lower.Issue)
  | notRecord
  | unsupportedField (index : Nat)
  | field (index : Nat) (issue : ListLower.Issue)
  | nested (index : Nat) (issue : Issue)
  | ownerReceipt
  | claims (issue : OwnedMemory.Claims.Issue)
  deriving DecidableEq, Repr

inductive Object where
  | shared (object : Lower.Object)
  | owner (receipt : OwnedMemory.Receipt)

def Object.ownerReceipt : Object → Option OwnedMemory.Receipt
  | .owner receipt => some receipt
  | .shared _ => none

inductive Field where
  | data (type : TypeOf) (payload : Payload type)
  | endpoint (channel : Channel) (element : Element) (id : EndId)
  | context (id : ErrCtxId)
  | owner (receipt : OwnedMemory.Receipt)
  | aggregate (type : TypeOf) (fields : List Field)
  | fixed (element : TypeOf) (length : Nat) (entries : List Field)
  | dynamic (type element : TypeOf) (entries : List Field)
  | sum (type : TypeOf) (arms : List (Option TypeOf)) (tag : Nat) (field : Option Field)

def Field.type : Field → TypeOf
  | .data type _ => type
  | .endpoint channel element _ => ListLower.endpointType channel element
  | .context _ => .errorContext
  | .owner receipt => .own receipt.1
  | .aggregate type _ => type
  | .fixed element length _ => .fixedList element length
  | .dynamic type _ _ => type
  | .sum type _ _ _ => type

mutual
/-- The canonical value described by the active compiled fields. This erases
nominal owner identities for comparison with the ABI; it confers no authority. -/
def Field.value : Field → Val
  | .data _ payload => payload.val
  | .endpoint .stream _ id => .stream id
  | .endpoint .future _ id => .future id
  | .context id => .errorContext id
  | .owner receipt => .own receipt.2.representation
  | .aggregate _ fields => .record (Field.values fields)
  | .fixed _ _ entries | .dynamic _ _ entries => .list (Field.values entries)
  | .sum _ _ tag field => .variant tag (Field.armValue field)
termination_by structural field => field

def Field.values : List Field → List Val
  | [] => []
  | field :: rest => field.value :: Field.values rest
termination_by structural fields => fields

def Field.armValue : Option Field → Option Val
  | none => none
  | some field => some field.value
termination_by structural field => field
end

mutual
/-- The layouts used by the compiled tree agree recursively with its declared type.
For sums, the complete arm layout and the selected payload both agree. -/
inductive Field.LayoutMatches : Field → TypeOf → Prop where
  | data {type : TypeOf} (payload : Payload type) : LayoutMatches (.data type payload) type
  | endpoint {channel : Channel} {element : Element} {id : EndId} :
      LayoutMatches (.endpoint channel element id) (ListLower.endpointType channel element)
  | context {id : ErrCtxId} : LayoutMatches (.context id) .errorContext
  | owner {receipt : OwnedMemory.Receipt} : LayoutMatches (.owner receipt) (.own receipt.1)
  | record {fields : List Field} {types : List (String × TypeOf)} : FieldsMatch fields (types.map Prod.snd) →
      LayoutMatches (.aggregate (.record types) fields) (.record types)
  | tuple {fields : List Field} {types : List TypeOf} :
      FieldsMatch fields types → LayoutMatches (.aggregate (.tuple types) fields) (.tuple types)
  | fixed {entries : List Field} {element : TypeOf} {length : Nat} :
      entries.length = length → EntriesMatch entries element →
      LayoutMatches (.fixed element length entries) (.fixedList element length)
  | list {entries : List Field} {element : TypeOf} :
      EntriesMatch entries element → LayoutMatches (.dynamic (.list element) element entries) (.list element)
  | map {entries : List Field} {key : WIT.KeyType} {element : TypeOf} :
      EntriesMatch entries (.record (mapEntryFields key element)) →
      LayoutMatches (.dynamic (.map key element) (.record (mapEntryFields key element)) entries) (.map key element)
  | variant {types : List (String × Option TypeOf)} {tag : Nat} {field : Option Field} {selected : Option TypeOf} :
      (types.map Prod.snd)[tag]? = some selected → ArmMatches field selected →
      LayoutMatches (.sum (.variant types) (types.map Prod.snd) tag field) (.variant types)
  | optionNone {element : TypeOf} :
      LayoutMatches (.sum (.option element) [none, some element] 0 none) (.option element)
  | optionSome {field : Field} {element : TypeOf} : LayoutMatches field element →
      LayoutMatches (.sum (.option element) [none, some element] 1 (some field)) (.option element)
  | resultOk {field : Option Field} {ok error : Option TypeOf} :
      ArmMatches field ok → LayoutMatches (.sum (.result ok error) [ok, error] 0 field) (.result ok error)
  | resultError {field : Option Field} {ok error : Option TypeOf} : ArmMatches field error →
      LayoutMatches (.sum (.result ok error) [ok, error] 1 field) (.result ok error)

inductive Field.FieldsMatch : List Field → List TypeOf → Prop where
  | nil : FieldsMatch [] []
  | cons {field : Field} {fields : List Field} {type : TypeOf} {types : List TypeOf} :
      LayoutMatches field type → FieldsMatch fields types → FieldsMatch (field :: fields) (type :: types)

inductive Field.EntriesMatch : List Field → TypeOf → Prop where
  | nil {type : TypeOf} : EntriesMatch [] type
  | cons {field : Field} {fields : List Field} {type : TypeOf} :
      LayoutMatches field type → EntriesMatch fields type → EntriesMatch (field :: fields) type

inductive Field.ArmMatches : Option Field → Option TypeOf → Prop where
  | none : ArmMatches none none
  | some {field : Field} {type : TypeOf} : LayoutMatches field type → ArmMatches (some field) (some type)
end

mutual
/-- Authority observations in the order in which the compiled fields transfer them.
Only the selected variant arm contributes, and shared contexts are not spent. -/
def Field.objects : Field → List Object
  | .data _ _ => []
  | .endpoint channel element id => [.shared (.endpoint channel element id)]
  | .context id => [.shared (.errorContext id)]
  | .owner receipt => [.owner receipt]
  | .aggregate _ fields | .fixed _ _ fields | .dynamic _ _ fields => Field.listObjects fields
  | .sum _ _ _ field => Field.armObjects field
termination_by structural field => field

def Field.listObjects : List Field → List Object
  | [] => []
  | field :: rest => field.objects ++ Field.listObjects rest
termination_by structural fields => fields

def Field.armObjects : Option Field → List Object
  | none => []
  | some field => field.objects
termination_by structural field => field
end

namespace Internal

mutual
def supportedField : TypeOf → Bool
  | .record fields => supportedFields fields
  | .tuple types => supportedTypes types
  | .option type => supportedField type
  | .list type | .fixedList type _ => supportedField type
  | .map _ type => supportedField type
  | .variant cases => supportedCases cases
  | .result ok error => supportedCase ok && supportedCase error
  | .future _ | .stream _ | .errorContext | .own _ => true
  | type => (Stored.Lower.checkSchema type).isOk
termination_by structural type => type

def supportedFields : List (String × TypeOf) → Bool
  | [] => true
  | (_, type) :: rest => supportedField type && supportedFields rest
termination_by structural fields => fields

def supportedTypes : List TypeOf → Bool
  | [] => true
  | type :: rest => supportedField type && supportedTypes rest
termination_by structural types => types

def supportedCases : List (String × Option TypeOf) → Bool
  | [] => true
  | (_, type) :: rest => supportedCase type && supportedCases rest
termination_by structural cases => cases

def supportedCase : Option TypeOf → Bool
  | none => true
  | some type => supportedField type
termination_by structural type => type
end

end Internal

abbrev Compile := StateT (List OwnedMemory.Receipt) (Except Issue)

def Compile.mapIssue {Value : Type} (compile : Compile Value) (map : Issue → Issue) : Compile Value :=
  fun receipts => (compile.run receipts).mapError map

def compileItems (compile : Nat → Val → Compile (Field × List Object))
    (values : List Val) : Compile (List Field × List Object) := do
  let items ← values.zipIdx.mapM (fun (value, index) => compile index value)
  return (items.map Prod.fst, items.flatMap Prod.snd)

namespace Internal

def compileEntries (compile : Nat → Val → Compile Field) (values : List Val) : Compile (List Field) :=
  values.zipIdx.mapM (fun (value, index) => compile index value)

def compileLeaf (index : Nat) (type : TypeOf) (value : Val) : Compile Field := do
  let payload ← liftM ((checkValue type value).mapError (Issue.preflight ∘ Lower.Issue.schema))
  match type, payload with
  | .future element, ⟨.future id, _⟩ => return .endpoint .future element id
  | .stream element, ⟨.stream id, _⟩ => return .endpoint .stream element id
  | .errorContext, ⟨.errorContext id, _⟩ => return .context id
  | type, payload =>
    match Stored.Lower.checkSchema type with
    | .ok () => return .data type payload
    | .error _ => throw (.unsupportedField index)

mutual
def compileField {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) : (type : TypeOf) → Val → Compile Field
  | .record types, value => do
    let .record values := value | throw (.preflight .decodedType)
    let fields ← (compileFields cx output 0 types values).mapIssue (.nested index)
    return .aggregate (.record types) fields
  | .tuple types, value => do
    let .record values := value | throw (.preflight .decodedType)
    let fields ← (compileTypes cx output 0 types values).mapIssue (.nested index)
    return .aggregate (.tuple types) fields
  | .fixedList type length, value => do
    if !Internal.supportedField type then throw (.unsupportedField index)
    let .list values := value | throw (.preflight .decodedType)
    if values.length != length then throw (.preflight .decodedType)
    let entries ← (compileEntries (fun pos => compileField cx output pos type) values).mapIssue (.nested index)
    return .fixed type length entries
  | .list type, value => do
    if !Internal.supportedField type then throw (.unsupportedField index)
    let .list values := value | throw (.preflight .decodedType)
    let entries ← (compileEntries (fun pos => compileField cx output pos type) values).mapIssue (.nested index)
    return .dynamic (.list type) type entries
  | .map key type, value => do
    if !Internal.supportedField type then throw (.unsupportedField index)
    let .list values := value | throw (.preflight .decodedType)
    let keyType : TypeOf := .prim key.toPrimitive
    let entryType : TypeOf := .record (mapEntryFields key type)
    let entries ← (compileEntries (fun pos entry => do
      let .record [keyValue, payload] := entry | throw (.nested pos (.preflight .decodedType))
      let key ← liftM ((checkValue keyType keyValue).mapError
        (Issue.nested pos ∘ Issue.preflight ∘ Lower.Issue.schema))
      let field ← (compileField cx output 1 type payload).mapIssue (.nested pos)
      return .aggregate entryType [.data keyType key, field]) values).mapIssue (.nested index)
    return .dynamic (.map key type) entryType entries
  | .option type, value => do
    if !Internal.supportedField type then throw (.unsupportedField index)
    match value with
    | .variant 0 none => return .sum (.option type) [none, some type] 0 none
    | .variant 1 (some value) => do
      let field ← (compileField cx output 0 type value).mapIssue (.nested index)
      return .sum (.option type) [none, some type] 1 (some field)
    | _ => throw (.preflight .decodedType)
  | .variant cases, value => do
    if !Internal.supportedCases cases then throw (.unsupportedField index)
    let .variant tag payload := value | throw (.preflight .decodedType)
    let field ← (compileCases cx output cases tag payload).mapIssue (.nested index)
    return .sum (.variant cases) (cases.map Prod.snd) tag field
  | .result ok error, value => do
    if !(Internal.supportedCase ok && Internal.supportedCase error) then throw (.unsupportedField index)
    match value with
    | .variant 0 payload => do
      let field ← (compileCase cx output ok payload).mapIssue (.nested index)
      return .sum (.result ok error) [ok, error] 0 field
    | .variant 1 payload => do
      let field ← (compileCase cx output error payload).mapIssue (.nested index)
      return .sum (.result ok error) [ok, error] 1 field
    | _ => throw (.preflight .decodedType)
  | .own resource, .own representation => do
    let receipt :: rest ← get | throw (.nested index .ownerReceipt)
    if receipt.1 != resource || receipt.2.representation != representation then
      throw (.nested index .ownerReceipt)
    set rest
    return .owner receipt
  | type, value => compileLeaf index type value

def compileFields {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) : List (String × TypeOf) → List Val → Compile (List Field)
  | [], [] => pure []
  | (_, type) :: types, value :: values => do
    let field ← compileField cx output index type value
    let fields ← compileFields cx output (index + 1) types values
    return field :: fields
  | _, _ => throw (.preflight .decodedType)

def compileTypes {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) : List TypeOf → List Val → Compile (List Field)
  | [], [] => pure []
  | type :: types, value :: values => do
    let field ← compileField cx output index type value
    let fields ← compileTypes cx output (index + 1) types values
    return field :: fields
  | _, _ => throw (.preflight .decodedType)

def compileCases {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output) :
    List (String × Option TypeOf) → Nat → Option Val → Compile (Option Field)
  | [], _, _ => throw (.preflight .decodedType)
  | (_, type) :: _, 0, payload => compileCase cx output type payload
  | _ :: rest, tag + 1, payload => compileCases cx output rest tag payload

def compileCase {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output) :
    Option TypeOf → Option Val → Compile (Option Field)
  | none, none => pure none
  | some type, some payload => do
    let field ← compileField cx output 0 type payload
    return some field
  | _, _ => throw (.preflight .decodedType)
end

end Internal

def Compile.withPlan {Shape : Type} (compile : Compile Shape) (objects : Shape → List Object) :
    Compile (Shape × List Object) :=
  fun receipts => (compile.run receipts).map fun (shape, rest) => ((shape, objects shape), rest)

def compileField {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) (type : TypeOf) (value : Val) : Compile (Field × List Object) :=
  (Internal.compileField cx output index type value).withPlan Field.objects

def compileFields {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) (types : List (String × TypeOf)) (values : List Val) : Compile (List Field × List Object) :=
  (Internal.compileFields cx output index types values).withPlan Field.listObjects

def compileTypes {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) (types : List TypeOf) (values : List Val) : Compile (List Field × List Object) :=
  (Internal.compileTypes cx output index types values).withPlan Field.listObjects

def compileCase {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (type : Option TypeOf) (value : Option Val) : Compile (Option Field × List Object) :=
  (Internal.compileCase cx output type value).withPlan Field.armObjects

def compileCases {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (types : List (String × Option TypeOf)) (tag : Nat) (value : Option Val) : Compile (Option Field × List Object) :=
  (Internal.compileCases cx output types tag value).withPlan Field.armObjects

def compileRecord {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Stored.Lower.Output) :
    Except Issue (List Field × List Object) := do
  let .record types := type | throw .notRecord
  (Stored.Lower.checkOptions cx type output).mapError (.preflight ∘ .abi)
  let .record values := value | throw (.preflight .decodedType)
  let (compiled, rest) ← (compileFields cx output 0 types values).run receipts
  if !rest.isEmpty then throw .ownerReceipt
  return compiled

/-- Compile the entire payload, including non-record roots, with the same receipts and
whole-schema checks used for nested fields. -/
def compileValue {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Stored.Lower.Output) :
    Except Issue (Field × List Object) := do
  (Stored.Lower.checkOptions cx type output).mapError (.preflight ∘ .abi)
  if !Internal.supportedField type then throw (.unsupportedField 0)
  let (compiled, rest) ← (compileField cx output 0 type value).run receipts
  if !rest.isEmpty then throw .ownerReceipt
  return compiled

/-- Inspect every field before starting any field write or guest allocation. Plain fields
use the canonical data path; nested records and sum types participate in the same whole-record
plan. Every arm's schema is checked even when only one arm contributes effects. -/
def preflight {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) :
    Except Issue (List Field × List Object) := do
  (Stored.checkSchema type).mapError (.preflight ∘ .schema)
  compileRecord cx type payload.val [] output

structure Authority (E : CoreEngine) (World : Type) where
  prepare : List Object → P E World (Except Issue Unit)
  transfer : Nat → Object → P E World (Except Issue Nat)

namespace Internal

def publishSlot {E : CoreEngine} {World : Type} (cx : LiftLowerContext E) (slot : Nat) :
    (output : Stored.Lower.Output) → P E World output.Result
  | .flat => pure [i32Flat slot]
  | .memory ptr => storeInt cx slot ptr 4

mutual
def runField {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType) (field : Field)
    (index : Nat) (output : Stored.Lower.Output) : P E World (Except Issue output.Result) :=
  match field with
  | .data type payload => do
    return (← Stored.Lower.lower limits quirks cx type payload output).mapError
      (.field index ∘ .beforeAllocation ∘ .abi)
  | .endpoint channel element id => do
    match ← authority.transfer index (.shared (.endpoint channel element id)) with
    | .error issue => return .error issue
    | .ok slot => return .ok (← publishSlot cx slot output)
  | .context id => do
    match ← authority.transfer index (.shared (.errorContext id)) with
    | .error issue => return .error issue
    | .ok slot => return .ok (← publishSlot cx slot output)
  | .owner receipt => do
    match ← authority.transfer index (.owner receipt) with
    | .error issue => return .error issue
    | .ok slot => return .ok (← publishSlot cx slot output)
  | .aggregate type fields =>
    match output with
    | .flat => do return (← runFlat limits quirks cx authority width fields 0).mapError (.nested index)
    | .memory ptr => do
      checkInBounds cx ptr (layout width type).size
      return (← runMemory limits quirks cx authority width fields ptr 0).mapError (.nested index)
  | .fixed element _ entries =>
    match output with
    | .flat => do return (← runFlat limits quirks cx authority width entries 0).mapError (.nested index)
    | .memory ptr => do
      return (← runElements limits quirks cx authority width entries (layout width element).size ptr 0).mapError
        (.nested index)
  | .dynamic _ element entries => do
    let plan := Field.listObjects entries
    match ← authority.prepare plan with
    | .error (.preflight issue) => return .error (.field index (.beforeAllocation issue))
    | .error issue => return .error (.nested index issue)
    | .ok () =>
      let area := layout width element
      let ptr ← ListLower.allocateRange cx area entries.length
      match ← authority.prepare plan with
      | .error (.preflight issue) => return .error (.field index (.afterAllocation issue))
      | .error issue => return .error (.nested index issue)
      | .ok () =>
        match ← runElements limits quirks cx authority width entries area.size ptr 0 with
        | .error issue => return .error (.nested index issue)
        | .ok () => return .ok (← ListLower.publish cx width ptr entries.length output)
  | .sum type arms tag field =>
    match output with
    | .flat => do
      let joined := (flatten width type).drop 1
      match field with
      | none => return .ok (← lowerFlatVariantWith arms.length joined tag [] (pure []))
      | some field =>
        match ← runField limits quirks cx authority width field 0 .flat with
        | .error issue => return .error (.nested index issue)
        | .ok words =>
          return .ok (← lowerFlatVariantWith arms.length joined tag (flatten width field.type) (pure words))
    | .memory ptr => do
      let alignment := maxCaseAlignment (arms.map (layoutOption width))
      let address ← storeVariantHead cx arms.length alignment tag ptr
      match field with
      | none => return .ok ()
      | some field =>
        return (← runField limits quirks cx authority width field 0 (.memory address)).mapError (.nested index)

def runMemory {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType) :
    List Field → Nat → Nat → P E World (Except Issue Unit)
  | [], _, _ => pure (.ok ())
  | field :: rest, cursor, index => do
    let area := layout width field.type
    let ptr := alignTo cursor area.alignment
    match ← runField limits quirks cx authority width field index (.memory ptr) with
    | .error issue => return .error issue
    | .ok () => runMemory limits quirks cx authority width rest (ptr + area.size) (index + 1)

def runElements {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType) :
    List Field → Nat → Nat → Nat → P E World (Except Issue Unit)
  | [], _, _, _ => pure (.ok ())
  | field :: rest, stride, ptr, index => do
    match ← runField limits quirks cx authority width field index (.memory ptr) with
    | .error issue => return .error issue
    | .ok () => runElements limits quirks cx authority width rest stride (ptr + stride) (index + 1)

def runFlat {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType) :
    List Field → Nat → P E World (Except Issue (List FlatValue))
  | [], _ => pure (.ok [])
  | field :: rest, index => do
    match ← runField limits quirks cx authority width field index .flat with
    | .error issue => return .error issue
    | .ok words =>
      let headWords : List FlatValue := words
      return (← runFlat limits quirks cx authority width rest (index + 1)).map (headWords ++ ·)
end

def emitRecord {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType)
    (type : TypeOf) (fields : List Field) :
    (output : Stored.Lower.Output) → P E World (Except Issue output.Result)
  | .flat => runFlat limits quirks cx authority width fields 0
  | .memory ptr => do
    let area := layout width type
    checkAligned ptr area.alignment.bytes
    checkInBounds cx ptr area.size
    runMemory limits quirks cx authority width fields ptr 0

def emitValue {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (width : AddrType) (type : TypeOf)
    (field : Field) (output : Stored.Lower.Output) : P E World (Except Issue output.Result) := do
  if let .memory ptr := output then
    let area := layout width type
    checkAligned ptr area.alignment.bytes
    checkInBounds cx ptr area.size
  runField limits quirks cx authority width field 0 output

def sharedPlan : List Object → Except Issue (List Lower.Object)
  | [] => .ok []
  | .shared object :: rest => (sharedPlan rest).map (object :: ·)
  | .owner _ :: _ => .error .ownerReceipt

def endpointAuthority {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (cx : LiftLowerContext E) : Authority E (State sig) where
  prepare plan := do
    let store ← getStore
    let state ← hostGet
    return (sharedPlan plan).bind fun objects =>
      (Lower.prepare store state objects).map (fun _ => ()) |>.mapError .preflight
  transfer index object := do
    match object with
    | .shared (.endpoint channel element id) =>
      return (← ListLower.transfer limits cx channel element id).mapError (.field index ∘ .beforeAllocation)
    | .shared (.errorContext id) =>
      if ((← getStore).errCtx? id).isNone then
        return .error (.field index (.beforeAllocation .missingContext))
      return .ok (← lowerErrorContext limits cx id)
    | .owner _ => return .error .ownerReceipt

def lowerWithPlan {E : CoreEngine} {World Shape Result : Type} (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (type : TypeOf) (value : Val)
    (compiled : Except Issue (Shape × List Object)) (objects : Shape → List Object)
    (emit : AddrType → Shape → P E World (Except Issue Result)) : P E World (Except Issue Result) :=
  match compiled with
  | .error issue => pure (.error issue)
  | .ok (shape, _) => do
    match ← authority.prepare (objects shape) with
    | .error issue => return .error issue
    | .ok () =>
      let width ← ptrType cx
      if !Stored.Lower.fits quirks cx.opts.encoding width type value then
        return .error (.preflight (.abi .allocationPrecondition))
      emit width shape

def lowerCompiled {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (authority : Authority E World) (type : TypeOf) (value : Val)
    (output : Stored.Lower.Output) (compiled : Except Issue (List Field × List Object)) :
    P E World (Except Issue output.Result) :=
  lowerWithPlan quirks cx authority type value compiled Field.listObjects fun width fields =>
    emitRecord limits quirks cx authority width type fields output

end Internal

/-- Lower fields in canonical record order. A refusal of the whole record before the first
field is effect-free. An allocator can reenter: each effectful field checks the live store
again, and lists and maps check after allocating their entries. Field errors and traps do not
undo the completed prefix or the effects of realloc. -/
def lower {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type)
    (output : Stored.Lower.Output) : P E (State sig) (Except Issue output.Result) :=
  Internal.lowerCompiled limits quirks cx (Internal.endpointAuthority limits cx) type payload.val output
    (preflight cx type payload output)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
