module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

/-- A successful recursive compilation keeps the declared type used for placement and
flattening by the shared emitter, including nominal owner types. -/
theorem compileField_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) (type : TypeOf) (value : Val) (before after : List OwnedMemory.Receipt)
    (field : Field) (objects : List Object)
    (compiled : (compileField cx output index type value).run before = .ok ((field, objects), after)) :
    field.type = type :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.field_type
    cx output index type value before after field objects compiled

/-- The child type sequence used by the flat and memory emitters agrees with the record schema. -/
theorem compileFields_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) (types : List (String × TypeOf)) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field) (objects : List Object)
    (compiled : (compileFields cx output index types values).run before = .ok ((fields, objects), after)) :
    fields.map Field.type = types.map Prod.snd :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.fields_types
    cx output index types values before after fields objects compiled

/-- Tuples use the declared element order, without dropping or duplicating a field. -/
theorem compileTypes_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) (types : List TypeOf) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field) (objects : List Object)
    (compiled : (compileTypes cx output index types values).run before = .ok ((fields, objects), after)) :
    fields.map Field.type = types :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.types_types
    cx output index types values before after fields objects compiled

/-- A selected sum arm contributes precisely its declared optional payload type. -/
theorem compileCase_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (type : Option TypeOf) (payload : Option Val) (before after : List OwnedMemory.Receipt)
    (field : Option Field) (objects : List Object)
    (compiled : (compileCase cx output type payload).run before = .ok ((field, objects), after)) :
    field.map Field.type = type :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.case_type
    cx output type payload before after field objects compiled

/-- Variant compilation must find a declared arm and preserve its payload type. -/
theorem compileCases_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (arms : List (String × Option TypeOf)) (tag : Nat) (payload : Option Val)
    (before after : List OwnedMemory.Receipt) (field : Option Field) (objects : List Object)
    (compiled : (compileCases cx output arms tag payload).run before = .ok ((field, objects), after)) :
    arms[tag]?.map Prod.snd = some (field.map Field.type) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.cases_type
    cx output arms tag payload before after field objects compiled

theorem compileValue_type {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Stored.Lower.Output) (field : Field) (objects : List Object)
    (compiled : compileValue cx type value receipts output = .ok (field, objects)) : field.type = type :=
  (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.value_spec
    cx type value receipts output field objects compiled).1

theorem compileRecord_types {E : CoreEngine} (cx : LiftLowerContext E) (types : List (String × TypeOf))
    (value : Val) (receipts : List OwnedMemory.Receipt) (output : Stored.Lower.Output)
    (fields : List Field) (objects : List Object)
    (compiled : compileRecord cx (.record types) value receipts output = .ok (fields, objects)) :
    fields.map Field.type = types.map Prod.snd :=
  (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.record_spec
    cx types value receipts output fields objects compiled).1

/-- The preflight plan is exactly the authority traversal of the emitted field. -/
theorem compileValue_plan {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Lower.Output) (field : Field) (objects : List Object)
    (compiled : compileValue cx type value receipts output = .ok (field, objects)) :
    objects = field.objects :=
  (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.value_spec
    cx type value receipts output field objects compiled).2

/-- Whole-record preflight and dynamic subregions use the same field-order traversal. -/
theorem compileRecord_plan {E : CoreEngine} (cx : LiftLowerContext E) (types : List (String × TypeOf))
    (value : Val) (receipts : List OwnedMemory.Receipt) (output : Lower.Output)
    (fields : List Field) (objects : List Object)
    (compiled : compileRecord cx (.record types) value receipts output = .ok (fields, objects)) :
    objects = Field.listObjects fields :=
  (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes.record_spec
    cx types value receipts output fields objects compiled).2

theorem lower_preflight_error {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type)
    (output : Stored.Lower.Output) {issue : Issue}
    (reject : preflight cx type payload output = .error issue) :
    (lower limits quirks cx type payload output : P E (State sig) _) = pure (.error issue) := by
  simp only [lower, reject, Internal.lowerCompiled, Internal.lowerWithPlan]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
