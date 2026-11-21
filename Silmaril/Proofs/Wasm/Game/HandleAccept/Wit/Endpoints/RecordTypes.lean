module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

private theorem run_bind {Value Result : Type} (first : Compile Value) (next : Value → Compile Result)
    (initial : List OwnedMemory.Receipt) :
    (first >>= next).run initial =
      match first.run initial with
      | .error issue => .error issue
      | .ok (value, rest) => (next value).run rest := by
  change (first.run initial >>= fun (value, rest) => (next value).run rest) = _
  cases first.run initial <;> rfl

private theorem run_pure {Value : Type} (value : Value) (initial : List OwnedMemory.Receipt) :
    (pure value : Compile Value).run initial = .ok (value, initial) := rfl

private theorem run_get (initial : List OwnedMemory.Receipt) :
    (get : Compile (List OwnedMemory.Receipt)).run initial = .ok (initial, initial) := rfl

private theorem run_set (receipts initial : List OwnedMemory.Receipt) :
    (set receipts : Compile PUnit).run initial = .ok (⟨⟩, receipts) := rfl

private theorem run_lift {Value : Type} (body : Except Endpoints.RecordLower.Issue Value)
    (initial : List OwnedMemory.Receipt) :
    (liftM body : Compile Value).run initial =
      match body with
      | .error issue => .error issue
      | .ok value => .ok (value, initial) := by
  cases body <;> rfl

private theorem withPlan_ok {Shape : Type} (compile : Compile Shape) (plan : Shape → List Object)
    (before after : List OwnedMemory.Receipt) (shape : Shape) (objects : List Object)
    (compiled : (compile.withPlan plan).run before = .ok ((shape, objects), after)) :
    compile.run before = .ok (shape, after) ∧ objects = plan shape := by
  change (compile.run before).map _ = _ at compiled
  cases success : compile.run before with
  | error issue => simp [success, Except.map] at compiled
  | ok result =>
    obtain ⟨found, rest⟩ := result
    simp only [success, Except.map, Except.ok.injEq, Prod.mk.injEq] at compiled
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := compiled
    exact ⟨rfl, rfl⟩

private theorem internal_field_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (type : TypeOf) (value : Val) (before after : List OwnedMemory.Receipt)
    (field : Field)
    (compiled : (Internal.compileField cx output index type value).run before = .ok (field, after)) :
    field.type = type := by
  unfold Internal.compileField at compiled
  split at compiled <;>
    repeat' first
      | contradiction
      | (have same := compiled.1; subst field; simp_all [Field.type, Endpoints.ListLower.endpointType])
      | simp (config := {failIfUnchanged := true}) only [run_bind, run_pure, run_get,
          run_set, run_lift, Internal.compileLeaf, Except.ok.injEq, Prod.mk.injEq] at compiled
      | split at compiled

private theorem internal_fields_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (types : List (String × TypeOf)) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field)
    (compiled : (Internal.compileFields cx output index types values).run before = .ok (fields, after)) :
    fields.map Field.type = types.map Prod.snd := by
  induction types generalizing index values before after fields with
  | nil =>
    cases values <;> cases compiled
    rfl
  | cons type types ih =>
    cases values with
    | nil => cases compiled
    | cons value values =>
      simp only [Internal.compileFields, run_bind, run_pure] at compiled
      split at compiled <;> try contradiction
      rename_i first middle head
      split at compiled <;> try contradiction
      rename_i rest receipts tail
      cases compiled
      simp only [List.map_cons, internal_field_type cx output index type.2 value before middle first head,
        ih (index + 1) values middle after rest tail]

private theorem internal_types_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (types : List TypeOf) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field)
    (compiled : (Internal.compileTypes cx output index types values).run before = .ok (fields, after)) :
    fields.map Field.type = types := by
  induction types generalizing index values before after fields with
  | nil =>
    cases values <;> cases compiled
    rfl
  | cons type types ih =>
    cases values with
    | nil => cases compiled
    | cons value values =>
      simp only [Internal.compileTypes, run_bind, run_pure] at compiled
      split at compiled <;> try contradiction
      rename_i first middle head
      split at compiled <;> try contradiction
      rename_i rest receipts tail
      cases compiled
      simp only [List.map_cons, internal_field_type cx output index type value before middle first head,
        ih (index + 1) values middle after rest tail]

private theorem internal_case_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (type : Option TypeOf) (payload : Option Val) (before after : List OwnedMemory.Receipt)
    (field : Option Field)
    (compiled : (Internal.compileCase cx output type payload).run before = .ok (field, after)) :
    field.map Field.type = type := by
  cases type <;> cases payload <;> simp only [Internal.compileCase, run_bind, run_pure] at compiled
  all_goals try contradiction
  case none.none => cases compiled; rfl
  case some.some type value =>
    split at compiled <;> try contradiction
    rename_i result rest plan
    cases compiled
    exact congrArg some (internal_field_type cx output 0 type value before after result plan)

private theorem internal_cases_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (arms : List (String × Option TypeOf)) (tag : Nat) (payload : Option Val)
    (before after : List OwnedMemory.Receipt) (field : Option Field)
    (compiled : (Internal.compileCases cx output arms tag payload).run before = .ok (field, after)) :
    arms[tag]?.map Prod.snd = some (field.map Field.type) := by
  induction arms generalizing tag with
  | nil => cases compiled
  | cons arm rest ih =>
    cases tag with
    | zero => exact congrArg some (internal_case_type cx output arm.2 payload before after field compiled).symm
    | succ tag => exact ih tag compiled

theorem field_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (type : TypeOf) (value : Val) (before after : List OwnedMemory.Receipt)
    (field : Field) (objects : List Object)
    (compiled : (compileField cx output index type value).run before = .ok ((field, objects), after)) :
    field.type = type :=
  internal_field_type cx output index type value before after field (withPlan_ok _ _ _ _ _ _ compiled).1

theorem fields_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (types : List (String × TypeOf)) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field) (objects : List Object)
    (compiled : (compileFields cx output index types values).run before = .ok ((fields, objects), after)) :
    fields.map Field.type = types.map Prod.snd :=
  internal_fields_types cx output index types values before after fields (withPlan_ok _ _ _ _ _ _ compiled).1

theorem types_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (types : List TypeOf) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field) (objects : List Object)
    (compiled : (compileTypes cx output index types values).run before = .ok ((fields, objects), after)) :
    fields.map Field.type = types :=
  internal_types_types cx output index types values before after fields (withPlan_ok _ _ _ _ _ _ compiled).1

theorem case_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (type : Option TypeOf) (payload : Option Val) (before after : List OwnedMemory.Receipt)
    (field : Option Field) (objects : List Object)
    (compiled : (compileCase cx output type payload).run before = .ok ((field, objects), after)) :
    field.map Field.type = type :=
  internal_case_type cx output type payload before after field (withPlan_ok _ _ _ _ _ _ compiled).1

theorem cases_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (arms : List (String × Option TypeOf)) (tag : Nat) (payload : Option Val)
    (before after : List OwnedMemory.Receipt) (field : Option Field) (objects : List Object)
    (compiled : (compileCases cx output arms tag payload).run before = .ok ((field, objects), after)) :
    arms[tag]?.map Prod.snd = some (field.map Field.type) :=
  internal_cases_type cx output arms tag payload before after field (withPlan_ok _ _ _ _ _ _ compiled).1

theorem value_spec {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Lower.Output) (field : Field) (objects : List Object)
    (compiled : compileValue cx type value receipts output = .ok (field, objects)) :
    field.type = type ∧ objects = field.objects := by
  cases plan : (compileField cx output 0 type value).run receipts with
  | error issue =>
    simp only [compileValue, bind, Except.bind, plan] at compiled
    repeat' first | contradiction | split at compiled
  | ok result =>
    obtain ⟨⟨found, transfers⟩, rest⟩ := result
    simp only [compileValue, bind, Except.bind, plan] at compiled
    repeat' first
      | contradiction
      | (cases compiled; exact ⟨field_type cx output 0 type value receipts rest _ _ plan,
          (withPlan_ok (Internal.compileField cx output 0 type value) Field.objects _ _ _ _ plan).2⟩)
      | split at compiled

theorem record_spec {E : CoreEngine} (cx : LiftLowerContext E) (types : List (String × TypeOf))
    (value : Val) (receipts : List OwnedMemory.Receipt) (output : Lower.Output)
    (fields : List Field) (objects : List Object)
    (compiled : compileRecord cx (.record types) value receipts output = .ok (fields, objects)) :
    fields.map Field.type = types.map Prod.snd ∧ objects = Field.listObjects fields := by
  cases options : Lower.checkOptions cx (.record types) output with
  | error issue => simp [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
  | ok accepted =>
    cases value <;> simp only [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
    all_goals try contradiction
    case record values =>
      cases plan : (compileFields cx output 0 types values).run receipts with
      | error issue => rw [plan] at compiled; contradiction
      | ok result =>
        obtain ⟨⟨found, transfers⟩, rest⟩ := result
        simp only [plan, pure, Except.pure] at compiled
        repeat' first
          | contradiction
          | (cases compiled; exact ⟨fields_types cx output 0 types values receipts rest _ _ plan,
              (withPlan_ok (Internal.compileFields cx output 0 types values) Field.listObjects _ _ _ _ plan).2⟩)
          | split at compiled

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes
