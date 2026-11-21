module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CompiledValue

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

private abbrev Receipt := OwnedMemory.Receipt
private abbrev Issue := Endpoints.RecordLower.Issue

private abbrev ValueSpec (type : TypeOf) (value : Val) (field : Field) : Prop :=
  field.value = value ∧ field.LayoutMatches type

private abbrev FieldsSpec (types : List TypeOf) (values : List Val) (fields : List Field) : Prop :=
  Field.values fields = values ∧ Field.FieldsMatch fields types

private abbrev EntriesSpec (type : TypeOf) (values : List Val) (fields : List Field) : Prop :=
  Field.values fields = values ∧ Field.EntriesMatch fields type

private abbrev ArmSpec (type : Option TypeOf) (value : Option Val) (field : Option Field) : Prop :=
  Field.armValue field = value ∧ Field.ArmMatches field type

private def Produces {Shape : Type} (compile : Compile Shape) (spec : Shape → Prop) : Prop :=
  ∀ before after shape, compile.run before = .ok (shape, after) → spec shape

private theorem run_bind {Value Result : Type} (first : Compile Value) (next : Value → Compile Result)
    (before : List Receipt) :
    (first >>= next).run before = match first.run before with
    | .error issue => .error issue
    | .ok (value, rest) => (next value).run rest := by
  change (first.run before >>= fun (value, rest) => (next value).run rest) = _
  cases first.run before <;> rfl

private theorem bind_spec {Value Result : Type} {first : Compile Value} {next : Value → Compile Result}
    {initial : Value → Prop} {spec : Result → Prop} (firstSpec : Produces first initial)
    (nextSpec : ∀ value, initial value → Produces (next value) spec) : Produces (first >>= next) spec := by
  intro before after result run
  rw [run_bind] at run
  split at run
  · contradiction
  · rename_i value middle entered
    exact nextSpec value (firstSpec _ _ _ entered) _ _ _ run

private theorem pure_spec {Shape : Type} (shape : Shape) {spec : Shape → Prop} (holds : spec shape) :
    Produces (pure shape) spec := by
  intro before after found run
  rw [← (Prod.mk.inj (Except.ok.inj run)).1]
  exact holds

private theorem error_spec {Shape : Type} (issue : Issue) (spec : Shape → Prop) :
    Produces (throw issue) spec := by
  intro before after found run
  contradiction

private theorem wrap_spec {Inner Outer : Type} {compile : Compile Inner} {inner : Inner → Prop}
    (wrap : Inner → Outer) {spec : Outer → Prop} (preserves : ∀ value, inner value → spec (wrap value))
    (produces : Produces compile inner) : Produces (do let value ← compile; pure (wrap value)) spec :=
  bind_spec produces fun value holds => pure_spec _ (preserves value holds)

private theorem cons_spec {head : Compile Field} {tail : Compile (List Field)} {type : TypeOf} {value : Val}
    {types : List TypeOf} {values : List Val} (headSpec : Produces head (ValueSpec type value))
    (tailSpec : Produces tail (FieldsSpec types values)) :
    Produces (do let field ← head; let fields ← tail; pure (field :: fields))
      (FieldsSpec (type :: types) (value :: values)) :=
  bind_spec headSpec fun field head => wrap_spec (List.cons field)
    (fun _ tail => ⟨congrArg₂ List.cons head.1 tail.1, .cons head.2 tail.2⟩) tailSpec

private theorem values_length (fields : List Field) : (Field.values fields).length = fields.length := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp only [Field.values, List.length_cons, ih]

private theorem mapIssue_spec {Shape : Type} {compile : Compile Shape} {spec : Shape → Prop}
    (produces : Produces compile spec) (map : Issue → Issue) : Produces (compile.mapIssue map) spec := by
  intro before after shape run
  change (compile.run before).mapError map = _ at run
  cases entered : compile.run before with
  | error issue => rw [entered] at run; contradiction
  | ok result => rw [entered] at run; exact produces _ _ _ (entered.trans run)

private theorem check_spec {Shape : Type} (type : TypeOf) (value : Val) (map : Stored.Issue → Issue)
    (next : Stored.Payload type → Compile Shape) {spec : Shape → Prop}
    (produces : ∀ payload, payload.val = value → Produces (next payload) spec) :
    Produces (liftM ((Stored.checkValue type value).mapError map) >>= next) spec := by
  unfold Stored.checkValue
  split
  · exact produces _ rfl
  · intro before after shape run; contradiction

private theorem entries_spec (compile : Nat → Val → Compile Field) (type : TypeOf)
    (element : ∀ index value, Produces (compile index value) (ValueSpec type value)) :
    ∀ (values : List Val) (start : Nat),
      Produces ((values.zipIdx start).mapM (fun (value, index) => compile index value))
        (EntriesSpec type values) := by
  intro values
  induction values with
  | nil => intro start; exact pure_spec [] ⟨rfl, .nil⟩
  | cons value values ih =>
    intro start
    simp only [List.zipIdx_cons, List.mapM_cons]
    exact bind_spec (element start value) fun field head => wrap_spec (List.cons field)
      (fun _ tail => ⟨congrArg₂ List.cons head.1 tail.1, .cons head.2 tail.2⟩) (ih (start + 1))

private theorem compileEntries_spec (compile : Nat → Val → Compile Field) (type : TypeOf) (values : List Val)
    (element : ∀ index value, Produces (compile index value) (ValueSpec type value)) :
    Produces (Internal.compileEntries compile values) (EntriesSpec type values) :=
  entries_spec compile type element values 0

private theorem leaf_spec (index : Nat) (type : TypeOf) (value : Val) :
    Produces (Internal.compileLeaf index type value) (ValueSpec type value) := by
  unfold Internal.compileLeaf
  apply check_spec
  intro payload equal
  split
  · exact pure_spec _ ⟨equal, .endpoint⟩
  · exact pure_spec _ ⟨equal, .endpoint⟩
  · exact pure_spec _ ⟨equal, .context⟩
  · split
    · exact pure_spec _ ⟨equal, .data _⟩
    · exact error_spec _ _

private theorem owner_spec {E : CoreEngine} {cx : LiftLowerContext E} {output : Lower.Output}
    (index : Nat) (resource : RtId) (representation : Nat) :
    Produces (Internal.compileField cx output index (.own resource) (.own representation))
      (ValueSpec (.own resource) (.own representation)) := by
  intro before after field compiled
  cases before with
  | nil => cases compiled
  | cons receipt rest =>
    have read : (get : Compile (List Receipt)).run (receipt :: rest) =
        .ok (receipt :: rest, receipt :: rest) := rfl
    simp only [Internal.compileField, run_bind, read] at compiled
    split at compiled
    · contradiction
    · rename_i accepted
      cases compiled
      constructor
      · simp only [Field.value, Val.own.injEq]
        by_contra different
        simp [different] at accepted
      · have same : receipt.1 = resource := by
          by_contra different
          simp [different] at accepted
        rw [← same]
        exact .owner

section
variable {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)

mutual
private theorem field_spec (index : Nat) (type : TypeOf) (value : Val) :
    Produces (Internal.compileField cx output index type value) (ValueSpec type value) := by
  cases type <;> try exact leaf_spec index _ value
  case record types =>
    simp only [Internal.compileField]
    split
    · rename_i values
      exact wrap_spec (Field.aggregate _) (fun _ fields => ⟨congrArg Val.record fields.1, .record fields.2⟩)
        (mapIssue_spec (fields_spec 0 types values) _)
    · exact error_spec _ _
  case tuple types =>
    simp only [Internal.compileField]
    split
    · rename_i values
      exact wrap_spec (Field.aggregate _) (fun _ fields => ⟨congrArg Val.record fields.1, .tuple fields.2⟩)
        (mapIssue_spec (types_spec 0 types values) _)
    · exact error_spec _ _
  case fixedList type length =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i values
        split
        · exact error_spec _ _
        · rename_i accepted
          have count : values.length = length := by
            by_contra different
            simp [different] at accepted
          exact wrap_spec (Field.fixed type length) (fun fields entries =>
            ⟨congrArg Val.list entries.1, .fixed ((values_length fields).symm.trans
              ((congrArg List.length entries.1).trans count)) entries.2⟩)
            (mapIssue_spec (compileEntries_spec _ type values (fun pos child => field_spec pos type child)) _)
      · exact error_spec _ _
  case list type =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i values
        exact wrap_spec (Field.dynamic (.list type) type) (fun _ entries => ⟨congrArg Val.list entries.1, .list entries.2⟩)
          (mapIssue_spec (compileEntries_spec _ type values (fun pos child => field_spec pos type child)) _)
      · exact error_spec _ _
  case map key type =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i values
        refine wrap_spec (Field.dynamic (.map key type) _)
          (fun _ entries => ⟨congrArg Val.list entries.1, .map entries.2⟩)
          (mapIssue_spec (compileEntries_spec _ (.record (mapEntryFields key type)) values ?_) _)
        intro pos item
        split
        · rename_i keyValue payload
          apply check_spec
          intro checked sameKey
          exact wrap_spec (fun field => Field.aggregate _ [.data _ checked, field])
            (fun _ certificate => ⟨by simp only [Field.value, Field.values, sameKey, certificate.1],
              .record (.cons (.data _) (.cons certificate.2 .nil))⟩)
            (mapIssue_spec (field_spec 1 type payload) _)
        · exact error_spec _ _
      · exact error_spec _ _
  case option type =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · exact pure_spec _ ⟨rfl, .optionNone⟩
      · rename_i child
        exact wrap_spec (fun field => Field.sum (.option type) [none, some type] 1 (some field))
          (fun _ field => ⟨congrArg (fun child => Val.variant 1 (some child)) field.1, .optionSome field.2⟩)
          (mapIssue_spec (field_spec 0 type child) _)
      · exact error_spec _ _
  case variant arms =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i tag payload
        exact wrap_spec (Field.sum (.variant arms) (arms.map Prod.snd) tag)
          (fun _ ⟨_, atTag, certificate⟩ =>
            ⟨congrArg (Val.variant tag) certificate.1, .variant atTag certificate.2⟩)
          (mapIssue_spec (cases_spec arms tag payload) _)
      · exact error_spec _ _
  case result success failure =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i payload
        exact wrap_spec (Field.sum (.result success failure) [success, failure] 0)
          (fun _ field => ⟨congrArg (Val.variant 0) field.1, .resultOk field.2⟩)
          (mapIssue_spec (case_spec success payload) _)
      · rename_i payload
        exact wrap_spec (Field.sum (.result success failure) [success, failure] 1)
          (fun _ field => ⟨congrArg (Val.variant 1) field.1, .resultError field.2⟩)
          (mapIssue_spec (case_spec failure payload) _)
      · exact error_spec _ _
  case own resource =>
    cases value <;> first | exact owner_spec index resource _ | exact leaf_spec index _ _
termination_by structural type

private theorem fields_spec (index : Nat) (types : List (String × TypeOf)) (values : List Val) :
    Produces (Internal.compileFields cx output index types values) (FieldsSpec (types.map Prod.snd) values) := by
  cases types with
  | nil => cases values <;> first | exact pure_spec _ ⟨rfl, .nil⟩ | exact error_spec _ _
  | cons type types =>
    cases values with
    | nil => exact error_spec _ _
    | cons value values =>
      exact cons_spec (field_spec index type.2 value) (fields_spec (index + 1) types values)
termination_by structural types

private theorem types_spec (index : Nat) (types : List TypeOf) (values : List Val) :
    Produces (Internal.compileTypes cx output index types values) (FieldsSpec types values) := by
  cases types with
  | nil => cases values <;> first | exact pure_spec _ ⟨rfl, .nil⟩ | exact error_spec _ _
  | cons type types =>
    cases values with
    | nil => exact error_spec _ _
    | cons value values =>
      exact cons_spec (field_spec index type value) (types_spec (index + 1) types values)
termination_by structural types

private theorem cases_spec (arms : List (String × Option TypeOf)) (tag : Nat) (payload : Option Val) :
    Produces (Internal.compileCases cx output arms tag payload)
      (fun field => ∃ selected, (arms.map Prod.snd)[tag]? = some selected ∧ ArmSpec selected payload field) := by
  cases arms with
  | nil => exact error_spec _ _
  | cons arm arms =>
    cases tag with
    | zero =>
      intro before after field run
      exact ⟨arm.2, rfl, case_spec arm.2 payload before after field run⟩
    | succ tag =>
      intro before after field run
      obtain ⟨selected, atTag, certificate⟩ := cases_spec arms tag payload before after field run
      exact ⟨selected, atTag, certificate⟩
termination_by structural arms

private theorem case_spec (type : Option TypeOf) (payload : Option Val) :
    Produces (Internal.compileCase cx output type payload) (ArmSpec type payload) := by
  cases type with
  | none => cases payload <;> first | exact pure_spec _ ⟨rfl, .none⟩ | exact error_spec _ _
  | some type =>
    cases payload with
    | none => exact error_spec _ _
    | some value => exact wrap_spec some (fun _ field => ⟨congrArg some field.1, .some field.2⟩) (field_spec 0 type value)
termination_by structural type
end

end

private theorem field {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (type : TypeOf) (value : Val) (field : Field) (objects : List Object)
    (before after : List OwnedMemory.Receipt)
    (compiled : (compileField cx output index type value).run before = .ok ((field, objects), after)) :
    field.value = value ∧ field.LayoutMatches type := by
  change ((Internal.compileField cx output index type value).run before).map _ = _ at compiled
  cases step : (Internal.compileField cx output index type value).run before with
  | error issue => rw [step] at compiled; contradiction
  | ok result =>
    obtain ⟨found, rest⟩ := result
    rw [step] at compiled
    cases compiled
    exact field_spec cx output index type value _ _ _ step

theorem value {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Lower.Output) (shape : Field) (objects : List Object)
    (compiled : compileValue cx type value receipts output = .ok (shape, objects)) :
    shape.value = value ∧ shape.LayoutMatches type := by
  cases run : (compileField cx output 0 type value).run receipts with
  | error issue =>
    simp only [compileValue, bind, Except.bind, run] at compiled
    repeat' first | contradiction | split at compiled
  | ok result =>
    obtain ⟨⟨found, plan⟩, rest⟩ := result
    cases rest <;> simp only [compileValue, bind, Except.bind, run, List.isEmpty, Bool.not_true,
      Bool.not_false, ite_true] at compiled
    <;> repeat' first
      | contradiction
      | (cases compiled; exact field cx output 0 type value _ _ _ _ run)
      | split at compiled

theorem record {E : CoreEngine} (cx : LiftLowerContext E) (types : List (String × TypeOf))
    (value : Val) (receipts : List OwnedMemory.Receipt) (output : Lower.Output)
    (fields : List Field) (objects : List Object)
    (compiled : compileRecord cx (.record types) value receipts output = .ok (fields, objects)) :
    .record (Field.values fields) = value ∧ Field.FieldsMatch fields (types.map Prod.snd) := by
  cases options : Lower.checkOptions cx (.record types) output with
  | error issue => simp [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
  | ok accepted =>
    cases value <;> simp only [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
    all_goals try contradiction
    case record values =>
      cases run : (compileFields cx output 0 types values).run receipts with
      | error issue => rw [run] at compiled; contradiction
      | ok result =>
        obtain ⟨⟨found, plan⟩, rest⟩ := result
        cases rest <;> simp only [run, pure, Except.pure, List.isEmpty, Bool.not_true,
          Bool.not_false, ite_true] at compiled
        · cases compiled
          change ((Internal.compileFields cx output 0 types values).run receipts).map _ = _ at run
          cases step : (Internal.compileFields cx output 0 types values).run receipts with
          | error issue => rw [step] at run; contradiction
          | ok result =>
            obtain ⟨fields, rest⟩ := result
            rw [step] at run
            cases run
            have certificate := fields_spec cx output 0 types values _ _ _ step
            exact ⟨congrArg Val.record certificate.1, certificate.2⟩
        · contradiction

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CompiledValue
