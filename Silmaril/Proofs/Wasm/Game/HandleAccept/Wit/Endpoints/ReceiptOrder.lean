module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.ReceiptOrder

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

private abbrev Receipt := OwnedMemory.Receipt
private abbrev Issue := Endpoints.RecordLower.Issue

private abbrev owners (objects : List Object) : List Receipt := objects.filterMap Object.ownerReceipt

private def Accounts {Shape : Type} (compile : Compile Shape) (plan : Shape → List Receipt) : Prop :=
  ∀ before after shape, compile.run before = .ok (shape, after) → before = plan shape ++ after

private theorem run_bind {Value Result : Type} (first : Compile Value) (next : Value → Compile Result)
    (before : List Receipt) :
    (first >>= next).run before = match first.run before with
    | .error issue => .error issue
    | .ok (value, rest) => (next value).run rest := by
  change (first.run before >>= fun (value, rest) => (next value).run rest) = _
  cases first.run before <;> rfl

private theorem run_get (before : List Receipt) :
    (get : Compile (List Receipt)).run before = .ok (before, before) := rfl

private theorem bind_ok {Value Result : Type} {first : Compile Value} {next : Value → Compile Result}
    {before after : List Receipt} {result : Result} (run : (first >>= next).run before = .ok (result, after)) :
    ∃ middle value, first.run before = .ok (value, middle) ∧ (next value).run middle = .ok (result, after) := by
  change (first.run before >>= fun (value, rest) => (next value).run rest) = _ at run
  cases initial : first.run before with
  | error issue => rw [initial] at run; contradiction
  | ok pair => obtain ⟨value, middle⟩ := pair; rw [initial] at run; exact ⟨middle, value, rfl, run⟩

private theorem pure_ok {Shape : Type} {value shape : Shape} {before after : List Receipt}
    (run : (pure value : Compile Shape).run before = .ok (shape, after)) : value = shape ∧ before = after :=
  Prod.mk.inj (Except.ok.inj run)

private theorem mapIssue_ok {Shape : Type} {first : Compile Shape} {map : Issue → Issue}
    {before after : List Receipt} {shape : Shape} (run : (first.mapIssue map).run before = .ok (shape, after)) :
    first.run before = .ok (shape, after) := by
  change (first.run before).mapError map = _ at run
  cases computed : first.run before with
  | error issue => rw [computed] at run; contradiction
  | ok pair => rw [computed] at run; exact run

private theorem accounts_lift {Value Shape : Type} (first : Except Issue Value) (next : Value → Compile Shape)
    {plan : Shape → List Receipt} (accounts : ∀ value, Accounts (next value) plan) :
    Accounts (liftM first >>= next) plan := by
  intro before after shape compiled
  cases first with
  | error issue => contradiction
  | ok value => exact accounts value before after shape compiled

private theorem accounts_pure {Shape : Type} (shape : Shape) (plan : Shape → List Receipt)
    (empty : plan shape = []) : Accounts (pure shape) plan := by
  intro before after found compiled
  obtain ⟨rfl, rfl⟩ := pure_ok compiled
  rw [empty, List.nil_append]

private theorem accounts_error {Shape : Type} (issue : Issue) (plan : Shape → List Receipt) :
    Accounts (throw issue) plan := by
  intro before after shape compiled
  contradiction

private theorem accounts_cons {First Tail : Type} {first : Compile First} {tail : Compile Tail}
    {headPlan : First → List Receipt} {tailPlan : Tail → List Receipt} {Shape : Type}
    (combine : First → Tail → Shape) (plan : Shape → List Receipt)
    (assembled : ∀ head rest, plan (combine head rest) = headPlan head ++ tailPlan rest)
    (accountsHead : Accounts first headPlan) (accountsTail : Accounts tail tailPlan) :
    Accounts (do let head ← first; let rest ← tail; pure (combine head rest)) plan := by
  intro before after shape compiled
  obtain ⟨middle, head, firstRun, tailRun⟩ := bind_ok compiled
  obtain ⟨last, rest, tailStep, result⟩ := bind_ok tailRun
  obtain ⟨rfl, rfl⟩ := pure_ok result
  rw [accountsHead _ _ _ firstRun, accountsTail _ _ _ tailStep, assembled, List.append_assoc]

private theorem accounts_wrap {Inner Outer : Type} {compile : Compile Inner} {plan : Inner → List Receipt}
    (wrap : Inner → Outer) (outerPlan : Outer → List Receipt)
    (preserves : ∀ inner, outerPlan (wrap inner) = plan inner) (accounts : Accounts compile plan) :
    Accounts (do let inner ← compile; pure (wrap inner)) outerPlan := by
  intro before after shape compiled
  obtain ⟨middle, inner, entered, finished⟩ := bind_ok compiled
  obtain ⟨rfl, rfl⟩ := pure_ok finished
  rw [preserves]
  exact accounts before middle inner entered

private theorem accounts_mapIssue {Shape : Type} {compile : Compile Shape} {plan : Shape → List Receipt}
    (accounts : Accounts compile plan) (map : Issue → Issue) :
    Accounts (compile.mapIssue map) plan :=
  fun before after shape compiled => accounts before after shape (mapIssue_ok compiled)

private theorem entries_accounts (compile : Nat → Val → Compile Field) (values : List Val)
    (element : ∀ position value, Accounts (compile position value) (owners ∘ Field.objects)) :
    Accounts (Internal.compileEntries compile values) (owners ∘ Field.listObjects) := by
  unfold Internal.compileEntries
  generalize values.zipIdx = entries
  induction entries with
  | nil =>
    intro before after fields compiled
    obtain ⟨rfl, rfl⟩ := pure_ok compiled
    rfl
  | cons entry rest ih =>
    rw [List.mapM_cons]
    exact accounts_cons List.cons _ (fun _ _ => by simp [owners, Field.listObjects, List.filterMap_append])
      (element entry.2 entry.1) ih

private theorem leaf_accounts (index : Nat) (type : TypeOf) (value : Val) :
    Accounts (Internal.compileLeaf index type value) (owners ∘ Field.objects) := by
  unfold Internal.compileLeaf
  apply accounts_lift
  intro payload
  split <;> try exact accounts_pure _ _ rfl
  split
  · exact accounts_pure _ _ rfl
  · exact accounts_error _ _

private theorem owner_accounts {E : CoreEngine} {cx : LiftLowerContext E} {output : Lower.Output}
    (index : Nat) (resource : RtId) (representation : Nat) :
    Accounts (Internal.compileField cx output index (.own resource) (.own representation))
      (owners ∘ Field.objects) := by
  intro before after field compiled
  cases before with
  | nil => cases compiled
  | cons receipt rest =>
    simp only [Internal.compileField, run_bind, run_get] at compiled
    split at compiled
    · contradiction
    · cases compiled; rfl

private theorem cons_owners (field : Field) (rest : List Field) :
    owners (Field.listObjects (field :: rest)) = owners field.objects ++ owners (Field.listObjects rest) := by
  simp [owners, Field.listObjects, List.filterMap_append]

section
variable {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)

mutual
private theorem field_accounts (index : Nat) (type : TypeOf) (value : Val) :
    Accounts (Internal.compileField cx output index type value) (owners ∘ Field.objects) := by
  cases type <;> try exact leaf_accounts index _ value
  case record types =>
    simp only [Internal.compileField]
    split
    · rename_i values
      exact accounts_wrap (Field.aggregate (.record types)) _ (fun _ => rfl)
        (accounts_mapIssue (fields_accounts 0 types values) _)
    · exact accounts_error _ _
  case tuple types =>
    simp only [Internal.compileField]
    split
    · rename_i values
      exact accounts_wrap (Field.aggregate (.tuple types)) _ (fun _ => rfl)
        (accounts_mapIssue (types_accounts 0 types values) _)
    · exact accounts_error _ _
  case fixedList type length =>
    simp only [Internal.compileField]
    split
    · exact accounts_error _ _
    · split
      · rename_i values
        split
        · exact accounts_error _ _
        · exact accounts_wrap (Field.fixed type length) _ (fun _ => rfl)
            (accounts_mapIssue (entries_accounts _ values (fun pos child => field_accounts pos type child)) _)
      · exact accounts_error _ _
  case list type =>
    simp only [Internal.compileField]
    split
    · exact accounts_error _ _
    · split
      · rename_i values
        exact accounts_wrap (Field.dynamic (.list type) type) _ (fun _ => rfl)
          (accounts_mapIssue (entries_accounts _ values (fun pos child => field_accounts pos type child)) _)
      · exact accounts_error _ _
  case map key type =>
    simp only [Internal.compileField]
    split
    · exact accounts_error _ _
    · split
      · rename_i values
        refine accounts_wrap (Field.dynamic (.map key type) _) _ (fun _ => rfl)
          (accounts_mapIssue (entries_accounts _ values ?_) _)
        intro pos item
        split
        · rename_i keyValue payload
          apply accounts_lift
          intro checked
          exact accounts_wrap (fun field => Field.aggregate _ [.data _ checked, field]) (owners ∘ Field.objects)
            (fun field => by simp [Field.objects, Field.listObjects])
            (accounts_mapIssue (field_accounts 1 type payload) _)
        · exact accounts_error _ _
      · exact accounts_error _ _
  case option type =>
    simp only [Internal.compileField]
    split
    · exact accounts_error _ _
    · split
      · exact accounts_pure _ _ rfl
      · rename_i child
        exact accounts_wrap (fun field => Field.sum (.option type) [none, some type] 1 (some field)) _
          (fun _ => rfl) (accounts_mapIssue (field_accounts 0 type child) _)
      · exact accounts_error _ _
  case variant arms =>
    simp only [Internal.compileField]
    split
    · exact accounts_error _ _
    · split
      · rename_i tag payload
        exact accounts_wrap (Field.sum (.variant arms) (arms.map Prod.snd) tag) _ (fun _ => rfl)
          (accounts_mapIssue (cases_accounts arms tag payload) _)
      · exact accounts_error _ _
  case result success failure =>
    simp only [Internal.compileField]
    split
    · exact accounts_error _ _
    · split
      · rename_i payload
        exact accounts_wrap (Field.sum (.result success failure) [success, failure] 0) _ (fun _ => rfl)
          (accounts_mapIssue (case_accounts success payload) _)
      · rename_i payload
        exact accounts_wrap (Field.sum (.result success failure) [success, failure] 1) _ (fun _ => rfl)
          (accounts_mapIssue (case_accounts failure payload) _)
      · exact accounts_error _ _
  case own resource =>
    cases value <;> first | exact owner_accounts index resource _ | exact leaf_accounts index _ _
termination_by structural type

private theorem fields_accounts (index : Nat) (types : List (String × TypeOf)) (values : List Val) :
    Accounts (Internal.compileFields cx output index types values) (owners ∘ Field.listObjects) := by
  cases types with
  | nil => cases values <;> first | exact accounts_pure _ _ rfl | exact accounts_error _ _
  | cons type types =>
    cases values with
    | nil => exact accounts_error _ _
    | cons value values =>
      exact accounts_cons List.cons _ cons_owners (field_accounts index type.2 value)
        (fields_accounts (index + 1) types values)
termination_by structural types

private theorem types_accounts (index : Nat) (types : List TypeOf) (values : List Val) :
    Accounts (Internal.compileTypes cx output index types values) (owners ∘ Field.listObjects) := by
  cases types with
  | nil => cases values <;> first | exact accounts_pure _ _ rfl | exact accounts_error _ _
  | cons type types =>
    cases values with
    | nil => exact accounts_error _ _
    | cons value values =>
      exact accounts_cons List.cons _ cons_owners (field_accounts index type value)
        (types_accounts (index + 1) types values)
termination_by structural types

private theorem cases_accounts (arms : List (String × Option TypeOf)) (tag : Nat) (payload : Option Val) :
    Accounts (Internal.compileCases cx output arms tag payload) (owners ∘ Field.armObjects) := by
  cases arms with
  | nil => exact accounts_error _ _
  | cons arm arms =>
    cases tag with
    | zero => exact case_accounts arm.2 payload
    | succ tag => exact cases_accounts arms tag payload
termination_by structural arms

private theorem case_accounts (type : Option TypeOf) (payload : Option Val) :
    Accounts (Internal.compileCase cx output type payload) (owners ∘ Field.armObjects) := by
  cases type with
  | none => cases payload <;> first | exact accounts_pure _ _ rfl | exact accounts_error _ _
  | some type =>
    cases payload with
    | none => exact accounts_error _ _
    | some value => exact accounts_wrap some _ (fun _ => rfl) (field_accounts 0 type value)
termination_by structural type
end

end

private theorem plan_accounts {Shape : Type} {compile : Compile Shape} {objects : Shape → List Object}
    (accounts : Accounts compile (owners ∘ objects)) :
    Accounts (compile.withPlan objects) (owners ∘ Prod.snd) := by
  intro before after compiled success
  change (compile.run before).map _ = _ at success
  cases state : compile.run before with
  | error issue => rw [state] at success; contradiction
  | ok pair =>
    obtain ⟨shape, rest⟩ := pair
    rw [state] at success
    cases success
    exact accounts _ _ _ state

theorem value {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Lower.Output) (field : Field) (objects : List Object)
    (compiled : compileValue cx type value receipts output = .ok (field, objects)) :
    receipts = objects.filterMap Object.ownerReceipt := by
  cases plan : (compileField cx output 0 type value).run receipts with
  | error issue =>
    simp only [compileValue, bind, Except.bind, plan] at compiled
    repeat' first | contradiction | split at compiled
  | ok result =>
    obtain ⟨⟨found, transfers⟩, rest⟩ := result
    cases rest <;> simp only [compileValue, bind, Except.bind, plan, List.isEmpty, Bool.not_true,
      Bool.not_false, ite_true] at compiled
    <;> repeat' first
      | contradiction
      | (cases compiled; have accounted := plan_accounts (field_accounts cx output 0 type value) _ _ _ plan
         exact accounted.trans (List.append_nil _))
      | split at compiled

theorem record {E : CoreEngine} (cx : LiftLowerContext E) (types : List (String × TypeOf))
    (value : Val) (receipts : List OwnedMemory.Receipt) (output : Lower.Output)
    (fields : List Field) (objects : List Object)
    (compiled : compileRecord cx (.record types) value receipts output = .ok (fields, objects)) :
    receipts = objects.filterMap Object.ownerReceipt := by
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
        cases rest <;> simp only [plan, pure, Except.pure, List.isEmpty, Bool.not_true,
          Bool.not_false, ite_true] at compiled
        · cases compiled
          have accounted := plan_accounts (fields_accounts cx output 0 types values) _ _ _ plan
          exact accounted.trans (List.append_nil _)
        · contradiction

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.ReceiptOrder
