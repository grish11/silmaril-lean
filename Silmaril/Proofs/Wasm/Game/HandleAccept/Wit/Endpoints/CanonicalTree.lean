module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Flat.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Memory.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CanonicalTree

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.CanonicalTree

variable {E : CoreEngine} {World : Type}
variable (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (width : AddrType)

private abbrev Agrees (item : Field) := ∀ out,
  field (World := World) limits quirks cx width item out = leaf limits quirks cx width item out

private theorem fieldTypes {items : List Field} {types : List TypeOf}
    (layout : Field.FieldsMatch items types) : items.map Field.type = types := by
  induction items generalizing types with
  | nil => cases layout; rfl
  | cons _ _ ih => cases layout with | cons head tail => simp [head.type_eq, ih tail]

private theorem entryMember {items : List Field} {type : TypeOf}
    (layout : Field.EntriesMatch items type) : ∀ item ∈ items, item.LayoutMatches type := by
  induction items with
  | nil => simp
  | cons _ _ ih =>
    cases layout with | cons head tail =>
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih tail item member

private theorem fieldMember {items : List Field} {types : List TypeOf}
    (layout : Field.FieldsMatch items types) : ∀ item ∈ items, ∃ type, item.LayoutMatches type := by
  induction items generalizing types with
  | nil => simp
  | cons _ _ ih =>
    cases layout with | cons head tail =>
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, head⟩
    · exact ih tail item member

private theorem flatSequence_eq (items : List Field) (index : Nat)
    (agrees : ∀ item ∈ items, Agrees (World := World) limits quirks cx width item) :
    flat (World := World) limits quirks cx width items =
      flatSequence (fun _ item => lowerFlatAt limits quirks cx width item.value item.type) items index := by
  induction items generalizing index with
  | nil => simp only [flat, flatSequence]
  | cons item rest ih =>
    rw [flat, flatSequence, agrees item (by simp) .flat, ih _ (fun child mem => agrees child (by simp [mem]))]
    rfl

private theorem memorySequence_eq (items : List Field) (ptr index : Nat)
    (agrees : ∀ item ∈ items, Agrees (World := World) limits quirks cx width item) :
    memory (World := World) limits quirks cx width items ptr = memorySequence (ptrType cx)
      (fun _ item addr => store limits quirks cx item.value item.type addr) items ptr index := by
  induction items generalizing ptr index with
  | nil => simp only [memory, memorySequence]
  | cons item rest ih =>
    rw [memory, memorySequence]
    congr 1
    funext reached
    simp only [agrees item (by simp) (.memory _), leaf]
    rw [ih _ (index + 1) (fun child mem => agrees child (by simp [mem]))]

private theorem valueElements_eq (items : List Field) (stride ptr index : Nat)
    (write : Field → Nat → P E World Unit)
    (agrees : ∀ item ∈ items, ∀ addr, field limits quirks cx width item (.memory addr) = write item addr) :
    elements limits quirks cx width items .value stride ptr =
      elementSequence (fun _ => write) items stride ptr index := by
  induction items generalizing ptr index with
  | nil => simp only [elements, elementSequence]
  | cons item rest ih =>
    simp only [elements, elementSequence, agrees item (by simp)]
    rw [ih _ (index + 1) (fun child mem => agrees child (by simp [mem]))]

private theorem mapElements_eq (items : List Field) (key : WIT.KeyType) (element : TypeOf)
    (reached : AddrType) (stride ptr index : Nat)
    (layouts : Field.EntriesMatch items (.record (mapEntryFields key element)))
    (agrees : ∀ item ∈ items, ∀ child, sizeOf child < sizeOf item → ∀ type,
      child.LayoutMatches type → Agrees (World := World) limits quirks cx width child) :
    elements limits quirks cx width items (.memoryMap reached key element) stride ptr =
      elementSequence (fun (_ : Nat) item => (canonicalMapEntry limits quirks cx reached key element item.value :
        Nat → P E World Unit)) items stride ptr index := by
  induction items generalizing ptr index with
  | nil => simp only [elements, elementSequence]
  | cons item rest ih =>
    cases layouts with | cons head tail =>
    have restEq := ih (ptr + stride) (index + 1) tail (fun child mem => agrees child (by simp [mem]))
    have below := agrees item (by simp)
    rcases map_entry_layout head with ⟨keyField, valueField, rfl, keyLayout, valueLayout⟩ | ⟨payload, rfl⟩
    · simp only [elements, elementSequence, restEq, Field.value,
        map_entry_memory_canon limits quirks cx reached key element keyField valueField keyLayout valueLayout ptr 0,
        below keyField (by simp only [Field.aggregate.sizeOf_spec, List.cons.sizeOf_spec]; omega) _ keyLayout (.memory _),
        below valueField (by simp only [Field.aggregate.sizeOf_spec, List.cons.sizeOf_spec]; omega) _ valueLayout (.memory _),
        leaf, memorySequence, Prog.pure_eq, Prog.bind_eq, Prog.pure_bind', Prog.bind_assoc]
    · simp only [elements, elementSequence, restEq]

private theorem sum_eq (type : TypeOf) (arms : List (Option TypeOf)) (tag : Nat) (selected : Option Field)
    (checked : Field.LayoutMatches (.sum type arms tag selected) type)
    (agrees : ∀ child, selected = some child → Agrees (World := World) limits quirks cx width child)
    : Agrees (World := World) limits quirks cx width (.sum type arms tag selected) := by
  intro output
  cases output with
  | flat =>
    cases selected with
    | none =>
      simp only [field, leaf, Field.type, Field.value, lowerFlatAt_sum_program limits quirks cx width type arms tag none checked]
      rfl
    | some child =>
      simp only [field, leaf, Field.type, Field.value, lowerFlatAt_sum_program limits quirks cx width type arms tag _ checked,
        agrees child rfl .flat]
      rfl
  | memory ptr =>
    simp only [field, leaf, Field.type, Field.value, store_sum_program limits quirks cx type arms tag ptr selected checked]
    cases selected with
    | none => rfl
    | some child => simp only [agrees child rfl (.memory _), leaf]; rfl

private theorem armLayout {item : Field} {type : Option TypeOf} (checked : Field.ArmMatches (some item) type) :
    ∃ actual, item.LayoutMatches actual := by
  cases checked with
  | some layout => exact ⟨_, layout⟩

theorem canonical (item : Field) (type : TypeOf) (checked : item.LayoutMatches type) (out : Lower.Output) :
    field limits quirks cx width item out = (leaf limits quirks cx width item out : P E World out.Result) := by
  revert out
  change Agrees (World := World) limits quirks cx width item
  induction item using WellFounded.induction (measure (sizeOf : Field → Nat)).wf generalizing type with
  | h item ih =>
    have below : ∀ child, sizeOf child < sizeOf item → ∀ actual, child.LayoutMatches actual →
        Agrees (World := World) limits quirks cx width child := ih
    cases checked with
    | data | endpoint | context | owner => intro output; cases output <;> simp only [field]
    | @record items schema layoutMatch =>
      have members : ∀ child ∈ items, Agrees (World := World) limits quirks cx width child := by
        intro child mem
        obtain ⟨actual, layout⟩ := fieldMember layoutMatch child mem
        exact below child (by have := List.sizeOf_lt_of_mem mem; simp; omega) actual layout
      intro output
      cases output with
      | flat =>
        simp only [field, leaf, Field.type, Field.value, lowerFlatAt,
          lowerFlatFields_sequence limits quirks cx width items schema 0 (fieldTypes layoutMatch)]
        exact flatSequence_eq limits quirks cx width items 0 members
      | memory ptr =>
        simp only [field, leaf, Field.type, Field.value, store,
          storeFields_sequence limits quirks cx items schema ptr 0 (fieldTypes layoutMatch)]
        exact memorySequence_eq limits quirks cx width items ptr 0 members
    | @tuple items schema layoutMatch =>
      have members : ∀ child ∈ items, Agrees (World := World) limits quirks cx width child := by
        intro child mem
        obtain ⟨actual, layout⟩ := fieldMember layoutMatch child mem
        exact below child (by have := List.sizeOf_lt_of_mem mem; simp; omega) actual layout
      intro output
      cases output with
      | flat =>
        simp only [field, leaf, Field.type, Field.value, lowerFlatAt, ← fieldTypes layoutMatch,
          lowerFlatTypes_sequence limits quirks cx width items 0]
        exact flatSequence_eq limits quirks cx width items 0 members
      | memory ptr =>
        simp only [field, leaf, Field.type, Field.value, store, ← fieldTypes layoutMatch,
          storeTuple_sequence limits quirks cx items ptr 0]
        exact memorySequence_eq limits quirks cx width items ptr 0 members
    | @fixed items element length _ layoutMatch =>
      have types := fun child mem => (entryMember layoutMatch child mem).type_eq
      have members : ∀ child ∈ items, Agrees (World := World) limits quirks cx width child := by
        intro child mem
        exact below child (by have := List.sizeOf_lt_of_mem mem; simp; omega) element (entryMember layoutMatch child mem)
      intro output
      cases output with
      | flat =>
        simp only [field, leaf, Field.type, Field.value, lowerFlatFixed_sequence limits quirks cx width items element length 0 types]
        exact flatSequence_eq limits quirks cx width items 0 members
      | memory ptr =>
        simp only [field, leaf, Field.type, Field.value, fixed_memory_canon limits quirks cx element length items ptr 0]
        congr 1
        funext reached
        apply valueElements_eq
        intro child mem addr
        simp only [members child mem (.memory addr), leaf, types child mem]
        rfl
    | @list items element layoutMatch =>
      have types := fun child mem => (entryMember layoutMatch child mem).type_eq
      have members : ∀ child ∈ items, Agrees (World := World) limits quirks cx width child := by
        intro child mem
        exact below child (by have := List.sizeOf_lt_of_mem mem; simp; omega) element (entryMember layoutMatch child mem)
      intro output
      have seq := dynamic_list_canon (World := World) limits quirks cx width element items output
      have elementsEq (reached : AddrType) (ptr : Nat) :
          elements (World := World) limits quirks cx width items .value (layout reached element).size ptr = elementSequence
            (fun _ child addr => store limits quirks cx child.value element addr) items (layout reached element).size ptr 0 :=
        valueElements_eq limits quirks cx width items _ ptr 0 _ fun child mem addr => by
          have program := members child mem (.memory addr)
          dsimp only [Lower.Output.Result, leaf] at program
          rw [types child mem] at program
          exact program
      cases output <;> simp only [field, leaf, Field.type, Field.value] at seq ⊢ <;>
        rw [seq] <;> simp only [canonicalDynamic, EntryMode.forOutput, elementsEq]
    | @map items key element layoutMatch =>
      have members := entryMember layoutMatch
      have types := fun child mem => (members child mem).type_eq
      intro output
      cases output with
      | flat =>
        simp only [field, leaf, Field.type, Field.value, dynamic_map_flat_canon limits quirks cx width key element items]
        simp only [canonicalDynamic, EntryMode.forOutput]
        congr 1
        funext reached
        congr 1
        funext ptr
        rw [valueElements_eq limits quirks cx width items _ ptr 0 _]
        intro child mem addr
        simp only [below child (by have := List.sizeOf_lt_of_mem mem; simp; omega) _ (members child mem) (.memory addr),
          leaf, types child mem]
        rfl
      | memory dest =>
        simp only [field, leaf, Field.type, Field.value, dynamic_map_memory_canon limits quirks cx width key element items dest]
        simp only [canonicalDynamic, EntryMode.forOutput]
        congr 1
        funext reached
        congr 1
        funext ptr
        apply congrArg (· >>= fun _ => Endpoints.ListLower.publish cx width ptr items.length (.memory dest))
        apply mapElements_eq limits quirks cx width items key element reached _ ptr 0 layoutMatch
        intro child mem node smaller actual cert
        exact below node (by have := List.sizeOf_lt_of_mem mem; simp; omega) actual cert
    | variant found layoutMatch =>
      apply sum_eq limits quirks cx width _ _ _ _ (.variant found layoutMatch)
      intro child eq
      subst_vars
      obtain ⟨actual, cert⟩ := armLayout layoutMatch
      exact below child (by simp only [Field.sum.sizeOf_spec, Option.some.sizeOf_spec]; omega) actual cert
    | optionNone =>
      apply sum_eq limits quirks cx width _ _ _ _ .optionNone
      simp
    | @optionSome child _ layoutMatch =>
      apply sum_eq limits quirks cx width _ _ _ _ (.optionSome layoutMatch)
      rintro _ ⟨⟩
      exact below child (by simp only [Field.sum.sizeOf_spec, Option.some.sizeOf_spec]; omega) _ layoutMatch
    | resultOk layoutMatch =>
      apply sum_eq limits quirks cx width _ _ _ _ (.resultOk layoutMatch)
      intro child eq
      subst_vars
      obtain ⟨actual, cert⟩ := armLayout layoutMatch
      exact below child (by simp only [Field.sum.sizeOf_spec, Option.some.sizeOf_spec]; omega) actual cert
    | resultError layoutMatch =>
      apply sum_eq limits quirks cx width _ _ _ _ (.resultError layoutMatch)
      intro child eq
      subst_vars
      obtain ⟨actual, cert⟩ := armLayout layoutMatch
      exact below child (by simp only [Field.sum.sizeOf_spec, Option.some.sizeOf_spec]; omega) actual cert

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CanonicalTree
