module

public import Silmaril.Formats.Parquet.ColumnIndex.Defs
public import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs
public import Silmaril.Formats.Parquet.FlatColumn.Defs
public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs

/-! Signed INT32 ColumnIndex claims checked downstream of a complete column read. -/

public section

namespace Silmaril.Formats.Parquet.ColumnIndex.Signed

open ThriftCompact
open Traversal (Field Reader)

abbrev Slots := List (Option Int32)

structure Bounds where
  lower : Int32
  upper : Int32
  deriving DecidableEq, Repr

inductive PageError where
  | allNull
  | nullCount (declared : Int) (actual : Nat)
  | boundWord
  | containment
  deriving DecidableEq, Repr

inductive OrderError where
  | footerByteLimit
  | compact (cause : Traversal.Error)
  | footerShape
  | annotated
  | missingOrder
  | unsupportedOrder
  deriving DecidableEq, Repr

inductive Error where
  | index (cause : ColumnIndex.Error)
  | order (cause : OrderError)
  | page (ordinal : Nat) (cause : PageError)
  | pageCount
  | lowerOrder
  | upperOrder
  deriving DecidableEq, Repr

structure Limits where
  column : FlatColumn.Limits := {}
  scalar : ScalarPage.Limits :=
    ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 0⟩
  index : ColumnIndex.Limits := {}

@[expose] def Limits.indexFraming (limits : Limits) : ColumnIndex.Limits :=
  { limits.index with offsetIndex := { limits.index.offsetIndex with page := limits.column.framing } }

private def readStruct (reader : Reader) (start : Nat) : Except OrderError (List Field × Nat) :=
  (Traversal.readStruct reader start).mapError .compact

@[expose] def OrderError.ofColumnOrder : Footer.ColumnOrder.Error → OrderError
  | .footerByteLimit => .footerByteLimit
  | .compact reason => .compact reason
  | _ => .footerShape

structure OrderFields where
  reader : Reader
  leaf : List Field
  order : List Field

/-- Use shared wire selection and translate its detailed failures to the
original signed diagnostic. -/
@[expose] def readOrderFields (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) : Except OrderError OrderFields := do
  let selected ← (Footer.ColumnOrder.readSelection limits snapshot binding.columnOrdinal).mapError
    OrderError.ofColumnOrder
  let some order := selected.order | throw .missingOrder
  pure ⟨selected.reader, selected.leaf.item.fields, order.item.fields⟩

def checkOrderFields (fields : OrderFields) : Except OrderError Unit := do
  if fields.leaf.any (fun field => field.id == 6 || field.id == 10) then throw .annotated
  let [member] := fields.order | throw .footerShape
  if member.id ≠ 1 then throw .unsupportedOrder
  if member.type ≠ .payload .struct then throw .footerShape
  let (members, next) ← readStruct fields.reader member.start
  if !members.isEmpty || next ≠ member.stop then throw .footerShape
  pure ()

/-- Admit the signed type-defined order of an unannotated INT32 leaf.
Selection, annotation presence, then marker checks retain their original
error precedence. -/
@[expose] def checkOrder (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) : Except OrderError Unit :=
  readOrderFields limits snapshot binding >>= checkOrderFields

/-- The selected leaf has neither annotation field. Its ColumnOrder is the
singleton TYPE_ORDER arm with an exactly consumed empty struct. -/
@[expose] def SignedOrder (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) : Prop :=
  ∃ fields member,
    readOrderFields limits snapshot binding = .ok fields ∧
    (∀ field ∈ fields.leaf, field.id ≠ 6 ∧ field.id ≠ 10) ∧
    fields.order = [member] ∧ member.id = 1 ∧ member.type = .payload .struct ∧
    Traversal.readStruct fields.reader member.start = .ok ([], member.stop)

abbrev Bounds.contains (bounds : Bounds) (value : Int32) : Prop :=
  bounds.lower.toInt ≤ value.toInt ∧ value.toInt ≤ bounds.upper.toInt

instance (bounds : Bounds) (value : Int32) : Decidable (bounds.contains value) := by
  unfold Bounds.contains
  infer_instance

private def checkNullCount (count : Option Int) (actual : Nat) : Except PageError Unit :=
  match count with
  | none => .ok ()
  | some n => if n = (actual : Int) then .ok () else .error (.nullCount n actual)

private def readBound (source : Bytes) : Except PageError Int32 :=
  match Plain.decodeInt32 1 source with
  | .ok [value] => .ok value
  | _ => .error .boundWord

private def checkBounds (claim : Claim) (slots : Slots) : Except PageError Bounds := do
  let lower ← readBound claim.lower
  let upper ← readBound claim.upper
  let bounds : Bounds := ⟨lower, upper⟩
  if (slots.filterMap id).all (fun value => decide (bounds.contains value)) then pure bounds
  else throw .containment

/-- Interpret exactly one PLAIN signed word per endpoint. Null-only pages
carry no endpoint in the returned sequence. -/
def checkPage (claim : Claim) (count : Option Int) (slots : Slots) : Except PageError (Option Bounds) := do
  if claim.allNull ≠ slots.all Option.isNone then throw .allNull
  checkNullCount count (slots.countP Option.isNone)
  if claim.allNull then pure none else some <$> checkBounds claim slots

/-- Bounds, if any, have the original decoded words and contain every
present value. Missing null counts assert nothing about the number of nulls. -/
@[expose] def PageValid (claim : Claim) (count : Option Int) (slots : Slots) (result : Option Bounds) : Prop :=
  (claim.allNull = true ↔ ∀ slot ∈ slots, slot = none) ∧
  (∀ n, count = some n → n = (slots.countP Option.isNone : Int)) ∧
  match result with
  | none => claim.allNull = true
  | some bounds => claim.allNull = false ∧
      Plain.decodeInt32 1 claim.lower = .ok [bounds.lower] ∧
      Plain.decodeInt32 1 claim.upper = .ok [bounds.upper] ∧
      ∀ value, some value ∈ slots → bounds.contains value

def checkEach (count : Nat → Option Int) (ordinal : Nat) (claims : List Claim) (pages : List Slots) :
    Except Error (List (Option Bounds)) :=
  if claims.length ≠ pages.length then .error .pageCount
  else ((claims.zip pages).zipIdx ordinal).mapM fun ((claim, slots), page) =>
    (checkPage claim (count page) slots).mapError (.page page)

/-- The three lists are walked in lockstep, with original page ordinals. -/
inductive PagesValid (count : Nat → Option Int) :
    Nat → List Claim → List Slots → List (Option Bounds) → Prop where
  | nil (ordinal : Nat) : PagesValid count ordinal [] [] []
  | cons {ordinal : Nat} {claim : Claim} {claims : List Claim} {slots : Slots} {pages : List Slots}
      {bound : Option Bounds} {bounds : List (Option Bounds)}
      (page : PageValid claim (count ordinal) slots bound)
      (rest : PagesValid count (ordinal + 1) claims pages bounds) :
      PagesValid count ordinal (claim :: claims) (slots :: pages) (bound :: bounds)

def nondecreasing : List Int → Bool
  | a :: b :: rest => decide (a ≤ b) && nondecreasing (b :: rest)
  | _ => true

def ordered (order : BoundaryOrder) (values : List Int) : Bool :=
  match order with
  | .unordered => true
  | .ascending => nondecreasing values
  | .descending => nondecreasing (values.map Neg.neg)

@[expose] def Ordered (order : BoundaryOrder) (values : List Int) : Prop :=
  match order with
  | .unordered => True
  | .ascending => values.Pairwise (· ≤ ·)
  | .descending => values.Pairwise (· ≥ ·)

@[expose] def endpoint (project : Bounds → Int32) (bounds : List (Option Bounds)) : List Int :=
  (bounds.filterMap id).map (Int32.toInt ∘ project)

def declaredCount (index : Index) : Nat → Option Int :=
  let counts := index.raw.nullCounts.map List.toArray
  fun page => counts.bind (·[page]?)

def check (index : Index) (pages : List Slots) : Except Error (List (Option Bounds)) := do
  let bounds ← checkEach (declaredCount index) 0 index.raw.claims pages
  if !ordered index.raw.order (endpoint Bounds.lower bounds) then throw .lowerOrder
  if !ordered index.raw.order (endpoint Bounds.upper bounds) then throw .upperOrder
  pure bounds

@[expose] def Verified (index : Index) (pages : List Slots) (bounds : List (Option Bounds)) : Prop :=
  PagesValid (declaredCount index) 0 index.raw.claims pages bounds ∧
    Ordered index.raw.order (endpoint Bounds.lower bounds) ∧
    Ordered index.raw.order (endpoint Bounds.upper bounds)

def splitPages (entries : List OffsetIndex.Entry) (slots : Slots) : List Slots :=
  (entries.foldl (fun (remaining, reversed) entry =>
    (remaining.drop entry.rowCount, remaining.take entry.rowCount :: reversed)) (slots, [])).2.reverse

def decodePage (limits : ScalarPage.Limits) (layout : FlatColumn.Layout) :
    FlatColumn.DecodePage Int32 FlatScan.AdapterError :=
  let levelLayout := match layout with
    | .required => FlatPage.Layout.required
    | .optional => FlatPage.Layout.optional
  fun leaf _ header body => FlatScan.decodeInt32Page limits ⟨leaf.name, levelLayout⟩ header body

def readFull (limits : Limits) {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) :
    Except (FlatColumn.Error FlatScan.AdapterError) Slots :=
  FlatColumn.readColumn binding limits.column ⟨0, .v1AndV2⟩ (decodePage limits.scalar layout) group

structure Result where
  rows : Slots
  index : Except Error (Option (List (Option Bounds)))

/-- Run the metadata diagnostic only after full column success. The bounds
follow the original checked page order. -/
def diagnose (limits : Limits) {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) (slots : Slots) :
    Except Error (Option (List (Option Bounds))) := do
  let index ← (ColumnIndex.validate limits.indexFraming snapshot group binding.columnOrdinal).mapError .index
  let some present := index | return none
  (checkOrder limits.index.offsetIndex.snapshot.footer snapshot binding).mapError .order
  some <$> check present (splitPages present.offsetIndex.pages slots)

/-- Return the original full read error, or the decoded rows with a separate
semantic diagnostic. A failed or absent index never changes the decoded rows. -/
def read (limits : Limits) {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) :
    Except (FlatColumn.Error FlatScan.AdapterError) Result :=
  (readFull limits binding group).map fun slots => ⟨slots, diagnose limits binding group slots⟩

end Silmaril.Formats.Parquet.ColumnIndex.Signed
