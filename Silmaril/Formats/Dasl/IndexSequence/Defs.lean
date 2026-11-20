module

public import Silmaril.Formats.Dasl.Encode.Map.Thms
public import Silmaril.Semantics.Rope.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.IndexSequence

variable {Name Cas Item : Type}

abbrev Entries (Name : Type) := List (Name × Nat)

structure Columns (Name : Type) where
  t : List Name
  e : List Nat
  deriving DecidableEq

def unzip (entries : Entries Name) : Columns Name := ⟨entries.unzip.1, entries.unzip.2⟩

/-- Check the full width before zipping; no suffix of either column is discarded. -/
def Columns.zip? (columns : Columns Name) : Option (Entries Name) :=
  if columns.t.length = columns.e.length then some (columns.t.zip columns.e) else none

inductive Profile where
  /-- An index into a separate class space, which need not have one class per row. -/
  | classId (count : Nat)
  /-- An index into these same rows: self means root, other parents must be earlier. -/
  | orderedParent

def Profile.allows : Profile → Nat → Nat → Prop
  | .classId count, _, target => target < count
  | .orderedParent, row, target => target ≤ row

instance (profile : Profile) (row target : Nat) : Decidable (profile.allows row target) :=
  match profile with
  | .classId _ => inferInstanceAs (Decidable (_ < _))
  | .orderedParent => inferInstanceAs (Decidable (_ ≤ _))

def Valid (profile : Profile) (entries : Entries Name) : Prop :=
  ∀ row : Fin entries.length, profile.allows row.val (entries.get row).2

instance (profile : Profile) (entries : Entries Name) : Decidable (Valid profile entries) :=
  inferInstanceAs (Decidable (∀ row : Fin entries.length, profile.allows row.val (entries.get row).2))

abbrev Checked (profile : Profile) (Name : Type) := { entries : Entries Name // Valid profile entries }

def check? (profile : Profile) (entries : Entries Name) : Option (Checked profile Name) :=
  if valid : Valid profile entries then some ⟨entries, valid⟩ else none

/-- Occurrence layouts do not need name equality. Only the map refinement checks uniqueness. -/
def asMap? [DecidableEq Name] {profile : Profile} (data : Checked profile Name) :
    Option { layout : Checked profile Name // (layout.val.map Prod.fst).Nodup } :=
  if unique : (data.val.map Prod.fst).Nodup then some ⟨data, unique⟩ else none

/-- Raw rows are exact two-element arrays; only the caller chooses leaf encodings. -/
def entryCodec (name : Encode.TotalCodec Name (Shallow Cas))
    (index : Encode.TotalCodec Nat (Shallow Cas)) : Encode.TotalCodec (Name × Nat) (Shallow Cas) :=
  (name.prod index).then Encode.pairEntry

abbrev SequenceCodec (Item Cas : Type) := Encode.TotalCodec (List Item) (Shallow Cas)

def flat (item : Encode.TotalCodec Item (Shallow Cas)) : SequenceCodec Item Cas := Encode.listOf item

open Silmaril.Semantics.Rope in
/-- Only payload pages are represented: full pages followed by at most one short page.
The empty sequence has no pages. No branch geometry or cached measures are serialized. -/
def pageContents (width : { size : Nat // 0 < size }) : Encode.TotalCodec (List Item) (List (List Item)) :=
  let geometry : Geometry := ⟨width.val, width.property, 0, .left⟩
  { encode := geometry.pages
    decode? := fun pages =>
      if pages.map List.length = sizes .left width.val pages.flatten.length then some pages.flatten else none
    recovers := fun items => by
      rw [← fromList_pages geometry]
      change (if (fromList geometry items).pages.map List.length =
        sizes .left width.val (fromList geometry items).flatten.length then
        some (fromList geometry items).flatten else none) = some items
      rw [flatten_fromList, page_lengths]; simp [geometry] }

def paged (width : { size : Nat // 0 < size }) (item : Encode.TotalCodec Item (Shallow Cas)) :
    SequenceCodec Item Cas := (pageContents width).then (Encode.listOf (Encode.listOf item))

def columnKeys : Finset String := {"t", "e"}

def columnRecord : Encode.TotalCodec (Shallow Cas × Shallow Cas) (Shallow Cas) where
  encode fields := .dict columnKeys (fun key => if key.val = "t" then fields.1 else fields.2)
  decode?
    | .dict keys fields =>
      if same : keys = columnKeys then
        let values : ↥columnKeys → Shallow Cas := same ▸ fields
        some (values ⟨"t", by decide⟩, values ⟨"e", by decide⟩)
      else none
    | _ => none
  recovers _ := rfl

/-- Each column has its own first-class sequence codec. It can use a different geometry. -/
def rawColumns (names : SequenceCodec Name Cas) (indices : SequenceCodec Nat Cas) :
    Encode.TotalCodec (Columns Name) (Shallow Cas) :=
  let tuple : Encode.TotalCodec (Columns Name) (List Name × List Nat) :=
    ⟨fun columns => (columns.t, columns.e), fun fields => some ⟨fields.1, fields.2⟩, fun _ => rfl⟩
  tuple.then ((names.prod indices).then columnRecord)

def columnsCodec : Encode.TotalCodec (Entries Name) (Columns Name) :=
  ⟨unzip, Columns.zip?, fun entries => by
    rw [Columns.zip?, ite_eq_left (by simp [unzip])]
    exact congrArg some (List.zip_unzip entries)⟩

def parallel (names : SequenceCodec Name Cas) (indices : SequenceCodec Nat Cas) : SequenceCodec (Name × Nat) Cas :=
  columnsCodec.then (rawColumns names indices)

/-- Layer index validation over either raw representation, without trusting the codec for guards. -/
def checked (profile : Profile) (raw : SequenceCodec (Name × Nat) Cas) :
    Encode.TotalCodec (Checked profile Name) (Shallow Cas) :=
  (⟨Subtype.val, check? profile, fun ⟨_, valid⟩ => by simp [check?, valid]⟩ :
    Encode.TotalCodec (Checked profile Name) (Entries Name)).then raw

end Silmaril.Formats.Dasl.IndexSequence
