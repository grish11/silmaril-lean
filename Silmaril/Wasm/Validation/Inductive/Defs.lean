module

public import Silmaril.Wasm.Validation.Intrinsic.Defs
public import Silmaril.Prelude.DeBruijnTyped

/-! Structural references for Wasm index spaces. A path selects an occurrence,
not merely a type: repeated entries remain distinguishable. The binary u32
bound is checked at the boundary, not stored at each successor. -/

@[expose] public section

namespace Silmaril.Wasm.Validation.Inductive

universe u v

inductive Path {α : Type u} : List α → α → Type u where
  | here {entry : α} {entries : List α} : Path (entry :: entries) entry
  | there {other entry : α} {entries : List α} : Path entries entry → Path (other :: entries) entry

namespace Path

variable {α : Type u} {β : Type v} {entries target : List α} {entry : α}

def toNat : {entries : List α} → {entry : α} → Path entries entry → Nat
  | _, _, .here => 0
  | _, _, .there tail => tail.toNat + 1

def map (f : α → β) : {entries : List α} → {entry : α} → Path entries entry → Path (entries.map f) (f entry)
  | _, _, .here => .here
  | _, _, .there tail => .there (tail.map f)

def lookup (entries : List α) (index : Nat) : Option (Sigma (Path entries)) :=
  match entries, index with
  | [], _ => none
  | value :: _, 0 => some ⟨value, .here⟩
  | _ :: tail, index + 1 => (lookup tail index).map fun ⟨value, path⟩ => ⟨value, .there path⟩

theorem resolves (path : Path entries entry) : entries[path.toNat]? = some entry := by
  induction path with
  | here => rfl
  | there tail ih => exact ih

def ofLookup : (entries : List α) → (index : Nat) → entries[index]? = some entry → Path entries entry
  | [], _, found => nomatch found
  | _ :: _, 0, found => (Option.some.inj found) ▸ .here
  | _ :: tail, index + 1, found => .there (ofLookup tail index found)

def rename (index : Nat → Nat) (valid : DeBruijn.TypedRen entries target index)
    (path : Path entries entry) : Path target entry :=
  ofLookup target (index path.toNat) (valid path.resolves)

end Path

/-- Structural occurrence plus the bound needed to erase it to a Wasm index. -/
abbrev Bounded {α : Type u} (entries : List α) (entry : α) :=
  {path : Path entries entry // path.toNat < 2 ^ 32}

def Bounded.erase {α : Type} {entries : List α} {entry : α} {kind : IndexKind}
    (path : Bounded entries entry) : Intrinsic.Ref kind entries entry :=
  ⟨⟨⟨path.val.toNat, path.property⟩⟩, path.val.resolves⟩

end Silmaril.Wasm.Validation.Inductive
