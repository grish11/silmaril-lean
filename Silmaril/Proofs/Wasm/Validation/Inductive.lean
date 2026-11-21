module

public import Silmaril.Wasm.Validation.Inductive.Defs

public section

namespace Silmaril.Proofs.Wasm.Validation.Inductive

open Silmaril.Wasm.Validation.Inductive

universe u

variable {α : Type u} {entries : List α} {entry : α}

theorem ofLookup_toNat (index : Nat) (found : entries[index]? = some entry) :
    (Path.ofLookup entries index found).toNat = index := by
  induction entries generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      have equal : head = entry := Option.some.inj found
      subst entry
      rfl
    | succ index => exact congrArg Nat.succ (ih index found)

theorem ofLookup_resolves (path : Path entries entry) :
    Path.ofLookup entries path.toNat path.resolves = path := by
  induction path with
  | here => rfl
  | there tail ih => exact congrArg Path.there ih

theorem lookup_value (entries : List α) (index : Nat) :
    (Path.lookup entries index).map Sigma.fst = entries[index]? := by
  induction entries generalizing index with
  | nil => rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index =>
      change (Path.lookup (head :: tail) (index + 1)).map Sigma.fst = tail[index]?
      rw [Path.lookup, ← ih index]
      cases Path.lookup tail index <;> rfl

theorem lookup_path (path : Path entries entry) : Path.lookup entries path.toNat = some ⟨entry, path⟩ := by
  induction path with
  | here => rfl
  | there tail ih => simp [Path.lookup, Path.toNat, ih]

end Silmaril.Proofs.Wasm.Validation.Inductive
