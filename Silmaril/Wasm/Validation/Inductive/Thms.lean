module

public import Mathlib.Logic.Equiv.Defs
public import Silmaril.Wasm.Validation.Inductive.Defs
import Silmaril.Proofs.Wasm.Validation.Inductive

@[expose] public section

namespace Silmaril.Wasm.Validation.Inductive

universe u v

namespace Path

variable {α : Type u} {β : Type v} {entries target : List α} {entry : α}

@[simp] theorem ofLookup_toNat (index : Nat) (found : entries[index]? = some entry) :
    (ofLookup entries index found).toNat = index := Proofs.Wasm.Validation.Inductive.ofLookup_toNat index found

@[simp] theorem ofLookup_resolves (path : Path entries entry) :
    ofLookup entries path.toNat path.resolves = path := Proofs.Wasm.Validation.Inductive.ofLookup_resolves path

theorem toNat_injective : Function.Injective (toNat : Path entries entry → Nat) := fun _ _ same => by
  have equal := congrArg (lookup entries) same
  rw [Proofs.Wasm.Validation.Inductive.lookup_path, Proofs.Wasm.Validation.Inductive.lookup_path] at equal
  exact eq_of_heq (Sigma.mk.inj (Option.some.inj equal)).2

theorem lookup_value (entries : List α) (index : Nat) :
    (lookup entries index).map Sigma.fst = entries[index]? := Proofs.Wasm.Validation.Inductive.lookup_value entries index

@[simp] theorem lookup_path (path : Path entries entry) : lookup entries path.toNat = some ⟨entry, path⟩ :=
  Proofs.Wasm.Validation.Inductive.lookup_path path

@[simp] theorem rename_toNat (index : Nat → Nat) (valid : DeBruijn.TypedRen entries target index)
    (path : Path entries entry) : (path.rename index valid).toNat = index path.toNat := ofLookup_toNat _ _

@[simp] theorem weaken_eq_there (other : α) (path : Path entries entry) :
    path.rename Nat.succ (DeBruijn.TypedRen.wk _ other) = .there path := by
  apply toNat_injective
  simp [toNat]

@[simp] theorem map_toNat (f : α → β) (path : Path entries entry) : (path.map f).toNat = path.toNat := by
  induction path with
  | here => rfl
  | there _ ih => exact congrArg Nat.succ ih

end Path

variable {α : Type} {entries : List α} {entry : α} {kind : IndexKind}

def Bounded.ofRef (ref : Intrinsic.Ref kind entries entry) : Bounded entries entry :=
  ⟨Path.ofLookup entries ref.index.toNat ref.resolves, by
    rw [Path.ofLookup_toNat]; exact ref.index.value.isLt⟩

/-- Two-sided even at a repeated type: the occurrence and its actual u32 index
are preserved. There is no claim that an arbitrarily long context fits u32. -/
def Bounded.equiv : Bounded entries entry ≃ Intrinsic.Ref kind entries entry where
  toFun := Bounded.erase
  invFun := Bounded.ofRef
  left_inv path := Subtype.ext (Path.ofLookup_resolves path.val)
  right_inv ref := by
    cases ref with
    | mk index found =>
      have same : (Bounded.erase (kind := kind) (Bounded.ofRef
          (⟨index, found⟩ : Intrinsic.Ref kind entries entry))).index = index :=
        Idx.toNat_injective (Path.ofLookup_toNat _ _)
      generalize Bounded.erase (Bounded.ofRef (⟨index, found⟩ : Intrinsic.Ref kind entries entry)) = rebuilt at same ⊢
      cases rebuilt
      cases same
      rfl

end Silmaril.Wasm.Validation.Inductive
