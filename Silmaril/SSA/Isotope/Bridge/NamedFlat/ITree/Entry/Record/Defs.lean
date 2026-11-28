module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Defs

/-! # Reindexing supplied entry records by a typed slot map -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Record

open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)

universe u
variable {κ : Type (u + 1)} [AtomValues κ] {n m : Nat}

local notation "C" => AtomValues.carrier (κ := κ)

/-- The institution's supplied input at the specified entry context. -/
abbrev Input (β : BoundCtx (Ty κ) n) := Ty.denote C (Region.packedInputType β.toList)

/-- Select a field of the supplied record in de Bruijn order. -/
def field : {n : Nat} → (β : BoundCtx (Ty κ) n) → Input β → (i : Fin n) → Ty.denote C (β.get i)
  | _, .nil, _, i => i.elim0
  | _, .snoc β _, record, i => Fin.cases record.2 (field β record.1) i

/-- Assemble the typed input record from its fields. -/
def ofFields : {n : Nat} → (β : BoundCtx (Ty κ) n) → ((i : Fin n) → Ty.denote C (β.get i)) → Input β
  | _, .nil, _ => PUnit.unit
  | _, .snoc β _, fields => (ofFields β (fun i => fields i.succ), fields 0)

/-- Pull a supplied record back along a type-preserving finite slot map. -/
def reindex {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m} (slots : BoundCtx.Renaming β γ)
    (record : Input γ) : Input β :=
  ofFields β fun i => (congrArg (Ty.denote C) (slots.typed i)) ▸ field γ record (slots.toFun i)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Record
