module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Record

open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open Silmaril.Isotope.Semantics (encodeValue)

universe u
variable {κ : Type (u + 1)} [AtomValues κ] {n m : Nat}

/-- The entry decoder encodes the value at each typed record position. -/
theorem inputEnv_field (β : BoundCtx (Ty κ) n) (record : Input β) (i : Fin n) :
    inputEnv β record i.val = encodeValue (AtomValues.carrier (κ := κ)) (β.get i) (field β record i) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record.inputEnv_field β record i

/-- Every typed bound environment is supplied by a caller record. -/
theorem field_surjective (β : BoundCtx (Ty κ) n) : Function.Surjective (field β) :=
  fun fields => ⟨ofFields β fields, funext (Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record.field_ofFields β fields)⟩

/-- Reindexing commutes with the institution's actual input decoder. -/
theorem inputEnv_reindex {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m}
    (slots : BoundCtx.Renaming β γ) (record : Input γ) (i : Fin n) :
    inputEnv β (reindex slots record) i.val = inputEnv γ record (slots.toFun i).val :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record.inputEnv_reindex slots record i

@[simp]
theorem reindex_id (β : BoundCtx (Ty κ) n) (record : Input β) :
    reindex (.id β) record = record :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record.reindex_id β record

/-- Reading a record along a composite checked slot map is successive
projection, in the reverse direction to the maps on slots. -/
theorem reindex_comp {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m}
    {k : Nat} {δ : BoundCtx (Ty κ) k} (first : BoundCtx.Renaming β γ)
    (second : BoundCtx.Renaming γ δ) (record : Input δ) :
    reindex (first.comp second) record = reindex first (reindex second record) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record.reindex_comp first second record

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Record
