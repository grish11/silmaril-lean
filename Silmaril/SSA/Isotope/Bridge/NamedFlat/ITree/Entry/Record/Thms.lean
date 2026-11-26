module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Record

open LambdaSSA.Semantics.Interaction.Typed (AtomValues)

universe u
variable {κ : Type (u + 1)} [AtomValues κ] {n m : Nat}

/-- Reindexing commutes with the institution's actual input decoder. -/
theorem inputEnv_reindex {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m}
    (slots : BoundCtx.Renaming β γ) (record : Input γ) (i : Fin n) :
    inputEnv β (reindex slots record) i.val = inputEnv γ record (slots.toFun i).val :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record.inputEnv_reindex slots record i

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Record
