module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Insert
public import Silmaril.Proofs.WasmSpec.BTree.V2.InsertNonfull
public import Silmaril.Proofs.WasmSpec.BTree.V2.Create

/-!
# The B-tree library, version 2: `InsertCreateSpec` by tactics

`btree_insert` (`Silmaril.Proofs.WasmSpec.BTree.V2.Insert`, from `insert_nonfull`'s
specification) with `insert_nonfull` proved by induction on the height
(`Silmaril.Proofs.WasmSpec.BTree.V2.InsertNonfull`), and `btree_create`
(`Silmaril.Proofs.WasmSpec.BTree.V2.Create`). Every-run total correctness at every profile and
host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

/-- **`InsertCreateSpec`, by tactics.** -/
theorem insertCreateSpec_tactic : InsertCreateSpec := fun _ _ _ _ har =>
  ⟨fun hc => insert_valid_of hc har fun _ _ hc' har' lo hi r d => insNF_valid d hc' har' lo hi r,
   fun hc => create_valid hc har⟩

end Silmaril.WasmSpec.BTree.V2
