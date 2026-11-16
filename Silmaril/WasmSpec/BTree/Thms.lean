module

public import Silmaril.Proofs.WasmSpec.BTree.Tactic
public import Silmaril.Proofs.WasmSpec.BTree.Tests

/-!
# Wasm specification library: `BTree` v1, results

The B-tree library of Watt, Maksimović, Krishnaswami and Gardner, *A Program Logic for
First-Order Encapsulated WebAssembly* (ECOOP 2019, §4). Status **partial**:

* **proved** (`tactic`, `Silmaril.Proofs.WasmSpec.BTree.Tactic`): `obaSpec_tactic : OBASpec`,
  i.e. `oba_get` (the paper's `OBAGet`, Figure 12) and `oba_find` (`OBAFind`, Figure 13, with
  the paper's loop invariant) meet the paper's specifications, strengthened to every-run total
  correctness with the store unchanged, at every profile and for every host relation;
* **stated, tested, not provable as stated**: `SearchSpec` (`btree_search`, Figure 14). Tested
  on `wasmi` against set membership on 300 random B-trees (`tools/wasm-spec-fuzz/tests/btree.rs`)
  and by `#guard` on a hand-built tree. `btree_search` reads the child pointers with `oba_get`,
  but `SearchSpec` gives `oba_get` only `getSpec`, which requires an *ordered* array, and the
  pointer arrays need not be ordered: an `oba_get` meeting `getSpec` may trap on them;
* **stated only** (no implementation in this entry): `InsertCreateSpec` (`BTreeInsert`,
  `BTreeCreate`, Figure 14) for a given implementation.

**Superseded by version 2** (`Silmaril.WasmSpec.BTree.V2`): `getSpec` on bounded arrays, the
callees resolved to the module's code, `SearchSpec` proved (with the plan below), and
`btree_insert`/`btree_create` implemented.

The plan for `SearchSpec`, as carried out in version 2: a loop invariant "page `x`
represents a subtree `T'` of the tree, `Ordered lo hi T'`, and `k ∈ κ ↔ InTree k T'`" with
the variant `height T'` (from `Balanced`), the call rule (`Silmaril.Wasm.Logic.Words.t_call`)
for the calls of `oba_find` and `oba_get`, and the lemma that `k` lies in child `i` (the
`oba_find` index) iff it lies in the node below its keys. For insertion: an implementation
(`B-TREE-INSERT` with `SPLIT-CHILD`, page allocation with `memory.grow`), a frame for the
pages the tree does not own, and the allocator state of the paper's metadata page
(`Free(φ)`, not modelled in `BTree`).

Canonical results: `obaSpec`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree

/-- The canonical solution of `OBASpec`. -/
theorem obaSpec : OBASpec := obaSpec_tactic

end Silmaril.WasmSpec.BTree

/-- info: 'Silmaril.WasmSpec.BTree.obaSpec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.obaSpec_tactic

/-- info: 'Silmaril.WasmSpec.BTree.obaSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.obaSpec
