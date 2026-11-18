module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Search
public import Silmaril.Proofs.WasmSpec.BTree.V2.InsertCreate
public import Silmaril.Proofs.WasmSpec.BTree.V2.Tests

/-!
# Wasm specification library: `BTree` v2, results

The B-tree library of Watt, Maksimović, Krishnaswami and Gardner, *A Program Logic for
First-Order Encapsulated WebAssembly* (ECOOP 2019, §4), with insertion and creation
implemented (`Silmaril.WasmSpec.BTree.V2.Defs`). Status **verified**: every statement is proved
by tactics (`tactic`), as every-run total correctness at every profile and for every host
relation:

* `obaSpec_tactic : OBASpec` (`Silmaril.Proofs.WasmSpec.BTree.V2.Oba`): `oba_get` on any bounded
  array, `oba_find` with the paper's loop invariant; the store unchanged;
* `searchSpec_tactic : SearchSpec` (`Silmaril.Proofs.WasmSpec.BTree.V2.Search`): the descent
  invariant (the current page holds a subtree that contains `k` iff the tree does), the least
  such height as the variant, the call rule for `oba_find`/`oba_get` and the child-index lemma;
  the store unchanged;
* `insertCreateSpec_tactic : InsertCreateSpec` (`Silmaril.Proofs.WasmSpec.BTree.V2.InsertCreate`):
  `btree_insert` returns `1` with a B-tree of `κ ∪ {k}` or `0` (a page allocation failed) with a
  B-tree of `κ`, changing no byte outside page `0`, the old tree's pages and the old free pages;
  `btree_create` returns `1` with an empty B-tree or `0` with the memory still empty. The
  helpers are proved against internal specifications: `ba_insert`, `ba_copy` (`Arrays`),
  `alloc_node` (`Alloc`), `split_child` (`SplitChild`, with the abstract split in `Split`),
  `insert_nonfull` (`InsertNonfull`, by induction on the height), `btree_insert` (`Insert`),
  `btree_create` (`Create`).

Also tested: on `wasmi` (`tools/wasm-spec-fuzz/tests/btree_v2.rs`: random insert/search
sequences against a Rust `BTreeSet` and a model of CLRS insertion, the memory checked to be a
B-tree after every insertion, the memory frame, out-of-memory runs and free pages) and by
`#guard` with silmaril-lean's interpreter (`Silmaril.Proofs.WasmSpec.BTree.V2.Tests`).

Canonical results: `obaSpec`, `searchSpec_holds`, `insertCreateSpec_holds`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

/-- The canonical solution of `OBASpec`. -/
theorem obaSpec : OBASpec := obaSpec_tactic

/-- The canonical solution of `SearchSpec`. -/
theorem searchSpec_holds : SearchSpec := searchSpec_tactic

/-- The canonical solution of `InsertCreateSpec`. -/
theorem insertCreateSpec_holds : InsertCreateSpec := insertCreateSpec_tactic

end Silmaril.WasmSpec.BTree.V2

/-- info: 'Silmaril.WasmSpec.BTree.V2.obaSpec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.V2.obaSpec_tactic

/-- info: 'Silmaril.WasmSpec.BTree.V2.searchSpec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.V2.searchSpec_tactic

/-- info: 'Silmaril.WasmSpec.BTree.V2.obaSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.V2.obaSpec

/-- info: 'Silmaril.WasmSpec.BTree.V2.searchSpec_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.V2.searchSpec_holds

/-- info: 'Silmaril.WasmSpec.BTree.V2.insertCreateSpec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.V2.insertCreateSpec_tactic

/-- info: 'Silmaril.WasmSpec.BTree.V2.insertCreateSpec_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.BTree.V2.insertCreateSpec_holds
