# Choosing a named DASL interface

**Default:** keep `Named` as the carrier, qualify store-dependent statements with
`Named.Compatible`, and use the functional `Renaming` when a name map is given.
Import `Silmaril.Formats.Dasl.Comparison.Thms` for the bridges; no replacement
syntax, store, or morphism hierarchy is required.

| View | Checked statement | When it is simpler |
| --- | --- | --- |
| Raw `Named` with separate compatibility | `Named.Compatible.rename`: a compatible tree stays compatible after a store morphism into a binding target. | For recursive syntax, erasure, or changing stores, the tree type does not acquire a store index. For syntax alone even the compatibility premise is unnecessary. |
| `Named.Valid` subtype | `Named.Valid.val_rename`: the checked action projects to the same raw action. `Named.Valid.map_iff` says a raw function qualifies on valid inputs iff it has a unique lifting that projects to it. | Useful when every caller works over one fixed store and wants validity supplied by the type. No extra wrapper is needed: `relatedPairsEquiv` identifies guarded raw PER edges with edges on bundled valid pairs, and `respects_onStore_iff_onValid` gives the same preservation law on either carrier for a qualified renaming. |
| Paired shallow spellings plus resolution | `Expands.rename_via_pair`: the paired shallow view agrees by the name map, and the original expansion plus the store morphism give an expansion of the abstract projection. | Use when two spellings must be retained. A shallow pair carries neither payloads nor resolution evidence; agreement alone cannot resolve a missing entry. `Named.compatible_iff_expands` connects raw compatibility to expansion at the tree's own shallow view. |

The bundle equivalence qualifies a **specified tree action**. It does not recover
a whole-store morphism from a map of valid trees: a finite tree never tests a
store entry it cannot expand. Use `Renaming` for a claim about all source entries.

## Functional or relational name rewrites

`Named.Relabels` is an occurrence-by-occurrence witness over tagged object/blob
links, with unchanged inline shape and blob bytes. It preserves erasure. It is
useful for a partial correspondence or when both trees are already given.
On the exact graph of a name function, `Named.Relabels.graph_iff` reduces the
witness to `left.rename names = right`, so the function is the simpler default.
A subrelation of that graph can forbid occurrences: `subgraph_iff` requires
the same output **and** coverage of every recursively mentioned tagged link.
More generally, a functional tagged
correspondence has at most one output, without being total or necessarily
coming from a single map on untagged names. Relabeling syntax alone does not
check store admission; `compatible_of_graph` explicitly uses a store morphism
and target binding. An arbitrary relation may also choose different targets
at different occurrences of the same source name.

## Which PER?

Use a direct named PER when spellings are part of the invariant. Use the erasure
pullback when they are not, and `onStore` only when support must be checked
against a store. `fromShallow_iff_onStore_equality` proves that the shallow-view
PER on valid full expansions is exactly named equality there: binding makes
finite expansion unique. This fails for raw unvalidated expansions. Named
equality restricted to a store refines the erasure equality pullback, strictly
in the fixture: two aliases for the same null are valid and erase identically
but remain distinct as named trees. Arbitrary named PERs still require an
explicit transport law; bundling validity does not supply one.

`lake build --wfail +Silmaril.Formats.Dasl.Comparison.Examples` checks the
raw, bundled, and paired presentations of the same alias collapse, exact
graph relabeling, an object correspondence missing a nested blob, identical
shallow views with different unchecked expansions, and the strict distinction
between name-sensitive and erasure equality.
