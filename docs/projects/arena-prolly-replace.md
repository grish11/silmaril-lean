# Indexed Prolly value replacement

`Silmaril.Formats.Dasl.Arena.Prolly.Replace.Thms` specifies an edit of a value
at an existing key. `Indexed.planValue` reads the original resident path and
appends exactly one block per visited level, leaf first. A new parent keeps
its separators and every unselected handle, and points the selected edge at
the copied child. It reuses the pinned names of those siblings; it does not
visit or reserialize them. This works with ordinary or tagged link keys. An
object-vs-blob key tag is not a structural tree edge.

`Indexed.replaceValue` stages exact rendered bytes through `Naming.admit` on
the authoritative snapshot. An existing binding cannot be replaced, even if
its bytes are malformed. An intra-batch collision also returns no candidate
arena or store. Equal bytes at one name are permitted: a new local index does
not imply a new content name. The returned name projection changes only for
the new indices; callers still own the root-directory switch. This is a pure
snapshot transition, not a backend's concurrent commit or durability proof.

`replaceValue_exact` proves that the named replacement publishes the same
batch and same snapshot when its decoded reads agree on the selected path
(`PathAgrees`). It preserves all old blocks and names and gives staged-byte
witnesses for the new blocks. `staged_readback` decodes any new index once its
batch is admitted and the reader recovers the profile's emitted bytes.
`replaceValue_rebuild` additionally requires the old canonical tree to be in
the authoritative store and the observed bytes to be a subset. It proves the
previous value, the same root name as rebuilding the edited ordered map,
exact fresh-block count, and readback of the full rebuilt tree.

These theorems do not infer whole-tree validity from a resident block's shape.
An external edge on the route needs localization; a missing local root,
out-of-range local edge, invalid level/shape, exhausted fuel, failed encoding
or name selection, verified absence, and collision are distinct. Verification
of absence requires the named theorem's binding-compatible reference tree.
The local check cannot detect wire errors that occurred before acquisition.

`Policy.cut` depends on level, current chunk length and last key, never on
the value. Existing-value replacement leaves those inputs and separators
unchanged. Insertion or deletion can shift the length/last-key sequence and
thus cuts in later siblings; even without a new cut, a changed maximal key
changes the parent separator. The width-two fixture shifts all subsequent
chunks on insertion/deletion at the front, without using a bucket predicate.
Neither operation is specified as path-local here.

Check with `lake build --wfail +Silmaril.Formats.Dasl.Arena.Prolly.Replace.Thms
+Silmaril.Formats.Dasl.Arena.Prolly.Replace.Examples`. The examples exercise
canonical rebuild, off-path local and external handles, distinct failures
and the tagged link key instance; the fixture naming is not a real hash.
