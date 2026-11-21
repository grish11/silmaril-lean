# Mutable arena specification: slots and capacity

Start at `Silmaril.Semantics.Arena.Thms`. The reference state is a partial map
from any key type, including `Nat` or `String`, to occupied slots. A hole is
`none`; `some ⟨none, none⟩` is occupied. Both have no name and no payload, but
only a hole can be reserved. `State.keyName` is a projection, not a substitute
for observing slot occupancy.

`Edit.reserve` requires a hole. `Edit.replace`, `Edit.write`,
`Edit.erasePayload`, and `Edit.clear` require occupancy. A write replaces the
name with the exact result of a caller's partial naming function (`none`
means anonymous). Erasing keeps the name and the occupied slot; clearing
releases the slot but does not change the CAS. `State.step_spec` says exactly
which cell changes on success; `State.step_error_iff` characterizes failure.

`State.observations` collects only pairs with both a name and resident payload.
`State.AdmittedBy` is inclusion in a caller-supplied naming relation, separate
from the transition. With a binding reference, those observations are binding.
`State.admitted_write_iff` says that a write from an admitted state is admitted
precisely when any selected name is justified for the new payload. A local
reservation does not establish that a payload exists in the CAS. An executable
caller must still supply its encoding, integrity and publication policies.

`Dense.equivBounded` gives an exact equivalence at fixed capacity with an
`Array (Option Slot)` of that length, including trailing holes. `Dense.step_commutes`
and `Bounded.step_abstract` give the same in-bound transitions and distinguish
out-of-bounds errors at the bounded interface. `Dense.append_commutes` allocates
at the old capacity, leaving existing keys unchanged. `Dense.packed` embeds
`Array Slot` as the no-hole case. There is no sentinel cell. Explicit reserve
can reuse a hole; a client with live references must impose its own liveness
or non-reuse policy. The bare index is not a generation-checked handle.

`lake build --wfail +Silmaril.Semantics.Arena.Examples` checks vacancy, bounds,
name-only reservation, named and anonymous writes, erase versus clear, append
past a hole, and a successful local write not admitted by the chosen CAS.

Next slices: strict versus discard typed views with codec recovery (including
name-dependent encoders); reachable dependencies and negative-cache provenance;
then indexed Prolly, safe lifetime/GC, and checked reference algorithms. This
slice does not add a wire codec, index tree, hash computation, Rust refinement,
or filesystem operation.
