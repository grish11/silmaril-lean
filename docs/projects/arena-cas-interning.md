# Optional interning and shared replacement

`Silmaril.Semantics.Arena.Cas.Intern.{Defs,Thms}` adds one-key-per-name
interning to the ordinary all-keys interface. `Index.Exact` equates
the supplied index with the set of attached resident keys in both
directions. A single hit identifies a key; an exact miss rules out an
attached resident. Placeholder claims do not participate. This is a
conditional index contract, not a verified implementation of an index
on disk or a guarantee for a stale miss. `Outcome.index_after` proves
that remembering the result keeps an initially exact index exact.

`intern` stages collision-safe byte admission before choosing a key. An
existing key is reused only after checking that its named resident and
the authoritative bytes agree with the request. On a miss a supplied
vacant key is installed; `none` represents no capacity. The state
transaction exposes no successor on error. A colliding selected name
never rebinds prior bytes, even with a valid index, spare capacity,
or a constant naming oracle. The uniqueness result comes from the
exact index, not hash injectivity. `Outcome.valid` proves readback and
preserves earlier bindings; it relates input and resident via their
encoded bytes, not object equality for a lossy codec.

For ordinary stable-key mutation, use `Cas.State.plain` and explicitly
reattach if needed. `replaceShared` instead preserves every previously
occupied slot, including the source and all aliases: caller references
are unchanged until the caller installs the returned handle. It can
return the source, a different existing key, or a new key. It does not
reclaim the old key, maintain reference counts, or assume all incoming
references are known. The fixtures cover all three successes and stale
hit, collision, placeholder, occupied and capacity failures. A stale miss
fixture demonstrates why authoritative byte binding alone cannot supply
unique resident keys.

The reference model assumes a single authoritative observation of slots,
index and bytes during the operation. A database backend must prove the
same returned key, slot observation, byte readback and unchanged-on-error
semantics for its transaction; a cache is not such a database. A staged
adapter can handle durable block admission separately if it explicitly
weakens the observation to allow harmless unreferenced blocks on failure.
That weaker refinement, crash durability, and collection policy are not
proved here.
