# Verified name attachment for arena residents

`Silmaril.Semantics.Arena.Cas.{Defs,Thms}` pairs the ordinary slot model
with a separate authoritative byte reader. `Profile` has a partial serializer
and a partial naming function. It does not require an injective hash, parser,
unique naming across profiles, or a total serializer.

- `State.plain` forgets the byte store for ordinary reads and edits. It
  simulates `Mutable.Access.raw` exactly. Stable-key replacement drops the
  slot's name, and replacing or removing a slot never changes the old byte
  binding. Unrelated slots, including aliases of that name, are unchanged.
- `Profile.attach` verifies an occupied resident against the requested name,
  then stages the exact bytes with `Naming.admit`. It distinguishes vacant,
  unresident, unencodable, unnamed, mismatched, and conflicting bytes.
  A successful attach changes only the selected slot and extends the byte
  graph by exactly the certified pair; rereading that name returns the exact
  bytes. Equal bytes under the same name are allowed. `Mutation.commit` exposes
  the original state on failure.
- `State.attachedKeys` returns the set of all co-present keys for a name. Under
  `Profile.Valid` they are verified, and alias keys at the same name serialize
  to the same bytes. This does not assert equality of the original objects for
  a lossy serializer. `claimKeys` also includes reservations and does not
  imply that bytes are present. These are specification sets, not enumerators.

The authoritative `blocks` snapshot is not a cache. A cache miss cannot
authorize an insertion, and removing an arena key does not reclaim a block.
An implementation must check the authoritative bytes and stage the slot and
binding changes with the same visibility boundary. Layered blob keys would
need a proof that resolving the full tagged name via that second table gives
the same bytes for every admitted name; row identity and digest equality
alone do not establish this. No concrete cache, persistence or GC policy is
required by this API. Fixtures exercise aliases, unresolved reservations,
error/rollback, publication readback and stable replacement under a constant
naming oracle.
