# Collision-safe publication of rebuilt Prolly trees

[`Naming.admit`](../Silmaril/Semantics/Naming/Admission/Thms.lean) checks a
finite batch against the authoritative raw lookup. It accepts exactly when
the union of the old graph and the proposed bindings is binding. Success
returns precisely that union; failure returns a name whose union contains
distinct payloads. An exact repeat is accepted, and errors expose no staged
snapshot. This also detects intra-batch collisions. The relation API stays
abstract; an executable lookup is required only for running admission.

[`Prolly.publish`](../Silmaril/Formats/Dasl/Prolly/Publish/Thms.lean) stages the
blocks of a rebuilt tree in the dedicated object-byte partition using the
selected block codec and a recovering partial wire codec. Every encoded block
must hash to its proposed name, including the named child blocks. Assuming
success, the root is named and the object view has a checked `Stored` witness;
the old bytes survive, and a fixed hash policy is preserved if it already
held. Existing raw bytes that fail decoding still count as present and cannot
be replaced. The independent blob relation is unchanged by the object view.

This is whole-tree publication, not an incremental edit algorithm; callers
can build a fresh tree from their updated ordered map. Neither hash injectivity
nor unique names are needed for collision safety. The check is relative to the
authoritative snapshot: a filtered reader, unreadable storage, or concurrent
writers need a separate transactional protocol. The generic wire codec does
not claim that every abstract shallow object has a canonical CBOR inverse.

## Publishing a named profile

[`RootProfile.publishTree`](../Silmaril/Formats/Dasl/Prolly/Root/Publish/Thms.lean)
first obtains a name from the partial byte oracle. It then replays that
address assignment into the same raw `publish` transaction. `None` at any
reached block aborts before admission; the total functions used for replay
never use their off-domain value on the batch.

With successful naming, publication succeeds exactly when the union of the
authoritative read snapshot and the profile's byte observations binds. A
successful result is exactly that union: old bytes are not replaced and an
equal existing block is reused. An error names a collision in that union,
including conflicting bytes that do not parse. Every published block can be
read back through the supplied recovering wire reader and checked block
decoder. The reader's recovery theorem is a parameter, not an assumption
that every abstract DASL value roundtrips through the canonical CBOR writer.
Names are abstract; no concrete hash or probability law is needed. The API
is over a pure, authoritative snapshot, not a concurrent transaction protocol.

`publishMap` rebuilds the entire bounded tree for the supplied ordered map
and publishes it with the same specification. `build_entries` recovers the
map entries from that tree. This is not incremental rebucketing or a locality
result.
