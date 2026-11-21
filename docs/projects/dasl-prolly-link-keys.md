# Name-keyed Prolly collections

Import `Silmaril.Formats.Dasl.Prolly.LinkKey.Thms`. Use `LinkKey.object` or
`LinkKey.blob` for a single lane, or `LinkKey.mixed` for `LinkKey.Mixed Name`:
the supplied name order within each lane, objects before blobs. The mixed
carrier is the lexicographic sum, not an order on resolved payloads. The
two lanes remain distinct even when the carrier names coincide. Two names
for the same target are still two keys. No alias normalization is performed.

`LinkKey.Map` and `LinkKey.Set` are the existing ordered map and set at the
mixed key type. Use `Encode.null` for a set's unit payload. `LinkKey.profile`
selects the codecs and existing Prolly builder; `acquire`, `routedLookup`,
and `RootProfile.combineAndPublish` remain unchanged. In particular, branch
children are always structural object links; a link used as a separator or
entry key is not a structural child. Key or payload targets are not read by
these operations. Failure to read a structural child is not verified absence.

The same proofs apply: `TypedMap.view_combine` for typed trees, `combine_spec`
and `combine_membership` for pointwise semantics, `routedLookup_build_sound`
and `combineAndPublish_sound` for binding reference stores, and
`validRootNames_singleton` for store-backed existence and uniqueness in a
fixed successful serialization and naming profile. A different name order,
bucketer, codec or hash profile can change the resulting root. Binding alone
does not provide a root or a unique semantic root name. Closed combination
rebuilds; it does not implement incremental merge.

`lake build --wfail +Silmaril.Formats.Dasl.Prolly.LinkKey.Thms` checks the API.
`lake env lean -DwarningAsError=true --run tests/formats/DaslProllyLinkKeys.lean`
exercises mixed maps and sets, distinct aliases, the same carrier name in
both lanes, domain versus entry inclusion, and checked absence versus a
missing root. The shallow fixture runs with and without object target bodies.
The canonical CBOR fixture publishes a mixed object/raw CID set, reads it
back without either target body, and rejects conflicting occupied bytes.
