# DASL layouts for finite partial partitions

A partition is observed as `PER.classes`, a set of nonempty member sets.
Exactly the PERs with **finite support** have a representation under either
total shallow layout; having only finitely many classes is not enough. The
arbitrary-PER statement is semantic. To compute a representation, supply a
finite universe covering the domain, a decidable relation, and a total key
order (`PER.Partition.canonicalOn`). Extra universe keys outside the support
do not acquire classes.

- `Encode.Partition.representativeMap` encodes a finite map from key to label.
  Successful keys are partition members; labels need not be keys.
- `Encode.Partition.classMembers` encodes a sorted table with one explicit
  member array per class identifier. It rejects empty or overlapping classes,
  duplicate keys, and decoding a non-ascending array. Raw class identifiers
  need not be members. `group_member_iff` relates the member table to the map
  fiber; `ungroup?_spec` characterizes acceptance precisely.

Both layout codecs recover raw labels. `encodeCanonical` or `encodeCanonical?`
instead chooses each class's least member before writing, and `decodePartition`
or its partial variant observes only the resulting partition. Normalization
preserves the PER, is idempotent, and yields a rooted state (`toUnionFind`).
Under a fixed total codec (or for two successful encodes under the same
partial codec), equal partitions give equal canonical representations and
conversely. Raw labels or different codecs, orders, or profiles do not share
that guarantee.

For links and storage, [`Encode.codedNames`](../Silmaril/Formats/Dasl/Encode/Defs.lean)
transports an abstract naming relation along the selected encoder.
[`PER.naming`](../Silmaril/Formats/PER/Naming/Defs.lean) instead observes classes
of already-named supported representations. Neither is a theorem that arbitrary
names are bound or canonical. With `Wire.Profile.codec`, shallow rendering and
the decode-back guard still apply; map equality for that guard can be decided
by comparing ordered entries when keys and values have decidable equality.
[`Wire.Profile.canonical_root`](../Silmaril/Formats/Dasl/Wire/Profile/Thms.lean)
requires fixed-address store integrity, wire success, a supported name, and
the addressed bytes being present. The separate `roots_binding` result assumes
store binding. Partitioning an arbitrary key type does not require an
algebraic congruence.
