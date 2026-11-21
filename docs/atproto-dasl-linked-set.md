# Linked DASL object and blob sets

The [layout](../Silmaril/Formats/Dasl/LinkedSet/Defs.lean) stores a single array
of typed links. The ordering key is the complete canonical payload encoding,
with a leading octet that distinguishes an object encoding from raw blob bytes.
The order is unsigned bytewise lexicographic, never CID or digest order.
Objects use a caller-selected partial codec for their semantic source type;
successful encodings must recover that type. An arbitrary shallow tree or
recursively resolved DAG is not assumed to have such an encoding. The concrete
example uses signed-i64 DASL objects and byte-exact blobs under DASL and BDASL.

The format does not store keys twice: the reader follows each top-level link,
recomputes the key from the recovered payload, and checks strict key order and
the profile's preferred name for each key. Object and blob eligibility are
separate guards. A missing, invalid, or nonpreferred link fails the read rather
than disappearing. The preferred-link function is independent of serialization
and store binding; no hash calculation or hash collision-freedom is assumed.

The [theorems](../Silmaril/Formats/Dasl/LinkedSet/Thms.lean) show that successful
normalization deduplicates exactly by semantic equality, that member lookup
recovers the payload, and that valid layouts for a fixed profile are extensionally
canonical. They establish equivalence with finite sets of supported keys, make
the presence and coherence conditions for constructing a layout explicit, and
give cardinality and shallow recovery. No promise is made about root-name
uniqueness across profiles, arbitrary child DAG resolution, or sublinear reads.

```sh
lake build --wfail +Silmaril.Formats.Dasl.LinkedSet.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslLinkedSet.lean
```
