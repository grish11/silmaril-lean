# Artifact naming prototype

This is an opt-in consumer of the [DASL foundation](atproto-dasl.md) (#1175).
It does not replace the `sil project` artifact registry, `Containers.Cas.Store`,
or the Docker/OCI example's checks. The registry verifies declared file
digests and separately records Lean observations; the Docker example checks
Docker's image ID and layer IDs, which are not DASL CIDs over an image export.
To name an export or other file here, supply the exact bytes, not a Docker ID,
tag, path, or a claimed digest copied from a different observation model.

## Three distinct layers

1. **Data and index.** The manifest is ASCII TSV with the header shown in
   [`fixtures.tsv`](../tools/verification-projects/artifact-naming/fixtures.tsv); `-` is the empty
   payload. `import_lean.py` emits declared name and payload bytes as a fresh
   Lean module of literals only. It checks the TSV syntax, not CID structure,
   conflicts or digests, and works without the verifier or hash backends.
   `Table` is a sparse bit trie; lookup follows at most one
   edge per bit of the caller's routing key. `set` overwrites one route; it
   checks neither integrity nor conflicts. Pre-materialize the constructors
   if construction cost matters to reduction. A route that is not injective
   can alias names; the fixture routes the full opaque name bytes. There is
   no dependency on the open codec or language PRs.
2. **Kernel facts.** `Table.lookup_iff` characterizes lookup by the structural
   entry relation, `relation_binding` proves functionality by name, and
   `overlay_iff` and `overlay_namesOf` recover union on compatible chunks.
   Left priority on incompatible chunks is not evidence of union. Repeat
   the binary overlay for multiple chunks, justifying compatibility at each
   step. The regression proves `observed hello bytes`, `observed empty bytes`,
   and `graph lookupDecoded title titleValue`. The separately materialized
   object trie is bridged by `Predecoded.Agrees`, a pointwise parser witness;
   the fixture proves it for every query, including a miss, using one checked
   serialization example. The bridge deliberately only takes an object
   lookup. It does not certify a raw blob as an object or assert parser
   agreement for any imported predecoded table automatically.
3. **External assurance.** `verify.py verify` recomputes the exact payload
   digest and validates the declared profile, role, algorithm, and CID
   boundary; conflicting payloads under one binary CID are rejected, identical
   bindings with distinct row IDs are allowed. Supported: CIDv1 `raw` (55)
   and `drisl` (71), SHA-256 (12), and in BDASL also BLAKE3 (1e), all 32-byte
   digests. This matches the binary rules of `Drisl.Cid.codec` (exact
   boundary); no base32 spelling or general multicodec registry is involved.
   `drisl` in the verifier selects the CID codec, not a CBOR validity check;
   the Lean example checks parsing and serialization using the existing wire
   reader/writer. Neither the script nor the parser resolves link targets.

## Running the slice

From the repository root with the pinned Lean and Python 3, check the kernel
facts without computing any hashes:

```sh
lake build --wfail +Silmaril.Semantics.Naming.Table.Thms +Silmaril.Formats.Dasl.Predecoded.Thms
bash tools/verification-projects/artifact-naming/check.sh
```

Independently, with `b3sum` on `PATH` for the BLAKE3 fixture, run the
standalone verifier tests, check hash consistency of the same declarations,
or compute names for exact bytes. Hosted Lean CI does not run this verifier:

```sh
tool=tools/verification-projects/artifact-naming
python3 -BEs "$tool/test_verify.py"
python3 -BEs "$tool/verify.py" verify "$tool/fixtures.tsv"
set -o pipefail
printf 'hello\n' | python3 -BEs "$tool/verify.py" name dasl raw sha256 -
bash "$tool/check.sh" "$tool/fixtures.tsv" /tmp/silmaril-title.cbor
python3 -BEs "$tool/verify.py" name dasl drisl sha256 /tmp/silmaril-title.cbor
```

Passing an output path to `check.sh` optionally runs the Lean writer; the
separate external `name` command can hash that output to compare to the
manifest. Direct naming is a runtime facility: the assurance TCB is the
script and the exact input/output bytes,
Python and its SHA-256 implementation, `b3sum` from `PATH` for BLAKE3, and
their runtime/OS. For bytes produced by the Lean executable, its compiled
writer/runtime must also behave as intended; the small kernel serialization
witness is independent of that execution. Use a controlled `PATH` and retain
the manifest/tool versions when relying on an external verification receipt.
There is no receipt-to-proof coercion, no trusted elaborator and no native
proof tactic. An imported row can prove table membership even if its digest
is entirely false. Binding does not imply reverse uniqueness or cryptographic
collision freedom. For example, BDASL permits multiple algorithms for the
same raw bytes unless the naming profile fixes one.

The benchmark uses materialized synthetic tables with four-byte,
shared-prefix keys (not full CIDs). Kernel `#reduce` checks the last 16 hits
and 16 misses; wall time includes the Lean process and imported fixture.
`lean --run` uses Lean's compiled VM, not an AOT native executable; the
timed loop checks the same queries and verifies its checksum. Construction
and import-only time are reported separately. These are lookup experiments,
not end-to-end measurements of CID import, hashing, or parsing. Neither this
benchmark nor the external tool is a new mandatory CI hook. To reproduce:

```sh
LEAN_PATH=. lake env python3 -I tools/verification-projects/artifact-naming/bench.py
```

One local run with the pinned Lean 4.37 nightly (median of three):

| Rows | Kernel wall: radix / linear (32 queries) | Compiled VM: radix / linear (8,192 queries) |
| ---: | ---: | ---: |
| 64 | 497 / 734 ms | 49 / 211 ms |
| 256 | 434 / 1,603 ms | 50 / 793 ms |
| 1,024 | 434 / 5,114 ms | 57 / 3,065 ms |

Import-only wall time was about 320 ms; fixture elaboration grew from
439 ms to 1,490 ms. Last-hit/miss probes favor an index; these results do
not claim a throughput ratio across evaluation engines or for other workloads.
