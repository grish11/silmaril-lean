# Bao and Iroh range proofs

`Silmaril.Formats.Bao.Thms` and `Silmaril.Formats.Iroh.Thms` specify different
proof formats over the same unkeyed BLAKE3 tree geometry. They do not import a
concrete compression/CV, naming or CAS implementation. `HashOps` is the
integration boundary: root output and non-root CVs are distinct domains, and
subtree hashing takes the absolute chunk counter (including for grouped data).

## Source pins

- [Official Bao spec](https://github.com/oconnor663/bao/blob/19763d70a5bda9402cc37a63e823cd7b9aa7f777/docs/spec.md#L20-L136)
  and [reference decoder](https://github.com/oconnor663/bao/blob/19763d70a5bda9402cc37a63e823cd7b9aa7f777/src/decode.rs),
  revision `19763d70a5bda9402cc37a63e823cd7b9aa7f777`.
- iroh-blobs revision `b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b`:
  [Get](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/src/protocol.rs),
  [range specs](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/src/protocol/range_spec.rs),
  [provider](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/src/provider.rs),
  [response FSM](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/src/get.rs),
  [16 KiB block size](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/src/store/mod.rs),
  [HashSeq](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/src/hashseq.rs),
  [CollectionV0](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/src/format/collection.rs).
- That revision's [Cargo.lock](https://github.com/n0-computer/iroh-blobs/blob/b798eea75b9fdfce3d35c28b6213a67f8c9d8a3b/Cargo.lock)
  pins [bao-tree 0.17.0](https://docs.rs/crate/bao-tree/0.17.0/source/) (registry SHA-256
  `50d0e17303b78c9bb240014f3f401ecae5c0460438ace49a171e5f97e3ae57ba`,
  `.cargo_vcs_info.json` commit `67691dfbd36538730c7e7402f013259205f76fcf`).
  Relevant source: [`rec.rs`](https://docs.rs/crate/bao-tree/0.17.0/source/src/rec.rs),
  [`iter.rs`](https://docs.rs/crate/bao-tree/0.17.0/source/src/iter.rs),
  [`outboard.rs`](https://docs.rs/crate/bao-tree/0.17.0/source/src/io/outboard.rs).
  The vector generator also uses the locked BLAKE3 `1.8.7`.

## Modeled formats

| Format | Claimed size | Body |
| --- | --- | --- |
| Bao combined | LE64 prefix | Preorder, 64-byte CV pairs and inline 1024-byte chunks (possibly short final chunk) |
| Bao outboard | LE64 prefix | Same preorder pairs, payload in a separate original-data input |
| Bao slice | LE64 prefix | Selected paths and entire visited chunks inline; the byte request is external |
| Iroh portable preorder/postorder outboard | LE64 prefix/suffix | Pairs above 16-chunk groups, traversed in the named order |
| Iroh memory outboard | External | Same pair bytes, with external size, profile and root |
| Iroh Get response | LE64 prefix per blob | Preorder proof; fully selected subtrees of up to 16 chunks collapse into one data event, partial groups can split to individual chunks |

Bao permits a zero-byte slice (which still proves one chunk) and selects the
right edge for a start at or beyond EOF. `requestedBytes` projects only the
requested bytes from a checked data event; an empty projection is not an EOF
claim. `strictBounds` is a separate policy, not the permissive default. Iroh
uses normalized *chunk* ranges, including open ranges and an empty selection;
an out-of-bounds selected chunk requests the final chunk. `endProbe` is Iroh's
open range starting at `u64::MAX`. A selected empty blob has one zero-byte
data event; an unselected blob has no scheduled transfer. Counts and offsets
use `Nat` arithmetic; a wire u64 is range-checked or read at its defined width.

`readGet` parses one canonical Postcard Get message (variant zero, 32-byte
hash, vector of run deltas and alternating chunk-width vectors). `transfers`
uses blob offset zero for the root, then `HashSeq[offset - 1]` for children,
skips empty range sets, and stops at the end of the supplied sequence. The
caller must authenticate the HashSeq before using its child IDs. CollectionV0
has a metadata link first; `collectionItems` joins UTF-8 names to subsequent
links and rejects a count mismatch. It assumes the caller already authenticated
both metadata and link bytes. The codec works on delimited messages, not the
QUIC request read limit, stream resets, ALPN negotiation, or provider errors.

## Checked claims and trust boundary

- `readSlots_spec` and `readFrame_spec` connect bytes to a width-checked
  reference tape. Bao `decode_spec` covers all three variants, including exact
  proof exhaustion. For Iroh, `readResponse_spec` leaves the next blob's bytes
  untouched; `readMemory_spec`, `readHeader_spec` and `readTrailer_spec`
  characterize the portable outboards. The length and feasibility checks in
  these relations are framing checks, not authentication.
- `coverage_at` supplies a data slot for each selected chunk within the
  tree; `selected_of_data` proves that every chunk in an emitted data slot was
  selected. `outboard_order` proves a permutation of coordinates, and
  `outboard_sublist` proves the Iroh preorder pair schedule is a subsequence
  of official Bao's. Executable projection/reordering requires the encoded
  pairs by coordinate; interleaving a Bao outboard also requires the original
  bytes. Iroh-to-Bao expansion is not a conversion on portable bytes alone.
  `detach_spec` converts the tape to a detached multiproof indexed by its
  slots, each carrying a fixed-width byte vector. It does not certify the root.
- `release_checked` proves that after any successful prefix of steps, every
  internal event has a checked path from the expected root **at the claimed
  geometry**. `rightEdgeClaim` is present exactly when a checked data event
  reaches the claimed right edge. It is not itself a kernel EOF certificate.
  `finished` is a separate predicate: all scheduled fields consumed, no
  leftover bytes, and the enclosing framer reports end. A good prefix can
  precede truncation or a bad proof. A finished interior slice can have no
  length witness. The state and plan are internal inputs to this guarantee;
  start the session from the decoded claim, request and trusted root.

**Length audit.** On 2049 zero bytes, pinned Bao's slice decoder for byte
1024 accepts the original proof with the header changed to 2050, 3072 or
3073; shrinking it to 2048 changes the path and fails. On 2050 zero bytes,
the same interior request also verifies with the header shrunk to 2049.
Changing the 2049-byte vector's final-chunk proof to 2050 or 3073 instead
truncates. The position of an authenticated interior byte is not evidence
for the total length. Bao's EOF guarantee needs the checked right edge,
including the zero-byte leaf for empty content. Iroh's size-header field is
likewise an untrusted claim even though the upstream FSM exposes it early.

The proof checks equality and provenance under the supplied operations; it
does **not** prove an arbitrary `HashOps` binds positions or lengths or that
it implements BLAKE3. In particular, the reference implementation's behavior
on the audit vectors is not a general cross-extent range theorem.

## Kernel handoff and release policy

The format modules do not depend on the drafts. The relevant interfaces are
in [PR #1583 at `94f0ce9`](https://github.com/hiloopai/silmaril-lean/pull/1583)
and its separate [EOF follow-up, PR #1586 at `ce7dcc0`](https://github.com/hiloopai/silmaril-lean/pull/1586).

1. Decode the Bao or Iroh frame to fields. For a Bao outboard, first supply
   original bytes to `fromOutboard .combined` (or `.slice`). For Iroh use the
   `readResponse` fields and that blob's `responsePlan`. For incremental
   checking, pass only complete fields from the prefix. `lowerPrefix` builds
   a grouped `Frontier`; `lowerPrefix_spec` rejects an opaque root or surplus
   fields and characterizes the result. Skipped/unread children carry the
   expected CV from their parent. A missing zero-byte root cell is different
   from a supplied zero-byte cell.
2. In a downstream adapter translate `Frontier.opaque` to `Opening.opaque`
   with `Blake3.loadWords (count := 8)` (little-endian words). Pass the root
   digest as bytes, not as a non-root CV. Map forks in the same order; map
   `Frontier.data span bytes` to `Blake3.disclose` of
   `Blake3.geometry span.first bytes.length`. This expands even an Iroh
   chunk group into kernel leaves at absolute chunk counters.
   `split_matches_byte_geometry` checks the parent split arithmetic; a
   general format-to-kernel refinement theorem is still separate work.
3. Call `Blake3.verifyRange?` with a resource-appropriate extent cap, the
   claim, and the exact absolute offset/count to stage. Only its returned
   `Checked` fragment becomes a `StagedRange`. `verifyRange?` rejects offsets
   outside the claim and does not accept an arbitrary `HashOps` result.
4. `releaseRanges` needs `ExtentEvidence` for the *same digest and claim*:
   an externally trusted extent or a `CheckedEOF` from `Blake3.verifyEOF?`.
   That can be from a separate Bao tail slice or Iroh `endProbe`; check the
   certificate again at the original claim, not at a different claimed
   extent. An independently verified EOF or trusted extent may permit
   release before wire completion, but cannot turn a truncated frame into a
   completed response. Without either, keep interior results staged.
5. Given an actual `Named` reference blob, instantiate `released_slice_or_collision`:
   for trusted extent supply equality with the reference length; otherwise
   use `CheckedEOF.extentOrCollision` from #1586, then
   `Checked.sliceOrCollision` from #1583 at equal extent. Alternatively use
   #1586's combined `Checked.sliceOrCollisionOfEOF`. The conclusion is a
   reference slice **or a compression collision**, not collision resistance
   or a guarantee that an object behind opaque CVs exists. In the CAS layer,
   `blake3_range_with_eof` supplies the reference from a compatible store hit.

No theorem here releases data for an arbitrary reference extent from a
range opening without a matching extent proof. Concrete refinement of every
accepted wire frame and equivalence to the upstream Rust parsers/iterators
remain follow-up work. The Lean codec is an in-memory reference, not a
resource-bounded network implementation. No keyed/derive-key profiles,
database/partial-storage internals, discovery, replication, alternate RPCs,
textual identifiers, or transport are formalized.

## Checks and vectors

```sh
lake build --wfail +Silmaril.Formats.Bao.Thms +Silmaril.Formats.Iroh.Thms +Silmaril.Formats.Iroh.Vectors
scripts/check-layout.sh
make check
```

`Vectors.lean` checks concrete BLAKE3 pair bytes and frame order supplied by
the pinned reference implementations; its authentication fixture is a
lookup for known test inputs, not a second implementation of BLAKE3. The
official oracle uses `encode`, `outboard`, `SliceExtractor` and `SliceDecoder`
on 2049 zero bytes. The Iroh oracle uses `PreOrderMemOutboard`,
`PostOrderMemOutboard`, and `encode_ranges_validated` with `BlockSize` log 4
on 32769 zero bytes. Canonical Get vectors are from the upstream protocol
test. A separate differential run matched 1232 Iroh responses and 44
Bao-to-Iroh outboard projections byte-for-byte over 22 sizes. Selected
artifact hashes (SHA-256 over exact bytes):

| Vector | Bytes | SHA-256 |
| --- | ---: | --- |
| Bao combined | 2185 | `8dc468b0d4de734c9e00b77620a9777fee825a10c39f51e3dd3a3b94318fc239` |
| Bao outboard | 136 | `e5507e4ae23dc66a07e43464316d176e22273b69082e1cd95888a74df93bb378` |
| Bao interior (start 1024, count 1) | 1160 | `4b30f17596fa7d3be54c0306bf72c0fb2a2119697d1e1d3a969bf201170a22b7` |
| Bao right edge (start 2048, count 1) | 73 | `de73f308b544a47056d8ff41a616bdc2bb5f74ded4f816a91066c23cc9746760` |
| Iroh preorder outboard | 136 | `90817efba4be8425e9b04e3655574a3b98fe832388761bad9687fb0fba759a5e` |
| Iroh postorder outboard | 136 | `fef7a3ade37a5c2e68834c441e6961d5c00d4274c359c25c00a94118dd100c1d` |
| Iroh Get response (all) | 32905 | `2f82f6cacf840b4cc870e90d641621f4a2a7e64a588c8470876763bb51bef316` |
| Iroh Get response (chunks 1..2) | 1416 | `94ba46a60016733b854d78b36dee379ae0b5c89d833425f2b21f5a81d4c91829` |
