# Checked BLAKE3 wire ranges for CAS

`Silmaril.Formats.Blake3Cas.Thms` integrates the [range/extent kernel](blake3-range-kernel.md)
with the [Bao and Iroh wire profiles](bao-iroh.md). `Silmaril.Containers.Cas.Blake3Wire.Thms`
adds store-level corollaries. The underlying formats and kernel do not depend on the integration.

## Acceptance and provenance

| Entry point | Input and accepted evidence |
| --- | --- |
| `checkBaoInline? .combined` | Official Bao LE64 header and combined preorder proof/data fields. |
| `checkBaoInline? (.slice request)` | Official Bao slice bytes; the byte request is external. |
| `checkBaoOutboard?` | Official Bao outboard plus the full separate original payload. The accepted pair projection equals the raw outboard body; the data projection equals the supplied original bytes, with slice equality at each accepted offset. |
| `checkIrohRawGet?` | Canonical raw single-blob Get request bytes and one strict response frame. The request must target offset zero only (`[(0, query), (1, [])]`), and its hash must equal the independently expected digest. |

Each accepts an expected digest and a local extent cap. The cap is checked before
constructing the format plan or kernel shape. `HeaderBinds` gives literal equality
between the raw input and the eight raw header bytes followed by the accepted body.
The Iroh result also retains `readGet` success and exact canonical request bytes.
Each accepted parent cell is indexed by its raw 64 bytes; the two parsed CVs
serialize back to those bytes, in order. Each accepted data cell carries a kernel
`Checked` proposition for those very bytes at its checked byte coordinate.

All four paths use `step?`. `parentCV` uses `parentInput` with the actual ROOT or
non-ROOT flag. `subtreeCV?` uses the scalar `compress32` evaluator on the reached
kernel `Shape`: absolute chunk indices and 1 KiB BLAKE3 leaves are unchanged. An
Iroh plan can group up to 16 chunks into one data cell or subdivide a partially
selected group; even a short group at EOF is hashed through the original kernel
leaves. `canonicalSpan` identifies the span of the canonical kernel geometry.
Each accepted cell carries `Aligned` and an `Anchor` to the canonical root.
Plan spans, byte starts and data widths are checked against that reached
shape. This is an acceptance check, not a theorem that every upstream-produced
schedule is modeled or accepted.

## Extent and incremental release

- `CompleteBody.trustedRange?` requires the scheduled extent to match a caller's
  trusted extent. An interior opening does not authenticate the header.
- `CompleteBody.verifiedRange?` requires `CheckedEOF` for the same root and extent.
  Only a checked data opening on the canonical right edge supplies it. For a
  grouped final field this opens the true final chunk; an empty object still
  has its authenticated zero-byte root chunk. Alternatively, use a `CheckedEOF`
  from a separate opening with the same digest and extent.
- `ExactRange.soundTrusted` and `ExactRange.soundEOF` turn accepted evidence into
  a naming fact or a concrete collision against a supplied actually named payload.
  The `Store.blake3_wire_*` corollaries take a compatible store hit as the named
  reference. The collision is distinct actual compression inputs with equal
  output words 0–7, not an injectivity assumption or a collision in all 512 bits.
  An opaque CV does not establish that a full payload exists.
- Abstract incremental state is `(Session, cursor)` for a fixed expected digest,
  claimed extent, plan and requested contiguous byte window. Start the cursor at
  the requested offset, then thread the `readRangeStep?` continuation. `Prefix.wire`
  identifies the consumed prefix of the actual raw bytes. `Advance.releasedPosition`
  and `Coverage.exactLength` give adjacent, positive emitted spans with exact
  offsets and no gaps or overlaps; cells outside the requested window do not
  advance the cursor. The window may be narrower than the wire's disclosed chunks.
- A checked prefix is independent of any later truncation, malformed cell or
  failure to complete. `RangeStep.trustedSpan?` uses independently trusted extent;
  `RangeStep.verifiedSpan?` requires a separately available or subsequently obtained
  `CheckedEOF`. The respective `releasedTrusted`/`releasedEOF` soundness theorems
  use these conditions. With neither, retain only the extent-relative `Checked` fact:
  do not release it as an arbitrary-object CAS slice. `Prefix.completed` separately
  requires an external frame boundary, no unconsumed bytes or scheduled cells,
  and the exact requested final offset. Completion does not supply EOF.

The outer wrappers buffer entire frames; outboard reinterleaving is eager. The
single-cell reference step has a prebuilt plan and kernel geometry, and takes
already available list bytes; it is not a socket parser, backpressure mechanism,
or resource-bound proof. The range result is one exact in-bounds contiguous byte
window; disjoint raw chunk queries are not a disjoint-range release API. Portable
Iroh outboards, HashSeq/Collection transfers, alternate request encodings and
transport are outside this integration. No production-library equivalence or
Rust verifier/refinement is claimed.

## Pinned inputs and checks

- [Kernel #1583](https://github.com/hiloopai/silmaril-lean/pull/1583):
  `94f0ce9cbb0ac133bc69e464b562f75c8d0a096d`.
- [Extent #1586](https://github.com/hiloopai/silmaril-lean/pull/1586), stacked on that kernel:
  `ce7dcc055af67e2498233f123ff2cc63afeed544`.
- [Formats #1587](https://github.com/hiloopai/silmaril-lean/pull/1587):
  `cd86b0153a91a0eff616a54d64fda61ba984c323`. The integrated step consumes the
  format's plan and byte fields directly; it does not depend on the generic
  callback checker, `rightEdgeClaim`, or a second pass through `lowerPrefix`.

Run the scoped warning-as-error build, executable regressions and axiom audit:

```sh
lake build --wfail +Silmaril.Containers.Cas.Blake3Wire.Thms +Silmaril.Formats.Iroh.Vectors
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/Blake3Cas.lean
scripts/check-layout.sh
```

The regression runs the recorded official and Iroh oracle fields from
[`Vectors.lean`](../../Silmaril/Formats/Iroh/Vectors.lean) through the concrete
kernel (not its format-only fixture callbacks). It also checks a new short
multi-chunk final group: for `byte[i] = i mod 251` and length 17,409, create a
`PreOrderMemOutboard` with chunk log 4, encode chunk range `16..` with
`encode_ranges_validated`, and prepend the LE64 extent. The pinned `bao-tree`
0.17.0 / BLAKE3 1.8.7 oracle yields a 1,097-byte response with SHA-256
`7a0f8b724986912fe626f4d688b6f460d11ea35c7358efacb0af9cf03594d430`.
The regressions distinguish failing malformed, substituted, reordered, truncated
and padded false-edge frames from interior false claims that still authenticate
an extent-relative prefix but do not prove EOF.
