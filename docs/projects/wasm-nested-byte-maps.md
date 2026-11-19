# Validating nested Wasm instruction/body-byte maps

`Wasm.Region.ByteMap.Nested` validates candidate maps throughout structured
function bodies. It extends the [root byte-map checker](region-adapters.md)
without replacing the existing Wasm CFG extractor or operational semantics.
The candidate supplies byte spans and a source-ancestry spine; acceptance yields
a `ValidatedByteMap` and the original Core binary grammar certificate for the
whole function body.

## Coordinates and source ancestry

A `DecodedLabel` contains the module function index, a CFG sequence path and an
instruction offset within that sequence. Function indices include imports.
Each sequence-path step is **segment index and arm**, following the existing
`Cfg.Machine.seqAt` and `Cfg.armOf`. It is not the opening instruction's index.
A raw label is a byte offset within the encoded function body, including locals,
not a module/file offset. The map retains those distinctions.

`Frame` records the segment index, opening instruction index, source span,
selected arm and candidate `Layout`. Its checks establish:

1. The entire instruction slice decodes to the claimed instruction. The source
   prefix decodes to exactly the preceding instructions, so repeated identical
   instructions cannot silently choose another occurrence.
2. The existing canonical segmentation places this instruction at the selected
   segment's terminator. Equality of the preceding instructions pins its position
   even when equal structured instructions occur more than once.
3. The parent instruction's actual source bytes equal its opcode, validated
   source header, arm bytes and delimiters. Block types and `try_table` catches
   are parsed, not assigned guessed encoding lengths.
4. Child ranges start after the actual header, and after the preceding arm and
   `else` delimiter when applicable. Their source bytes decode to the selected
   child sequence; their bounds and `Cfg.Machine.seqAt` lookup are checked.

The supported structured forms are `block`, `loop`, both `if` arms and
`try_table`. Headers and arm bytes are source bytes, not canonical re-encodings;
valid nonminimal LEB encodings remain subject to the existing decoder's policy.
An absent encoded `else` is different from an explicitly encoded empty else.
The former has no second byte interval; `child?` returns `none` for that request.
Empty sequences and `end`/`else` delimiters are never instruction rows.

A `Sequence` stores path, half-open source range and decoded body. `Located`
records the checked source ancestry from the original body. `follow?` validates
a finite candidate spine, one parent at a time, and fails on unknown or invalid
paths. It also checks child grammar, bounds and CFG lookup independently; the
implementation prioritizes auditable rejection and evidence over eliminating
redundant parses. This is a checker for candidate witnesses, not an automatic
byte-position producer.

`DecodesAt` records a located sequence, the exact decoded function/path/index,
source prefix encoding and the Core grammar encoding of the instruction's
actual slice. `located_lookup` recovers its sequence's existing CFG lookup;
`candidate_sound` establishes this meaning from successful checks and whole-body
validation. An isolated slice that merely decodes to an equal instruction is
insufficient without the enclosing source ancestry.

## Tables and coverage

`TableChecks` validates each candidate and requires functional decoded-to-byte
and byte-start-to-decoded mappings. Structured parent spans may contain nested
child spans: this is expected overlap, not a uniqueness failure. Distinct
instruction identities still have distinct byte starts. The certified table
uses the existing `ValidatedByteMap`, including its partial `raw?` query.
Absent rows remain unknown.

`validate?` requires the original `Input.BodyChecks`, including the exact locals
vector, complete expression parse and expanded-locals bound. It returns the
caller's entries with proof fields, or `none`; `validate_entries` proves the
output-entry identity. `validate_certify` characterizes successful construction.
The generic full-slice parser, instruction and sequence encoding lemmas are
exposed by the existing root checker's public theorem header and reused here.

Coverage is separate from correctness. `Covered labels candidates` checks a
chosen finite inventory; an empty valid map establishes no coverage.
`inventory input` reuses **`Cfg.blocks input.body`** and `seqAt`: every
instruction position in every represented sequence is included, with duplicate
paths harmless. `cfg_coverage_sound` proves that a validated table covering
this inventory supplies an actual encoded byte row for every instruction of
every sequence named by an extracted CFG block. It does not infer execution,
reachability, type correctness, or module validation from binary decoding.

## Checked fixtures

Four deterministic bodies cover the principal source-layout cases:

| Fixture | Layout | Listed instructions / nested positions |
| --- | --- | --- |
| `nested` | block containing loop containing NOP | 3 / 2 |
| `conditional` | if with identical NOPs in both arms | 3 / 2 |
| `handler` | try_table with empty catch vector and NOP body | 2 / 1 |
| `prefixed` | NOP before a block opener, making instruction and segment indices differ | 3 / 1 |

All four tables are accepted and cover the reused CFG inventory: **11 listed
instruction positions, six nested**. `fixture_counts` verifies those denominators.
These are source fixtures, not module-corpus measurements. A fifth negative
layout checks that an absent else interval is not invented. Further negatives
reject exchanging identical opposite-arm NOP offsets, shifting into a header,
wrong segment index, missing parent ancestry, delimiters as instructions and
wrong function identity. `nested_instruction_sound` is a concrete grammar and
source-ancestry theorem for the two-level nested NOP.
The public validator also rejects a swapped-arm table, and accepts an empty
table while its CFG coverage check fails, demonstrating the partial-map policy.

## Verification and limits

```sh
lake build --wfail Silmaril.Wasm.Region.ByteMap.Nested.Examples.Thms
make check CHECK_TARGETS=Silmaril.Wasm.Region.ByteMap.Nested.Examples.Thms
```

The map handles encoded instruction locations, not synthetic CFG return/trap/
raise/invalid targets. There are no source instructions at synthetic exits.
Imported functions have no encoded body here. A caller must bind `Input.bytes`
to the intended module's selected code-body bytes and its import-adjusted
function index; the whole-module code-section offset/provenance bridge is
separate. Candidate generation, corpus-wide coverage, decoder completeness and
uniqueness of every possible binary spelling are not established.

The existing region operational coverage theorem retains its own profile,
call-interface, frame, lookup/support and outward-target assumptions. This map
does not discharge those assumptions, justify call resumptions or upgrade
unresolved targets to finite closed regions. The abstract region-law lattices
are unchanged; source certificates and partial extraction helpers are a
separate interpretation layer.

[Module provenance and automatic production](wasm-module-byte-maps.md) add
checked whole-module framing, import-adjusted body identities, module byte
coordinates and a producer which still requires nested validation and coverage.
