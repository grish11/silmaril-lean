# Module provenance and automatic Wasm byte maps

`Wasm.Region.ByteMap.ModuleSource` binds a body map to its original complete
module bytes. `ByteMap.Produce` automatically proposes source framing, locals
boundaries, instruction spans and nested ancestry spines, then applies the
existing decoder and [nested-map checker](wasm-nested-byte-maps.md). The generic
region lattice and operational semantics remain independent of extraction.

## What successful source checking establishes

`ModuleSource.Layout` is candidate data: source section IDs, original size-LEB
bytes and payloads, the code-section index, its vector-count bytes and the
ordered code bodies with their original size prefixes. No re-encoding assigns
positions. `validate?` obtains the module from `Binary.Core.decode?` on the
same complete source bytes and checks:

1. Exact source decomposition into magic/version and the section frames, with
   every size prefix parsed as the actual payload length and exactly one code
   section selected by ID 10. Custom-section contents cannot supply code bodies.
2. Exact decomposition of that code payload into its original vector prefix
   and body entries. The existing `readVec readCode` parses it to exactly the
   defined module functions' locals and bodies, in definition order.
3. The vector count and body count equal the number of defined functions.
   Every size prefix equals its body's byte length; each body independently
   passes the original locals/expression grammar and bounds checks.
4. Every local definition `i` has function identity
   `module.importedFunctions.length + i`. Global, memory, table and tag imports
   do not increment the function index space. Imported functions have no source
   body in this table.
5. Every body's computed module offset reads exactly its original bytes, lies
   inside the complete source and agrees with its parsed locals and expression.

The redundant source-slice checks are deliberate: the coordinate bridge is
explicitly verified, independently of the heuristic that computed it.
`Certified.encoding` is the existing Core whole-module grammar certificate.
`source_framing` exposes the exact source decomposition; `code_section` proves
that the selected frame is a Core `CodeSec` encoding, with exactly the decoded
defined-function bodies. `function_body`, `function_index`, `index_bound` and
`body_bytes` give the binding and coordinates individually.

The module byte offset `Layout.bodyStart i` points to the body's locals-vector
prefix, **after** its size prefix. Nested instruction ranges are half-open and
relative to that body; adding `bodyStart` translates them to module/file byte
offsets. `MappedModule.absolute_slice` proves this translation for every mapped
instruction. `instruction_source` gives the existing instruction grammar on
those actual original module bytes, retaining its CFG sequence path and
import-adjusted function index. It does not identify body, module, runtime
address or synthetic-exit coordinates.

## Automatic candidate production and acceptance

The producer runs existing parsers at source cursors. Section lengths select
payload slices; code-vector and body prefixes select definitions. Locals parsing
locates the instruction sequence. `readOne` supplies each instruction span;
`readBlockType`, `readCatch` and `readSeq` locate the structured headers, arms
and actual end/else delimiters. The existing canonical CFG segmentation selects
the opening segment index. Block, loop, both if arms and try_table reuse the
nested checker's source-ancestry rules. An absent else has no invented interval.

Every generated table still passes `Nested.validate?`; `FullMap` additionally
carries checked coverage of the reused CFG inventory. `module?` returns a
`MappedModule` only with a source certificate and a full map for **every** defined
body. This is checked acceptance, not a completeness theorem for the producer.
Fuel is bounded by source length; unknown forms, parsing failures, failed
source/spine/uniqueness checks and incomplete coverage return `none`.
A module with no code section is currently an unsupported/empty-module case
for this body adapter, also `none`; failure never means no functions or empty
successor allowances. An explicit empty code section can have zero body maps.

`FullMap.cfg_coverage` preserves the existing block-membership and sequence
lookup premises. Coverage here is over distinct `DecodedLabel` positions of
`Nested.inventory`: every instruction position in every sequence named by the
actual extracted CFG blocks, with repeated inventory positions deduplicated.
A CFG lookup/operational adequacy theorem, reachability and type validation
remain separate. No synthetic return/trap/raise/invalid CFG target has a source
instruction row. Unresolved branches and calls acquire locations, not invented
finite targets or justified resumptions.

## Kernel examples and measured corpus

The kernel-checked source fixtures include two identical nested function bodies
with **one function import plus one global import**, and a custom section
containing a decoy copy of the same body. The automatic maps give function
indices 1 and 2 at module body offsets 47 and 57, with three rows each.
Other fixtures exercise identical if arms, try_table, an opener whose instruction
index differs from its CFG segment index, and an absent encoded else. Five
source modules contain six defined bodies and 16 mapped instruction positions.
Separate examples reject truncation, wrong import-adjusted identity, selecting
the custom decoy as code, and the no-code-section case.

The native report was run over exactly these seven checked-in fixtures, after
`scripts/check-wasm-checkers.py` verified their pinned bytes. The report executes
the same checked API, but it is **native measurement evidence**, not seven new
kernel theorem declarations over included files. The hash/policy manifest is
checked by that script; the file paths below define this measurement corpus.

| Fixture | Module bytes | Defined bodies / full maps | Distinct CFG inventory positions / mapped |
| --- | ---: | ---: | ---: |
| `examples/wasm-checkers/lrat.wasm` | 1812 | 10 / 10 | 802 / 802 |
| `examples/wasm-checkers/farkas.wasm` | 372 | 3 / 3 | 121 / 121 |
| `examples/wasm-acceptors/member_check.wasm` | 108 | 1 / 1 | 35 / 35 |
| `examples/wasm-acceptors/empty_check.wasm` | 45 | 1 / 1 | 1 / 1 |
| `examples/wasm-demos/rust-adder/wasm/adder.wasm` | 124 | 4 / 4 | 17 / 17 |
| `examples/wasm-demos/c-adder/wasm/adder.wasm` | 192 | 6 / 6 | 35 / 35 |
| `examples/wasm-demos/as-adder/wasm/adder.wasm` | 113 | 4 / 4 | 17 / 17 |
| **Total** | **2766** | **29 / 29** | **1028 / 1028** |

All seven modules source-checked. All have zero imported functions; import
indexing is tested by the separate kernel fixture. No other module corpus or
complete-decoder success rate is claimed. Rows at structured parent spans may
contain child spans; uniqueness concerns instruction identity and byte starts,
not disjoint byte intervals.

## Check and reproduce

```sh
lake build --wfail Silmaril.Wasm.Region.ByteMap.Produce.Examples.Thms wasm-region-map
make check CHECK_TARGETS='Silmaril.Wasm.Region.ByteMap.Produce.Examples.Thms wasm-region-map'
scripts/wasm-region-map/corpus.sh > build/wasm-region-maps.json
```

The executable is included in the default check target set. The JSON report
records status, definition/function indices, module body offsets, body sizes,
coverage denominators and accepted counts. Failed bodies remain incomplete;
missing rows are unknown. It deliberately omits proof serialization.

The checker closes the source-body/function-index and automatic-candidate
obligations for accepted outputs. Remaining limits include general producer
completeness, the no-code-section case, broader corpus/profile coverage,
per-file kernel certificates for the measured corpus, validation/instantiation,
operational event and call-summary adequacy, and export into a viewer. Decoding
and byte-location coverage do not prove termination, trap freedom, ABI behavior
or a closed finite semantic region.
