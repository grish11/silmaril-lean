# Region adapters: operational coverage, byte placement and remaining gates

The [abstract lattice](region-lattices.md) and [tree relation](region-trees.md)
APIs remain independent of every adapter here. These optional interpretations
reuse existing semantics and parsers; they do not supply missing hardware
semantics or define a region as a partition into certified basic blocks.

## Wasm: operational coverage without a second CFG

`Silmaril.Wasm.Region.Operational.Thms` uses the existing
`Cfg.Machine.mstep_edgeC` theorem. With successful block lookup and the existing
frame invariant, every machine step follows a normal extracted edge, reaches
`trap`, follows an enclosing catch edge, or takes a call effect edge. The
adapter's `operational_step` covers all four. It neither rebuilds the CFG nor
changes the existing syntactic candidates.

The operational theorem has no typing premise, so every finite root allowance
also includes `trap`. Nested blocks currently use Top: a catch target can be
attached to an ancestor `try_table`, and it would be unsound to consult only
the throwing block's immediate adjacency. Calls and unresolved handlers retain
Top. A future finite refinement must prove catch coverage and, if it removes
traps, justify that from the chosen profile/typing/entry state assumptions.

`system` exposes the existing block machine to region semantic queries.
`operational_sound` proves first-exit soundness from an admitted frame
invariant, coverage of supported states by successful block lookups, and the
actual outward allowance condition. Invariant preservation is reused from
`mstep_invC`. Top always covers label targets; it cannot by itself establish
a finite closed region. This query view has an empty event alphabet: it
observes control and state, not a trace of effects inside an oracle call.
Synthetic `exit`, `trap` and `raise` are separate halts. An unanswered call can
be stuck rather than an invented resumption.

These are operational results for the existing block machine. Its public
`Cfg.Machine`/`Cfg.FunctionCfg`/`Cfg.BridgeCfg` headers already contain Core and
native adequacy results. Their fragment, profile and callee-adequacy premises
continue to apply. In particular `run_sound_initialC` reaches the existing
`RunC` relation without assuming a sound call oracle; Core soundness needs the
existing call-soundness premise, and Core completeness with arbitrary calls
is not supplied by this adapter. The host-free checked session layer has its
own restricted instance/profile and rejects exceptions. None of these is a
claim of complete operational coverage for every Wasm extension.

## Wasm: checked instruction/body-byte maps

`Silmaril.Wasm.Region.ByteMap.Thms` supplies `validate?`, an executable
producer of proof-carrying maps from untrusted proposed tables. It checks:

- the actual locals prefix with the existing locals-vector decoder;
- the whole remaining source expression with the existing expression decoder;
- each nonempty bounded span with the existing instruction decoder, consuming
  the entire slice;
- the instruction prefix before the span against the first `instructionOffset`
  instructions of the decoded body;
- function identity, root path and both decoded/raw-start uniqueness.

The proofs use `Decode.readInstr_readSeq_sound`, `readExpr_sound`,
`readLocals_sound` and `readVec_sound`. `Certified.bodyEncoding` is the actual
Core binary `Func` relation for the source bytes, including locals and the end
delimiter. `map.correct` additionally certifies the instruction and its encoded
prefix. Bounds alone never validate a table. Source spellings accepted by the
existing decoder, including nonminimal LEBs, need not be canonical re-encodings.

Offsets are within `Bfunc`, **after the code-entry size prefix and including
the locals vector**. Root instruction indices count structured instructions
once; a block span includes its header, nested body and `end`. Prefix checking
prevents the second of two identical instructions from borrowing the first's
span. The delimiter is not an instruction. `Cfg.BlockId.idx` counts segments,
not instructions; it must not be substituted for `instructionOffset`.

This producer validates root paths only. Nested paths are rejected. It can
validate a partial table; absence remains unknown, and complete coverage must
be established separately before transporting an entire region to raw labels.
It does not extract bodies/function indices from a whole binary module or
produce candidate spans automatically. Those are untrusted front-end tasks;
the checker is the trust boundary. The syntax equality helper is total and
proved correct, including nested instruction lists and dependent constant
widths, rather than relying on an opaque partial derived comparator.

The benign kernel fixtures in `Wasm.Region.Examples.Thms` cover two accepted
tables (locals/repeated instructions and a structured block), and four rejected
proposals (wrong repeated occurrence, immediate byte, nested path, delimiter).
They are a six-case regression set, **not a measured Wasm corpus**.
Separate `RootCovered` theorems certify all 3/3 root positions in the repeated
fixture and 2/2 in the structured fixture: 5/5 root positions across these two
hand-authored bodies. There is one nested nop and no nested row (0/1); it is
excluded explicitly from the root denominator. `root_coverage_sound` connects
successful validation and this coverage witness to per-position grammar
certificates. Function index 7 is supplied by these fixtures, not extracted
from a linked module. General module/nested coverage remains a prerequisite.

## x86: ELF placement and calls

`Silmaril.Elf.Region.X86.Thms.parsed_window_loaded` proves that a bounded
executable window of the existing checked x86 ELF image meets
`Decompile.Region.LoadedIn`, provided the machine satisfies the repository's
byte-exact `Link.FnSpec.ImageLoaded` contract. This derives all subspan fetches,
including empty endpoint reads. The checked x86 task-size bound keeps those
endpoints strictly below the address limit. `placed_listing_step` then applies
the existing listing/Ext operational edge theorem directly.

This is a placement bridge, not a Linux-loader correctness theorem. Parsing
alone does not establish `ImageLoaded`. Windows of a loaded segment can include
loader-established zero fill; the separate file-backed mapping continues to
exclude it. Existing `ELFImage.segment_file_byte` and `segment_bss_byte` specify
file versus zero-tail identity. ET_REL section offsets are still distinct from
placed VAs; existing link validation supplies relocation/placement certificates,
and declarations of relocated calls are not semantic call proofs.

`Silmaril.Machine.Region.Calls.Thms` reuses `FnContract.Strict` over an explicit
`SegVC.Isa`. Under its live/ABI/entry preconditions, a real first return exists;
determinism and first-return uniqueness prove that **every** actual first
return meets the contract's ABI, write-frame and postcondition. Its PC is the
state's justified return address. An angelic total contract promising some
later returned state is insufficient for this theorem.

This adapter works with the existing open x86 contract machines. It does not
silently transfer Open/Ext8 contracts to the narrower Ext fetch language, nor
replace a call's instruction step with a summary edge. The Ext region adapter
therefore continues to use Top for CALL/RET. Turning a first-return summary
into a region first-exit theorem also requires a support invariant and proof
that no earlier boundary crossing occurs; a PC return label alone does not
establish stack/ABI return. Indirect/unresolved targets and unavailable callee
contracts remain unknown.

## Scope matrix and exact next prerequisites

| Deliverable | Implemented/proved | Remaining gate |
| --- | --- | --- |
| Fixed-signature segment/label/tree lattices | Raw and fixed-positive-rule closed complete lattices; ceilings and transport | Optional adapter-specific rule families need independent compatibility/ceiling proofs |
| Primitive trees and CFG relationships | Loss-aware projections, adjacency separate from dominance, witnessed finite dominance lifting | No unconditional unique CFG from region families or dominator inference from composition |
| Wasm CFG operational coverage | Step coverage and conditional semantic first-exit soundness, reusing existing machine | Finite nested allowances need an ancestor-handler coverage theorem; smaller trap sets need typing/profile proofs |
| Wasm byte map | Executable proof-carrying root-table validator, source `Func` and per-span grammar certificates | Nested delimiter/path location theorem; module/body extraction and function-index binding; automatic span proposal and general nested-table coverage (fixture roots have explicit coverage proofs) |
| CFG block to instruction/byte coordinates | Coordinate distinction and validated instruction rows | Prove block-segmentation prefix lengths correspond to instruction indices, then compose with complete nested maps |
| Wasm Core/native coverage | Existing public adequacy reused with its actual hypotheses | Arbitrary-call Core completeness needs callee adequacy; all-extension coverage is not established |
| x86 direct subset | Existing actual Ext listing proof and loaded direct-jump fixture | Wider hardware semantics remain outside handwritten Ext; decode rejection remains a distinguished halt |
| ELF placement | Checked-image executable windows imply actual listing fetch contract | Concrete workload must prove parse, image membership, placement/loading and code preservation; no whole-executable corpus run here |
| x86 call summaries | Strict first-return results/labels/frame under existing contract semantics | Actual callee contract, ABI admission, appropriate machine agreement and no earlier support crossing; unresolved calls stay Top |
| Corpus coverage | Seven-fixture x86 candidate classification; six Wasm checker cases | No repository-wide extraction corpus denominator or throughput claim; requires a selected corpus and executable exporter |
| Queries, Hoare/WP and gluing | Abstract semantic queries, partial/total rules and actual-edge wiring | Adapter-specific effect traces, syscall/foreign/UB policies beyond these chosen machines remain separate obligations |

## Scoped verification

Use the pinned toolchain, without changing dependency revisions:

```sh
lake build --wfail Silmaril.Wasm.Region.Examples.Thms \
  Silmaril.Elf.Region.X86.Thms Silmaril.Machine.Region.Calls.Thms
```

Pass these targets and any additional affected region roots as `CHECK_TARGETS`
to `make check` for
source, layout, browser-unit and offline process gates as well. Targeted local
success is not a claim that the full native release suite was run locally.
CI evaluates correctness and timing separately; passing either check does
not establish that the other passed.

The [nested Wasm map guide](wasm-nested-byte-maps.md) describes candidate-spine
validation for block, loop, if and try_table bodies, including coverage against
the existing CFG inventory. The original root checker remains a smaller API;
module/body provenance and operational assumptions remain separate.
