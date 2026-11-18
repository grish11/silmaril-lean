# Decoder graphs and machine rebasing

[`DecodeGraph`](../../Silmaril/Machine/DecodeGraph/Defs.lean) is a success-only
interface for instruction and block decoders. A query is `(context, bytes)`;
an outcome is `(value, count)`. The count identifies the exact consumed prefix
and the remaining suffix. Put mode, address or other query parameters in the
context rather than mixing outcomes from different modes. The existing
[`Machine.Decoder`](../../Silmaril/Machine/Decoder.lean) remains the executable
codec interface; `ofDecoder` does not change any decoder, and `successes` can
also forget errors from an `Except`-valued decoder. Those errors are not merged
by the graph, nor equated with architectural faults.

## Order and composition

- The ambient complete lattice is Mathlib's `SetRel` (a set of pairs): join is
  union and meet is intersection. Bounds, positive consumption, prefix
  locality, determinism and completeness relative to a specified relation are
  independent contracts. `not_deterministic_sup` shows that different successful
  results at the same query survive a join, even when each decoder on its own
  is deterministic. This includes disagreement on length alone.
- `transport` postcomposes with an arbitrary relation on values while keeping
  the consumed span; `map` specializes it to a function. `pointwise` lifts an
  instruction relation via `List.Forall₂`, with an append law. A relation on
  **whole lists** uses the same transport and composition, without any
  equal-length or append assumption. If independent chunks do not agree on an
  intermediate segmentation, a chunk-wise composition rule cannot be inferred
  from ordinary relational composition.
- Types and relations have identities and associative composition. A directed
  comparison `R ⊆ R'` is a 2-cell between parallel relations with the same
  input and output types. `rebase_mono` composes two such comparisons
  horizontally: `A ⊆ A'` and `M ⊆ M'` give `A ○ M ⊆ A' ○ M'`.
  `rebase_interchange` checks that horizontally composing the vertical chains
  gives the same inclusion as vertically composing the horizontal pairs.
  These are checked concrete Lean laws, not a bundled Mathlib 2-category
  instance: horizontal composition uses Mathlib's `SetRel.comp_subset_comp`
  and interchange uses proof irrelevance of inclusions. For a fixed query
  context, the laws make graph
  transport covariant and observed-machine rebasing contravariant on arrows
  (and both monotone on 2-cells), taking graphs into their inclusion posets. A
  sound map from one decoder to another is the inclusion of the transported
  graph in the target graph; identities and composites follow from those same
  laws. No second category hierarchy is introduced.

## Entry, exit and observations

`blocks` is a bounded witness, not an executable parser or CFG. The caller
supplies entry (a natural byte address), the bytes starting there, and a
terminator predicate independent of semantic execution. `Path` requires
positive, in-bounds consumption at every instruction, advances the address and
suffix together, and closes only at the first terminator on that path. The exit
*byte boundary* is entry plus total count, not the successor PC. No synthetic
terminator, resynchronization, partial block, or empty block is emitted for a
truncated, undecodable, or fuel-exhausted path. End-of-input is not itself a
terminator, unlike the straight-line `Decoder.decodeAll` policy. A valid block
may leave a nonempty suffix. `path_bounds` checks nonemptiness, fuel and byte
bounds; `blocks_deterministic` lifts determinism through a fixed boundary
policy. The caller is responsible for any architectural address arithmetic,
memory assumptions, or semantic significance of the end predicate.

`rebase adapter model` pulls back an observed execution relation on a common
base. Comparing two models by observation inclusion on that base implies
inclusion after rebasing along the same adapter, and successive rebases compose.
An input with no witness has no observations (so inclusion can be vacuous).
`dom_rebase_of_covered` gives exact availability on the adapter domain when
every possible witness admits some observation. Multiple witnesses contribute
the union of their observations; acceptance by some witness is not a must
guarantee. For an ambiguity-independent answer require agreement of the
observation sets at all related base inputs, or an independently justified
unique witness. To use an existing [`Behaviour.Semantics`](../../Silmaril/Machine/Behaviour/Semantics.lean),
take its `Beh` as the observation relation: labeled divergence, UB or faults
are copied unchanged along a witness, but the construction neither creates
these labels from decode failure nor proves that execution on bytes has the
same behaviors. It does not turn whole blocks into small-step semantics.

The [checked x86 example](../../Silmaril/Proofs/Machine/DecodeGraph/X86Example.lean)
uses the existing `X86.Insn.byteDecoder`. At entry 16, `41 50 c3 cc` decodes as
`push r8; ret`, consumes three bytes and leaves `cc`. A truncated `41` has no
block. The toy semantics counts ordinary instructions and observes a return
tag; it does not execute a real push, access the stack, or compute a return
address. Its two-instruction listing relates to a singleton abstract block;
the checked rebases admit the observation at both list and byte inputs.

## Directed comparison with the executable decoder

`blocks_subset_sequentialPrefixes` proves a comparison for **all** contexts,
bytes, fuel and successful results of the factored block decoder built from a
`Machine.Decoder`. On the prefix of the claimed length, the unchanged
`Decoder.decodeBlock` returns a listing with the same instructions after
erasing its offsets. The proof uses prefix locality and the executable's
recursive decode, not equality by wrapping the same implementation.

The x86 example checks the direction is strict: the legacy decoder also accepts
the two-byte `push r8` prefix with no terminator, which the factored decoder
rejects. On the three-byte prefix the legacy decoder computes the listing at
offsets 16 and 18; on the full sample with extra fuel it fails at `cc`. Thus the
claim compares successful consumed prefixes, not equal behavior on the full
stream or preservation of failure diagnostics. `stack_byte_observations_refine`
then composes the adapter inclusion with the listing projection and the toy
block machine, proving observation inclusion at byte inputs.

## Atomic decoder institution

[`Institution`](../../Silmaril/Machine/DecodeGraph/Institution/Thms.lean)
checks the atom-only institution separately from forward transport. Fix the
context type, byte carrier and span carrier. A signature is an instruction
type, a signature arrow is a function, and a sentence asserts that one exact
tuple of context, bytes, instruction and span is successful. `translate` maps
only the instruction. Models are relational success graphs (with only
identity model morphisms), and `reduct` is inverse image: an exact source
success holds precisely when its translated target success holds. The
sentence maps and contravariant reduct satisfy identity and composition, and
the atomic satisfaction condition is definitional. No functor bundling or
logical connectives are needed for this fragment.

This is not a construction on deterministic executable decoders. If two
distinct source instructions map to a successful target instruction, the
reduct has both as successes at the same input and span, even if the target
graph was deterministic (`reduct_not_deterministic_of_collision`). Forward
`map` takes images of successes; reduct admits all preimages. Neither runs a
decoder or preserves diagnostics.

## Staged gaps

- No connection to CFG recovery, existing decompilation certificates, or a
  platform fetch/step equivalence. `Decoder.decodeBlock`, x86 listing checks,
  and those certificates continue to serve their own contracts. Fall-through
  at an externally supplied boundary, address wraparound, and diagnostic
  policies can be added as separately justified variants.
- Logical fragments beyond atoms and signature arrows beyond functions are
  not part of this institution experiment. In particular, determinism and
  negative or universal properties under arbitrary relations do not follow
  from covariant success transport.

Targeted check:

```sh
lake build --wfail Silmaril.Machine.DecodeGraph.Institution.Thms Silmaril.Proofs.Machine.DecodeGraph.X86Example
```
