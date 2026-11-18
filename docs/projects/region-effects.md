# Indexed instruction effects and block summaries

`Silmaril.Semantics.Region.Effects` separates observation alphabets, possible
execution effects, sequential dataflow summaries, and control outcomes. These
are interpretation and certificate layers over regions. They do not change the
[positive-law model lattice](region-lattices.md).

## An open signature with fewer arguments

The canonical alphabet is an indexed family:

```lean
Atom (Payload : Kind → Type v) := Sigma Payload
```

An atom is a category and a payload of that category's type. `Kind : Type u` is
arbitrary: there is no mandatory finite list of categories, decidable equality,
common payload type or machine representation. `atKind effects k` observes one
category. Its result has type `Set (Payload k)`.

`DirectKind` is an optional reusable vocabulary, including instruction identity,
reads, writes, clobbers, calls, syscalls, UB, trap, fault and raise. Supplying a
payload family chooses each domain separately. The checked
[`Examples.Payload`](../../Silmaril/Semantics/Region/Effects/Examples/Defs.lean)
uses natural-number read addresses, symbolic write addresses, bounded register
and syscall numbers, strings for instructions/calls, and unit payloads for
abnormal effects. The different read/write domains are deliberate: a combined
touch domain requires a supplied common address mapping, or a tagged sum, rather
than an ill-typed union.

`Examples.LayerPayload` extends the alphabet with a call-summary layer. The
`embedDirect` renaming and `projectDirect` partial projection have a proved
round trip. The projection returns `none` for summary nodes; it does not invent
a direct effect. A signature can instead be a model's associated data; no global
typeclass instance is required for the core.

`BlockSignature` packages the family, register carrier and control-outcome
carrier. Block APIs take this one signature; subsequent arguments are inferred.
The family is explicit, so two analyses of the same machine can coexist without
competing typeclass instances. An adapter may add a local typeclass that selects
its signature, but the generic API does not commit to a unique signature per
machine.

`Atom` lives in `Type (max u v)`. All fibers of a family share a universe bound,
not a type. A family containing larger domains can raise that bound with
`ULift`; fully arbitrary universe-polymorphic fibers cannot themselves form one
ordinary Lean indexed family. `BlockSignature` separately tracks the universes
of categories, payloads, registers and control outcomes. Packaging reduces term
parameters, not universe constraints.

## Direct observations and transferred summaries

A direct effect describes the current instruction's behavior, excluding
transitive execution through a call. A direct call event records the call;
a callee's read/write/syscall envelope is separate evidence. A resumed-call
summary needs an operational call/return contract before it can contribute to a
caller's summary. No resumption theorem follows from a call opcode or the
presence of a call atom. The `direct_does_not_include_callee` example checks this
separation on distinct call and syscall atoms.

Instruction identity is itself an optional direct observation. Read/write sets
are possible accesses; clobbers describe a chosen loss-of-value policy. None is
a definite definition merely because it is possible. UB is an explicit atom or
distinguished outcome under the selected interpretation, never the empty set.
Trap, fault and raise have the same policy choice; clients should state whether
they emit an event, stop with a reason, or both.

`InstructionSummary` has three components:

| Component | Combination within a block | Meaning |
| --- | --- | --- |
| `direct` | union | Possible direct observations of its instructions, excluding transitive callees |
| `useDef` | sequential transfer | Upward-exposed uses and definitions guaranteed on the relevant continuation |
| `control` | final instruction only | Normal successors, including fallthrough, and distinguished outcomes under the chosen policy |

A `Block` is nonempty: a list of body instructions and a final instruction.
The final instruction need not branch. An ordinary final instruction contributes
its fallthrough successor. `Block.effects_direct` characterizes the direct
union exactly. `Block.direct_bound` connects that union to actual emitted
effects given instruction-lookup coverage and a per-step observation proof; it
does not infer those premises from the instruction list. `Block.effects_control` proves that body successor summaries do
not leak into the block control summary. `prepend_assoc` permits regrouping
sequential summaries.

This control rule needs a certificate. `CertifiedBlock c` requires each body
instruction to satisfy `c.interior`, direct certificates for every instruction,
and the final instruction's control certificate. `interior` must exclude
escaping control outcomes under the adapter's policy and justify continuation.
These are proofs relative to the chosen `BlockContract`; arbitrary supplied
predicates do not establish machine semantics. `CertifiedBlock.control_sound`
transports the final certificate to the computed block summary.

In particular, an interior memory fault must not disappear just because it
occurs before the final instruction. Either prove it impossible in the admitted
domain, include it through an appropriate different block analysis, or decline
the terminal-only certificate. The operational theorem
`control_bound_of_terminal` requires coverage of both first normal exits and
reachable distinguished halts by the supplied terminal transfer relation. Its
conclusion is `ControlBound`, with separate guarantees for normal labels and
halt reasons. It proves no termination or progress claim.

## Upward-exposed use/def

For a sequential pair:

```text
uses(a ; b) = uses(a) ∪ (uses(b) \ definiteDefs(a))
definiteDefs(a ; b) = definiteDefs(a) ∪ definiteDefs(b)
```

For selection, possible uses union and definite definitions intersect. The
precision order increases possible uses and decreases guaranteed definitions.
`UseDef.selection_lub` proves that selection is the least upper allowance in
this order. `UseDef.sequence_mono` proves sound weakening in both operands;
`UseDef.sequence_assoc` proves associativity. The formulas describe paths that
reach the relevant continuation. To apply them to a potentially faulting or
nonreturning instruction, the adapter must specify that continuation's domain;
they are not guarantees that every execution reaches the second instruction.

The checked examples define a register before using it, obtaining no
upward-exposed use. Reversing the order retains the use. Selection with a branch
that does not define the register removes its definite-definition guarantee.
Plain union of direct accesses or instruction-level uses cannot compute these
summaries.

## Sound envelopes and changes of observation

`envelope T A U observe` is the least sound upper allowance of events emitted
by steps on admitted internal prefixes and their next step, including boundary
crossing. Finite prefixes of diverging runs are included. `envelope_le_iff`
characterizes leastness. `covered_bound` and `labels_bound` lift covered local
observations to regions without any BB partition.

`outcomeEnvelope` additionally observes every reachable distinguished halt,
including a halt with no outgoing transition or emitted event. It uses the
alphabet `Sum Event Stop` and has its own leastness theorem and
`outcome_covered_bound`. Local step coverage and local halt coverage together
suffice. `fault_not_empty_control` and `fault_envelope_nonempty` demonstrate a
faulting state that would be missed by normal-exit-only or emitted-event-only
checking.

These are may analyses. Bounds can be arbitrary complete lattices, including
powersets, products, or domains with top. Top is sound but uninformative.
`MustOccur` instead quantifies over a chosen nonempty trace family; its
`must_implies_may` theorem needs separate operational coverage of that family.
Joining possible effects establishes no must occurrence.

`Renaming` maps categories and their dependent payloads. Its powerset image
preserves identity, composition, inclusion and arbitrary unions. It can merge
observations, so no intersection or truth-reflection claim is made.
`bound_transport` separately transports sound bounds through any monotone map
of observation orders. Exactness, reflection and recovery of erased effects
require further hypotheses.

## Verification and scope

```sh
lake build --wfail Silmaril.Semantics.Region.Effects.Examples.Thms
make check CHECK_TARGETS=Silmaril.Semantics.Region.Effects.Examples.Thms
```

The examples are deterministic abstract analyses, not binary-corpus coverage.
This API supplies no ISA event inference, call adequacy, executable fetch or
concurrent interference theorem. Such adapters must provide the actual events,
admitted-state invariants, continuation contracts and step/halt coverage.
