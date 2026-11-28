# Serial cuts between checked RVSDG and flat LambdaSSA regions

The serial interface composes two checked numbered graphs whose producer
exits carry the same payload type as the consumer entry. A single physical
token accompanies the payload. The two graphs can have different outer
vertex counts, local scopes and carrier encodings. The final component
may expose two different exit payload types.

`Serial.splice` uses the existing checked splice twice. The first
application puts the carrier conversion before the consumer. The second
substitutes that suffix at the producer's returned data and token origins.
The conversion strips the producer's exit tag, injects the payload into the
consumer's entry carrier, and retains the token. The resulting graph has
one numbered outer region, with local γ and θ scopes preserved.
`certifyCut` compares the reconstructed graph to the supplied actual graph.
It checks the whole typed numbering and wiring at this specified cut.

`Serial.splice_agrees` is the binary composition law. It takes two checked
codes and their existing agreements with actual flat LambdaSSA regions.
It combines `Splice.append_denote` with `Flat.denote_link`, which relocates
the block tables and redirects both producer exits to a fresh consumer
entry. The theorem applies in coherent `StateT σ Part` models. The checked
cut's finite-return law has an intermediate witness consisting of the
producer's decoded exit, its payload, and its exact returned token. The
consumer observes that payload and token in source order. An absent finite
return remains absent on both sides. The SSA observation groups blocked
execution and nontermination under absence of a finite return.

[Definitions](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Serial/Defs.lean) ·
[Binary law and serial adequacy](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Serial/Thms.lean)

## Constructing and recovering a pipeline

- Forward. A finite nonempty typed `Spine` of the existing acyclic-body
  loops computes an actual flat CFG, a numbered RVSDG, and its checked
  token and cut witnesses. A link can attach two already composed
  spines, so the number of outer θ vertices is unbounded.
- Reverse. Given local structural views, their component graphs and
  a supplied cut layout, the existing local decoder recovers the loop
  components. `certifyCut` checks each proposed split and
  `Decomposition.link` combines the certificates. The recovered typed
  CFG is computed from this decomposition. The certificate has no
  LambdaSSA region field.

This interface checks supplied cuts. The [serial recognizer](rvsdg-serial-recognition.md)
recovers them from the emitted alternating layout. Renumbering, nested θ
inside a leaf body, and structuring CFGs with nonserial edges or more
general reducible control flow are separate developments. The binary law can also be applied to other
codes with this carrier interface and an independently established
component agreement.

The fixture compiles three effectful loops into five outer vertices.
The first θ takes feedback. Its exit supplies payload 6 and token 6
to the second loop. That loop returns payload 13 and token 9, and the
third observes both and returns payload 23 and token 12 at the second
external label. The two exit labels of the last loop have different
types. The fixture runs two separate cut checks, composes their reverse
certificates, and checks the same observation for the recovered CFG's
actual denotation. A typed mutation of the second cut keeps its data
edge and reads the entry token. The checker rejects it.
[Fixture](../../../../tests/ssa/RVSDGLambdaSSASerialCuts.lean)

## Route typed producer exits in the flat CFG

`Flat.linkBy` gives each producer exit a typed destination. A route either
enters the relocated consumer entry or returns immediately to a chosen
external label. The producer's two payload types may differ. Local edges
and both consumer exit labels retain their original meaning. The ordinary
`Flat.link` sends both exits to the consumer.

`Flat.denote_linkBy` proves that the actual flat `Region.denote`
sequences the producer with just the chosen destination in coherent monadic
Elgot models. The proof uses codiagonal for the two phases and carries state
through the cut by ordered bind. The fixture gives the producer a unit exit
that bypasses the consumer and a numeric exit that enters it after feedback.
The consumer observes the producer's exact state on one input and reaches a
selected undefined primitive on another. The numbered serial graph emitter
still uses the homogeneous handoff described above.
[Typed linker](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Defs.lean) ·
[Denotation theorem](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Thms.lean) ·
[Exit-routing fixture](../../../../Silmaril/Proofs/SSA/RVSDG/LambdaSSA/NestedFeedback/Regression.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3 and 6.1. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), arXiv:2411.09347v1, §§3, 5.1 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
