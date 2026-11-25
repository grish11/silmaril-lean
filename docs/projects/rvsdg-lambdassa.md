# Typed λSSA ↔ RVSDG correspondence

The translation fragments use the repository's `Silmaril.Isotope.LambdaSSA.Tm`
and `Tm.HasType`. An admitted straight-line expression is a sequence of
`let₁ (op f (var i))` bindings ending in `var j`. Each instruction has one
typed argument and one typed result. A type code denotes one port, so a
dialect can use a product type as a single operand or result. The fragment's
syntax includes neither forming nor destructuring those products.
[Admission and fibres][defs] · [Categorical theorems][thms]

`inputs` maps the ordered λSSA context to value ports using the same type
codes. `Opcode.instr` keeps the instruction and obtains its unary port
signatures from `HasTy`. `Scope.origin` maps de Bruijn zero to the newest
binding and keeps older producer numbers when appending to the table. The
entry order is the de Bruijn list order, with index zero at the first port.
The semantics compares this ordering to λSSA's choice of newest variable as
the right tensor factor.

`Related` describes the correspondence by the syntax rules for a result
wire and for an opcode with a numbered input wire and a related
continuation. It contains no semantic premises. `SSAForm` recognizes the
expression shape with typed variable positions. At the RVSDG end, `RVForm`
certifies unary primitive nodes and their typed live origins. `GraphForm`
applies this test to the typed numbered linearization. `lowerGraph` and
`raiseGraph` construct dependent pairs of target syntax and correspondence
evidence. `Related.typing` recovers repository typing for every witness.

## Model and theorem

Given the repository's λSSA `TypeModel`, each primitive must have a value
arrow `f` whose image under the distributive Freyd functor `J` is its
`InstructionModel` denotation. The RVSDG model wraps these same value
arrows with the singleton port-product unitors. `GraphRelated.sound` applies
to any relation witness. It constructs a structural λSSA `Denotes` witness
whose image agrees with the direct RVSDG graph arrow after applying the input
context map and removing the trailing unit on the result. In a model with
the existing `TypingCoherent` hypothesis, `GraphRelated.denote_eq` identifies
the standard chosen λSSA denotation. The proof covers the acyclic rules of
the interface, so a strong Elgot Freyd model can instantiate it without using
iteration.

## Scoped terminal γ

A λSSA selector for `n + 1` arms is a right-associated sum of `n + 1`
copies of unit. `selectorLiteral` constructs a typed tag in actual λSSA
syntax. Arm zero is the left injection, each successive right injection
advances one position, and the final unit marks the last arm. This agrees
with the RVSDG predicate's in-range index. The interpretation of the λSSA
sum and the RVSDG selector object each satisfy the coproduct universal
property for `Fin (n + 1)` copies of the tensor unit. `selectorIso_tag` proves
that the canonical isomorphism preserves each arm number. The types instance
of the RVSDG model uses `ULift (Fin (n + 1))`.
[Selector encoding][selector]

The scoped switch has one selector input and an ordered payload context
`Γ`. For each arm, an indexed `Port Γ A` specifies the payload position
returned at the common result type `A`. The λSSA expression is a left-first
case spine starting from de Bruijn index zero. Each left arm returns the
corresponding original payload variable. Each right arm cases on the newly
bound suffix selector, until the final unit tag returns its payload variable.
The arm positions are shifted through the binders and can never name a
selector or unit introduced by the case spine.

On the RVSDG side, the root has exactly one γ node whose first input is the
control port and whose remaining inputs are all payload arguments in order.
Every child is a fresh region with zero vertices and one result wire sourced
from its selected payload argument. The root returns the γ result. This
admission rule is syntactic and keeps the selector distinct even if its
λSSA type code coincides with a payload type. The `lowerGammaGraph` and
`raiseGammaGraph` fibres both use `GammaGraphRelated`.

`GammaGraphRelated.sound` applies to any relation witness. The proof uses
λSSA's contextual case combinator, the distributive law that carries the
payload into the selected branch, and the coproduct property of the tagged
RVSDG payload to cover all inputs. `GammaGraphRelated.denote_eq` identifies
the chosen denotation under `TypingCoherent`. [Terminal γ theorems][gamma]

The two slices admit open expressions. They leave computed selectors,
instructions inside γ arms, composition of γ with straight-line bindings,
arbitrary expression normalization, state ports, multiple exits, CFG
restructuring, ordered effects and iteration open. A dialect institution can
use these typed syntax relations and the graph soundness theorems at the
model boundary.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Gamma.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Gamma.Thms
```

The fixture uses two distinct base types, an argument wire, an output shared
by two instructions, and a return from an older binding. The switch fixture translates a concrete λSSA case spine and checks
all three γ results in deliberately permuted payload order. [Fixture][fixture]

The exact studied versions and PDF SHA-256 digests of Reissmann et al.,
*RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
and Ghalayini and Krishnaswami, *The Denotational Semantics of SSA* (2024),
are pinned in the categorical milestone. The relevant passages are RVSDG
§§4.1.1–4.1.2, 5.1.2 and 5.2.2 and λSSA §§3 and 5.3.
[Scholarly source pins](rvsdg-categorical.md#sources)

[defs]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Defs.lean
[thms]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Thms.lean
[gamma]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Gamma/Thms.lean
[selector]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Selector/Thms.lean
[fixture]: ../../tests/ssa/RVSDGLambdaSSA.lean
