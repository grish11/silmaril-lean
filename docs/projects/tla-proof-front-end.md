# TLA+ proof obligations and exact named assumptions

`Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Thms` exposes a constant-level
proof profile for one standalone source module. `prepare` parses source and
returns its module assumptions and theorem obligations in declaration order.
Each obligation has a goal, its preceding module assumptions, its own
`ASSUME … PROVE` hypotheses, and the outcome of scoping the source proof.
[Definitions](../../Silmaril/Logic/Temporal/TLA/ProofFrontEnd/Defs.lean) ·
[Soundness statement](../../Silmaril/Logic/Temporal/TLA/ProofFrontEnd/Thms.lean)

## Scope and denotation

- The admitted statements are expression assumptions, expression theorems and
  plain `ASSUME … PROVE` theorems with a flat list of expression hypotheses.
  Each admitted hypothesis and goal must have constant level and lower in the
  existing core data profile without external primitives. Definitions and
  declarations use the existing resolver and level checks. Module composition,
  proof directives, hierarchical proofs, `NEW`, boxed forms and labeled or
  nested hypotheses are outside this profile.
  [Semantic coverage baseline](tla-semantic-coverage.md) ·
  [Data lowering](tla-data-elab.md)
- For expression statements the projection uses the equivalent nullary
  definitions described in TLA+2 §4.1. Anonymous expressions, local hypotheses
  and rule conclusions use generated names outside parsed identifier syntax.
  Named `ASSUME … PROVE` statements enter citation scope as rules. Each cited
  fact and returned statement carries its original zero-based source unit
  index. Resolver, level and lowering diagnostics carry projected paths, which
  can shift when hypotheses add definitions.
  [TLA+ Version 2, §§4.1–4.2](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=7)
- In `BY` and `BY ONLY`, each citation must be a bare name of an earlier
  module assumption or theorem. Forward and self citations, formula
  citations, selectors, module citations and `DEF` are rejected. External
  prover modules are outside this profile. A citation of a prior theorem
  records its identity only.
  TLAPS distinguishes known facts from facts available to a prover and
  describes additional scoping and usability rules in its proof language.
  [TLA+ Version 2, §§7.2–7.3](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=22) ·
  [TLAPS known and usable facts](https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Hierarchical_proofs.html) ·
  [TLAPS prover tactics](https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Tactics.html)

`Obligation.Valid` says that for every valuation in a chosen data
interpretation, if the preceding module assumptions and the local hypotheses
evaluate to that interpretation's true value, so does the goal. All
expressions share the same data operations, Boolean policy and valuation.
This is the semantic judgment for the extracted obligation. The `ONLY`
flag is retained on the leaf citation, and the automatic rule below uses
just its single cited premise.
[*Specifying Systems*, §§17.5.6–17.6](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=352) ·
[TLA+ Version 2, §8.2](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=38)

## Evidence

- **Unresolved.** Preparation records missing proofs, `OMITTED`, `OBVIOUS`
  and well-scoped `BY` leaves. This status carries the source proof request.
  Rejected parse, scope or unsupported forms produce a diagnostic instead.
- **Automatic.** `Obligation.checkExact` applies to `BY A` or `BY ONLY A`
  with one prior named module assumption `A`. It compares the expanded goal
  and cited assumption as typed data terms. The matcher covers rigid
  declaration identities, numerals, Boolean literals and structurally
  matching equality or disequality. A successful `ExactCertificate` carries
  an in-scope premise and a Lean equality of terms. `ExactCertificate.sound`
  gives the semantic judgment in every data interpretation. A failed match,
  multiple citations or a theorem citation leaves the proof unresolved.
- **Supplied.** A Lean caller can separately furnish `SuppliedEvidence` for
  `Obligation.Valid`. Its proof is scoped to the supplied interpretation and
  does not change the source proof status.

For example, the expanded term for `C = 0` is shared by the assumption and
the goal in this module. The checker uses that equality to discharge the
goal under the assumption.

```tla
---- MODULE ExactAssumption ----
CONSTANT C
ASSUME Zero == C = 0
THEOREM Same == C = 0 BY ONLY Zero
====
```

The soundness theorem covers this rule over the landed data denotation.
General source proof checking, TLAPS correspondence and whole-module
validity are outside the contract.

The TLA+ Version 2 guide cited here is dated 11 December 2018, with PDF
SHA-256 `ace1b572ff0c80965de6db654dae69847ec63debe11c595c428d7367ea194951`.
[Reference PDF](https://lamport.azurewebsites.net/tla/tla2-guide.pdf)

## Verification

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Examples
```

The parsed examples exercise exact matching through expanded definitions,
mismatches, scoped assumptions and hypotheses, references to omitted and
`ASSUME … PROVE` theorems, and representative rejection paths. The same
module proves an example of separately supplied Lean evidence.
[Regressions](../../Silmaril/Logic/Temporal/TLA/ProofFrontEnd/Examples.lean)
