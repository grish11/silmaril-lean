# TLA+ proof obligations and exact fact reuse

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
  In a named theorem, a whole hypothesis can carry a parameterless label.
  Each admitted hypothesis and goal must have constant level and lower in the
  existing core data profile without external primitives. Definitions and
  declarations use the existing resolver and level checks. Module composition,
  proof directives, hierarchical proofs, `NEW`, boxed forms, nested
  `ASSUME … PROVE` hypotheses and general expression labels are outside this profile.
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
- A `BY` or `BY ONLY` citation can name an earlier module assumption or
  theorem. In the proof of `T`, `T!H` can cite the whole local hypothesis
  labelled `H ::`. Labels must be unique within their theorem and introduce
  no bare expression names. The proof profile restricts `T!H` to the
  owning proof, where the hypothesis is a known fact. That restriction
  leaves out the general use of subexpression names as formulas. Bare
  forward and self citations, other selectors, formula citations, module
  citations and `DEF` are rejected. A scoped theorem citation records its
  source unit, independently of its proof status.
  [TLA+ Version 2, §6.4](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=18) ·
  [TLA+ Version 2, §§7.2–7.3](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=22) ·
  [TLA+ Version 2, §7.6.2](https://lamport.azurewebsites.net/tla/tla2-guide.pdf#page=34) ·
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
- **Exact reuse.** `Obligation.checkExact` checks a single module assumption
  or local hypothesis cited by `BY` or `BY ONLY`. `Context.checkExact` also
  checks single citations of earlier named formula theorems. It processes
  the actual obligations in declaration order and reuses only a successful
  certificate for the cited theorem in that module. The certificate requires
  the earlier module assumptions to be in the current obligation's scope and
  requires the earlier theorem to have no local hypotheses. A certified
  `ASSUME … PROVE` can therefore establish its own judgment. Applying it as
  a rule in another proof is outside this profile.
- **Term matching.** Exact reuse compares expanded typed data terms. The
  matcher covers rigid declaration identities, numerals, Boolean literals
  and structurally matching equality or disequality. A successful
  `ExactCertificate` carries the Lean equality and the in-scope evidence.
  `ExactCertificate.sound` gives the semantic judgment in every data
  interpretation. A failed match, multiple citations or a dependency
  without a certificate leaves the proof unresolved.
- **Supplied.** A Lean caller can separately furnish `SuppliedEvidence` for
  `Obligation.Valid`. Its proof is scoped to the supplied interpretation and
  does not change the source proof status.

`First` uses the module assumption `Zero`, `Same` uses the certificate for
`First`, and `Rule` uses its own hypothesis `H`.

```tla
---- MODULE ExactFacts ----
CONSTANT C
ASSUME Zero == C = 0
THEOREM First == C = 0 BY ONLY Zero
THEOREM Same == C = 0 BY First
THEOREM Rule == ASSUME H :: C = 1 PROVE C = 1 BY ONLY Rule!H
====
```

The soundness theorem covers these exact rules over the landed data
denotation. General source proof checking, TLAPS correspondence and
whole-module validity are outside the contract.

The TLA+ Version 2 guide cited here is dated 11 December 2018, with PDF
SHA-256 `ace1b572ff0c80965de6db654dae69847ec63debe11c595c428d7367ea194951`.
[Reference PDF](https://lamport.azurewebsites.net/tla/tla2-guide.pdf)

## Verification

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Examples
```

The parsed examples exercise exact matching through expanded definitions,
label qualification and scope, theorem dependency chains across later module
assumptions, and refusal to reuse uncertified theorems and conditional rules.
The same module proves an example of separately supplied Lean evidence.
[Regressions](../../Silmaril/Logic/Temporal/TLA/ProofFrontEnd/Examples.lean)
