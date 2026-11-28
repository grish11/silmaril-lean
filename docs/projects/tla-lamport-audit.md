# Standalone TLA audit against Lamport

This audit covers the typed Simple TLA and scoped General TLA described in the
[project guide](tla.md). Its reference is Leslie Lamport, *The Temporal Logic of
Actions*, ACM TOPLAS 16(3), May 1994, pp. 872–923, DOI
`10.1145/177492.177726`. The section and figure numbers below refer to the
author-hosted November 1993 camera-ready PDF, SHA-256
`47b8e7844b0ca7a7ce4cf31bad2df887307e796450f36520bbdc078516b8278e`.
[Author-hosted PDF](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf)
· [Published article](https://doi.org/10.1145/177492.177726)

## Simple TLA

| Paper | Lean definition or theorem | Coverage |
| --- | --- | --- |
| §§2.1–2.6 and Fig. 4, states, state functions, actions, priming and validity | `Behavior`, `StateExpr`, `StatePred`, `Action`, `Action.current`, `Action.prime`, `Formula.Sat`, `Formula.Entails` | Direct denotations over a chosen Lean state type. Priming reads the target state. Action validity is a Lean premise quantified over pairs of states. The paper interprets first-order expression syntax by simultaneous substitution in a universe of variable assignments. The standalone leaves are functions and relations, with no expression grammar, occurrence analysis or syntactic action validity judgment. |
| §2.7, equation (5), enabledness | `Action.enabled`, `General.StatePred.enabled` and `eval` | Direct existential over target states. The General state predicate exposes enabledness as a constructor whose action is still a denotation. The paper's syntactic expansion into fresh rigid quantifiers over the primed occurrences would require expression syntax and substitution. |
| §5.6, Fig. 4, temporal grammar and evaluation | `Formula`, `Formula.Holds`, `Formula.Sat`, `Formula.holds_suffix` | Five constructors match the Simple fragment. The Lean type also has a typed rigid existential whose body closes over a single value. Indexed evaluation is proved equivalent to explicit suffix evaluation. The first two states supply action denotations inside steps. Bare actions and the unrestricted action box belong to the paper's RTLA discussion in §4. |
| §§5.1–5.3 and Fig. 4, unchanged, bracket, angle, eventually and leads-to | `Action.unchanged`, `bracket`, `angle` and `Formula.eventually`, `eventuallyAngle`, `leadsTo`; `Formula.holds_eventually`, `holds_eventuallyAngle`, `holds_leadsTo` | Defined from the primitive connectives and action semantics. The characterization lemmas derive their indexed witness laws. A bracket can permit changes to components outside its observation. |
| §§5.3–5.5, equations (17)–(18), fairness and program shape | `Formula.weakFair`, `strongFair`, `spec`; `holds_weakFair`, `holds_strongFair`, `strongFair_implies_weakFair` | The fairness definitions directly encode recurrence of changing steps or the respective disabledness clauses. Continuous-enablement and recurrent-enablement forms are derived. `spec` assembles the standard three conjuncts with arbitrary `Live`. A machine-closure criterion saying when fairness adds no safety constraints remains open here. |

[Simple definitions](../../Silmaril/Logic/Temporal/TLA/Defs.lean)
· [Simple theorems](../../Silmaril/Logic/Temporal/TLA/Thms.lean)

### Figure 5 rules

The statements in `Rules.Figure5` interpret validity of an action premise as
quantification over source and successor states. A temporal premise is an
entailment over all behaviors, so it can also be applied on any suffix.

| Paper rule | Lean statement and coverage |
| --- | --- |
| TLA1 | `tla1` gives the equivalence between `□P` and `P ∧ □[P ⇒ P′]_f`. The premise checks preservation of `P` across any step with equal observations. |
| TLA2 | `tla2` derives `□Q ∧ □[B]_g` from `□P ∧ □[A]_f` using the single step premise `P ∧ [A]_f ⇒ Q ∧ [B]_g`. The simulation example erases a hidden bit, including steps where only that bit changes. |
| INV1 | `inv1` derives `□I` from `I ∧ □[N]_f` using the bracket-preservation premise. It specializes the existing `Formula.spec_invariant`. |
| INV2 | `inv2` gives the equivalence between `□[N]_f` and `□[N ∧ I ∧ I′]_f` under `□I`. Both copies of `I` are inside the bracket. |
| WF1 | `wf1` derives `P ↝ Q` using bracket preservation of `P ∨ Q` while in `P`, progress on `⟨N ∧ A⟩_f` while in `P`, and enablement of `⟨A⟩_f` in `P`. The example's fair action permits a successor outside `N` that fails `Q`. |
| SF1 | `sf1` uses the same step premises and the temporal premise `□P ∧ □[N]_f ∧ □F ⇒ ◇ENABLED ⟨A⟩_f`. Applying this premise on every suffix that stays in `P` yields recurrent enabledness. The checked example includes an alternating behavior that meets the step and temporal assumptions with weak fairness and fails the leads-to conclusion. |
| WF2 | `wf2` takes the barred action, observation, and target enabledness separately. Its four premises keep the Figure 5 simulation, guarded progress (including `P′` and target enabledness), enablement implication, and eventual stabilization of `P` when no changing `B` steps occur and target enabledness eventually holds continuously. |
| SF2 | `sf2` uses recurrent target enabledness in the stabilization premise and drops the enabledness guard from step progress, as in Figure 5. Its conclusion uses recurrent target steps or eventual continuous target disabledness, following equation (18). The pinned PDF's barred SF line in equation (53) prints `□◇` on disabledness and `◇□` on the step disjunct. Equation (18), the Figure 5 recurrent-enablement premise, and the §7.2.2 explanation give the strong-fairness reading used here. |
| STL1 | `stl1` uses `PropDerives`, classical natural deduction in the `¬, ∧` basis, and its pointwise soundness theorem. Temporal formulas can stand for opaque propositions. An empty context gives tautologies. For Note 11's derivations from previously proved formulas, the caller supplies each context formula's validity on every behavior. Examples check excluded middle and modus ponens from such a context. |
| STL2 | `stl2` derives `F` from `□F` at the current instant. |
| STL3 | `stl3` gives the equivalence `□□F ≡ □F`. |
| STL4 | `stl4` lifts the validity of `F ⇒ G` to `□F ⇒ □G` by applying the premise to each suffix. |
| STL5 | `stl5` gives the equivalence `□(F ∧ G) ≡ (□F) ∧ (□G)`. |
| STL6 | `stl6` gives the equivalence `(◇□F) ∧ (◇□G) ≡ ◇□(F ∧ G)`. The later of the two stabilization times witnesses the common tail. |
| Lattice | `lattice` derives `(∃ c, H_c) ↝ G` under `F` from `H_c ↝ (G ∨ ∃ d, c ≻ d ∧ H_d)` for each `c` under the same `F`. Well-founded induction uses the smaller-rank instance at the later witness time of the original behavior. The example combines WF1 with Lattice on a run that passes through two ranks before reaching zero. `F` holds initially and fails at the second rank. |

Lattice represents the paper's set by an index type, so `c : ι` carries the
membership premise. The quantified families are written as Lean existentials
at the relevant instants, using the same witness semantics as leads-to. This
allows arbitrary temporal members without extending the Simple TLA grammar.
The relation argument `smaller d c` expresses the printed `c ≻ d`. Lean requires
well-foundedness alone, which also permits strict relations without transitivity.
The rule retains the printed, unboxed `F` at the start of the behavior. The
leads-to premises already quantify over all later instants of that behavior.

For WF2 and SF2, `weakFair_map_iff` and `strongFair_map_iff` identify ordinary
fairness of the mapped behavior with the explicit-enabledness formulas for the
pulled-back action and observation. They evaluate `ENABLED` over target
successors before mapping the resulting predicate back. Both transfer examples
use a target step that can change a hidden component at counter zero, where
enabledness of the pulled-back action fails. The SF2 example also checks that
positive even counter states enable a target step and odd states disable it.

[Figure 5 statements](../../Silmaril/Logic/Temporal/TLA/Rules/Figure5/Thms.lean)
· [STL and Lattice statements](../../Silmaril/Logic/Temporal/TLA/Rules/Figure5/Temporal/Thms.lean)
· [Action and fairness examples](../../Silmaril/Logic/Temporal/TLA/Rules/Figure5/Examples.lean)
· [STL and Lattice examples](../../Silmaril/Logic/Temporal/TLA/Rules/Figure5/Temporal/Examples.lean)
· [Pinned PDF, Figure 5](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf#page=17)

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Rules.Figure5.Temporal.Examples
```

## General TLA and Figure 9

| Paper | Lean definition or theorem | Coverage |
| --- | --- | --- |
| §2.6 and Fig. 9, rigid variables and quantification | `General.Scope`, `Model`, `Expr.rigid`, `Expr.flex`, `Action.existsRigid`, `StatePred.existsRigid`, `Formula.existsRigid` and their evaluation clauses | Direct typed semantics. One rigid valuation is used throughout a behavior and at both ends of an action. A rigid binder extends that valuation once, choosing from one sort's carrier. The paper uses a common value domain. |
| §8.2 and Fig. 9, general formula grammar | `General.Formula`, `Formula.Sat`, `Formula.Holds`, `Formula.rename`; `Context.old`, `Context.fresh`, `Scope.Rename.underFlex`, `underRigid` | Scoped temporal syntax with denotational leaves and binders that add a fresh name of a selected sort. The Lean grammar also allows box directly over a quantified formula. Fig. 9's displayed General production only inherits box through its Simple-formula alternative. Renaming preserves the fresh name under binders. |
| §8.2, equations (48)–(49), and Fig. 9, stuttering and agreement away from the hidden name | `Behavior.canonicalReduction`, `canonicalReduction_eq48`, `eq_canonicalReduction_of_eq48`, `canonicalReduction_eq_iff_stutterEquiv`, `hide_iff_lamport_reduction` | The reduction takes the first state of each maximal constant block and repeats the final state forever if the changes end. It satisfies all three stream equations in (48), which uniquely determine it. Equality of reductions is equivalent to the existing `Retiming`-based common expansion relation `StutterEquiv`. The product-state form of (49) uses equality of full-state reductions and equality after visible projection for `=_x`, for stutter-invariant operands. |
| Equation (49), flexible witnesses; §8.2, invariance | `hide`, `General.Formula.existsFlex`, `Formula.sat_existsFlex`, `Formula.sat_stutterInvariant`, `Formula.holds_retime` | The core projects a full witness and compares its visible run up to stuttering. `sat_existsFlex` derives the clause in extended valuation coordinates. Whole-state stuttering invariance holds for every scoped formula, including nested binders. `forallFlex` and `forallRigid` and their satisfaction characterizations are derived by duality. |
| E1, introduction with a state function | `General.Formula.existsFlex_intro` | The premise evaluates the body after extending the valuation at each instant with `f ρ s`. The term can depend on the outer rigid environment and visible state. That extension witnesses the quantifier without a change of clock. The unresolved syntactic result is a capture-avoiding operation `F(f/x)` on a chosen expression grammar and a theorem equating its satisfaction with this evaluation premise, including for nested binders and `ENABLED`. |
| E2, elimination with a fresh conclusion | `General.Formula.existsFlex_elim`, `Scope.Rename.weakenFlex`, using `Formula.sat_rename` and `sat_stutterInvariant` | The conclusion is typed in the outer scope. Its weakening forces independence from the fresh name. The proof transfers the weakened consequence along the witness's projected stuttering equivalence. A formulation for named syntax would need free-name analysis and a theorem that any syntactically fresh conclusion factors through weakening. |
| F1, introduction with a constant expression | `General.Formula.existsRigid_intro` | The premise uses `e ρ` as a single value for the whole run. The type of `e` permits outer rigid variables and excludes flexible-state inputs. The unresolved syntactic result is satisfaction of capture-avoiding `F(e/c)`, including rigid binders inside actions and predicates. |
| F2, elimination with a fresh conclusion | `General.Formula.existsRigid_elim`, `Scope.Rename.weakenRigid`, using `Formula.sat_rename` | The conclusion again lives in the outer scope and reaches the extended premise by weakening. A named syntax would need the rigid free-name and weakening factorization theorem. |

[General definitions](../../Silmaril/Logic/Temporal/TLA/General/Defs.lean)
· [General theorems](../../Silmaril/Logic/Temporal/TLA/General/Thms.lean)
· [Semantic rule statements](../../Silmaril/Logic/Temporal/TLA/Rules/Thms.lean)

Each input behavior is a retiming of its canonical reduction. The proof's
clock counts changes before the last block and advances at every instant
inside an infinite last block to stay cofinal. In the other direction,
retiming preserves the first changed state of every block, so two behaviors
with a common expansion have equal reductions.

The checked examples reduce `0, 0, 1, 1, 2, 2, …` to `0, 1, 2, 2, …` and
`0, 0, 1, 1, 0, 0, 1, 1, …` to `0, 1, 0, 1, …`.
[Stutter reduction statements](../../Silmaril/Logic/Temporal/TLA/StutterReduction/Thms.lean)
· [Checked examples](../../Silmaril/Logic/Temporal/TLA/StutterReduction/Examples.lean)
· [Pinned PDF, equations (48)–(49)](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf#page=33)

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.StutterReduction.Examples
```

## Auxiliary variables and refinement

- In §8.3.2, an auxiliary variable is justified by recovering the original
  specification after hiding. `hide_extension_iff` gives a sufficient criterion.
  Projection must satisfy the visible specification, which must be stutter-invariant,
  and every satisfying visible behavior must admit an extension with exactly
  that projection. Taking the same clock is a sufficient witness condition.
  The examples apply this to a history bit recording whether a visible bit
  has ever been high. The paper's general existence result for suitable
  auxiliary variables, including prophecy, remains outside this development.
- For equation (51), `hide_refines` transports a full-state simulation through
  the existential hiding on each side. Its state map computes the target hidden
  component from the full source state and computes the target visible component
  from the visible source state alone. Iterated binders and substitution of
  refinement expressions into named formulas are separate obligations. The
  existing `General.Refines.comp` composes maps and `hide_map_iff` is a
  visible-state pullback law for stutter-invariant operands.
- For §8.3.3, evaluate target enabledness in the target state space before
  pulling the resulting predicate back. `Action.enabled_pullback_iff` gives a
  sufficient condition for evaluating enabledness after action pullback instead.
  Every target successor allowed by the action from the mapped source must
  lift to an implementation state. For fairness the action in this hypothesis
  is the angle action. The checked diagonal example reproduces the distinction
  in §8.3.3 with Boolean values. A syntactic barring theorem must substitute only
  free occurrences, treating the successor variables in `ENABLED` as bound.

[Rule examples](../../Silmaril/Logic/Temporal/TLA/Rules/Examples.lean)

## Next PRs

1. On a specified expression grammar, prove capture-avoiding substitution under
   priming, quantifiers and `ENABLED` and connect it to E1/F1 evaluation and to
   barring. Prove the free-name weakening criteria for E2/F2 in the same
   representation.
2. Formalize machine closure and identify the remaining premises of the paper's
   relative completeness result (§8.3.2 and Note 12).

Build both sets of standalone rule examples with

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Rules.Examples \
  +Silmaril.Logic.Temporal.TLA.Rules.Figure5.Examples
```
