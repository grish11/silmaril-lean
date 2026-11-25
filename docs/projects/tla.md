# Temporal Logic of Actions

Import [`Silmaril.Logic.Temporal.TLA.Thms`](../../Silmaril/Logic/Temporal/TLA/Thms.lean)
for Simple TLA and
[`Silmaril.Logic.Temporal.TLA.General.Thms`](../../Silmaril/Logic/Temporal/TLA/General/Thms.lean)
for scoped General TLA. Both standalone modules use Lean's state types and
propositions. Import
[`Silmaril.Logic.Temporal.TLA.General.Institution.Thms`](../../Silmaril/Logic/Temporal/TLA/General/Institution/Thms.lean)
for the room functor and satisfaction condition.

For named TLA+ source trees, import
[`Silmaril.Logic.Temporal.TLA.Surface.Defs`](../../Silmaril/Logic/Temporal/TLA/Surface/Defs.lean)
and use the namespace `Silmaril.Logic.Temporal.TLA.Surface`. See
[TLA+ surface syntax](#tla-surface-syntax) for its grammar coverage.

The reference is Leslie Lamport's *The Temporal Logic of Actions*,
§§5.3–5.6 and Fig. 4 for Simple TLA, §§2.6–2.7 for rigid variables and enabling,
§8.2, equation (49) and Fig. 9 for General TLA, and §8.3.2 for refinement mappings.
*Specifying Systems*, §§8.1, 8.3, 8.8 and 16.2.4, provides the specification and
fairness conventions. [Paper](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf)
· [Book](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf)

## Typed Simple TLA

A behavior is a function `Nat → S` over a chosen state space `S`. A behavior
that settles in its last state still has infinitely many instants. A state
expression has type `S → V`, a state predicate has type `S → Prop`, and
an action has type `S → S → Prop`. These are denotations supplied by the
caller. `Action.current` reads the first state of the pair, and
`Action.prime` reads the second. `Action.enabled A s` quantifies over all
possible target states of type `S`. To restrict enabledness to legal targets,
encode that restriction in the action or in the state space.

The `Formula` constructors are a state predicate, `□[A]_f`, negation,
conjunction and `□F`. At instant `n`, `□[A]_f` tests every successive
pair starting at or after `n`, and `□F` evaluates `F` on every suffix
starting at or after `n`, including the current suffix. A bare action and
a temporal next operator are outside the grammar. `holds_suffix` relates
indexed evaluation to evaluation on the explicit suffix. `Sat` starts at
zero, and `Entails` is implication on every behavior.

The state observation `f` can be the identity, a projection, or a function
computing a tuple of relevant values. The modality stores an observation in
the state type's universe. The action-level operations also accept observations
from a different universe.

| Notation | Definition |
| --- | --- |
| `UNCHANGED f` | The observation has the same value in the source and target states. |
| `[A]_f` | `A ∨ UNCHANGED f`. |
| `⟨A⟩_f` | `A ∧ ¬UNCHANGED f`. |
| `◇F` | `¬□¬F`. |
| `◇⟨A⟩_f` | `¬□[¬A]_f`. |
| `F ~> G` | `□(F ⇒ ◇G)`. |
| `WF_f(A)` | Angle steps recur without bound, or disabled states recur without bound. |
| `SF_f(A)` | Angle steps recur without bound, or there is a suffix of only disabled states. |

Both fairness clauses use `ENABLED ⟨A⟩_f`. The theorems for WF and SF
characterize their premises as eventual continuous enablement and unbounded
recurring enablement, respectively. `strongFair_implies_weakFair` proves the
implication between them. `spec` assembles `Init ∧ □[Next]_f ∧ Live`,
where `Live` can be a conjunction of fairness clauses. `spec_invariant`
requires preservation on every bracket step, including steps that preserve
`f` while changing other state. `weakFair_progress` proves a leads-to
property from step preservation while waiting, enablement while waiting,
and an angle step that establishes the target.

## Stuttering and flexible hiding

A retiming begins at zero, holds or advances by one at each instant, and is
cofinal in `Nat`. It can expand each state into a nonempty finite run of
copies. It cannot postpone a later state forever. Two behaviors are
`StutterEquiv` when they admit retimings that produce the same behavior.
Lean proves this is an equivalence relation. For transitivity, the proof
synchronizes the two clocks on the middle behavior and proves both
synchronized clocks are cofinal.

This common-expansion presentation corresponds to the paper's equality of
stutter-reduced behaviors. Retiming preserves the ordered sequence of
maximal constant blocks and whether the last block is infinite. Conversely,
when those sequences agree, matching each pair of finite blocks at the
larger of their two lengths gives a common expansion. A final infinite
block can be matched one instant at a time. The Lean proofs use retiming
directly.

`Formula.holds_retime` proves invariance at corresponding instants under
repetition of **whole states**. Thus every Simple TLA formula, including WF
and SF, is invariant under `StutterEquiv`. The observation `f` in a
bracket only governs that bracket. Keeping `f` fixed can still change state
predicates, enablement, or another bracket. The theorem does not give
invariance under arbitrary changes to those other state components.

For split state `Visible × Hidden`, `hide p σ` holds when a full behavior
satisfying `p` has a visible projection stutter-equivalent to `σ`. The
hidden value can vary at each instant, and a hidden step can occupy time
inside a visible constant block. `hide_stutterInvariant` proves invariance
on visible behaviors for any predicate `p`. When `p` itself is
stutter-invariant on full behaviors, `hide_iff_lamport` proves agreement
with the paper's equation (49). At a full input `σ`, choose a full behavior
`ρ` in the stuttering class of `σ`, then existentially replace its hidden
component pointwise to obtain a behavior satisfying `p`.

## Scoped General TLA

A `General.Scope` gives each sort two types of names, in `rigid` and
`flex`. Fix a family of carriers `Value : Sorts → Type u`. A valuation
assigns a value of the designated sort to every name. A `General.Model`
holds one rigid valuation and a behavior of flexible valuations. The same
rigid valuation is available at every instant and on both sides of an
action. `Expr.rigid` and `Expr.flex` read typed names. Use
`TLA.Action.current` and `TLA.Action.prime` on an expression with the
rigid environment fixed to read the two ends of an action.

A binder adds a distinguished fresh name of the selected sort in its
own context. `Context.old` embeds an outer name and `Context.fresh`
selects the new name. Renaming under a binder translates outer names
and fixes the fresh name. Rigid existential quantification chooses a
single value from its sort. It is available in actions through
`Action.existsRigid` and in both state predicates and temporal formulas.

The temporal syntax has state predicates, bracket modalities, conjunction,
negation, always, and both existential binders. Always ranges over suffixes
and can enclose quantified formulas. `Formula.Holds` evaluates on the
suffix at a given instant. Both universal binders are defined by duality.
`Formula.sat_forallFlex` quantifies over the same class of extended
behaviors as the existential binder and `Formula.sat_forallRigid`
quantifies over values.

`Formula.existsFlex` uses the product-state `hide` above. The product
splits an extended valuation into its outer valuation and its bound
variable. `Formula.sat_existsFlex` gives the equivalent direct clause
over extended valuations: the witness's old variables follow the
input behavior up to stuttering. Its bound variable may change on
each step. `Formula.sat_stutterInvariant` covers every scoped formula,
so the operands of flexible hiding meet the hypothesis in
`hide_iff_lamport`. `Formula.holds_retime` gives the corresponding
law at related instants.

## Scope maps and refinement

A `Scope.Rename Γ Δ` maps each kind of name to a name of the same sort.
`Formula.rename` translates forward and `Model.reduct` restricts the
rigid environment and the states of a behavior backward. Both operations
obey identity and composition, with equality of the translated syntax.

`Formula.satisfies_rename` states that satisfaction of a translated
formula in the larger model is equivalent to satisfaction of the original
in its reduct. Its hypothesis is injectivity at each flexible sort.
Rigid names may be identified. The hypothesis is used for the
explicit `StatePred.enabled` constructor, including under binders.
In the reverse direction of `Action.enabled_rename`, extend a successor
from the smaller scope by assigning its values on the image and keeping
the current state's values at every other name. This construction
requires only the actual current state as a base, even when some sorts
have empty carriers. Identifying flexible names can equate coordinates
that an enabled action requires to differ.

`hide_map_iff` commutes hiding with pullback along any visible-state
function for a stutter-invariant operand. The
easy direction maps the entire witness. For the reverse direction,
the projected ambient behavior and the visible part of the witness
admit a common expansion. Repeat the *whole ambient state* with the
ambient clock and take the hidden value with the witness clock. The
result projects onto a retiming of the ambient behavior, and its small
image is a retiming of the original full witness. Stutter invariance
transfers the operand to that image. This construction preserves extra
ambient state through inserted repeats and works even when projection
collapses steps. Injectivity is used only when the formula induction
reaches `ENABLED`.

`Refines` expresses semantic refinement via a total state function.
It sends each satisfying implementation behavior to a satisfying
specification behavior. `Refines.comp` composes such maps. A state
function can compute specification variables as in §8.3.2. Substitution
through explicit `ENABLED` would require a separate successor-lifting
condition on the state function.

## General TLA institution

For a fixed type of sorts `Sorts` and carrier family `Value`, the signature
category has objects `Scope Sorts`. A morphism is a sort-preserving
`Scope.Rename` with injectivity evidence at each flexible sort. The rigid
maps may identify names. `Scope.Rename.id_comp`, `comp_id` and
`comp_assoc` give equality of the underlying maps, and proof irrelevance
gives equality of the morphisms carrying the evidence.

The discrete-model presentation `General.Institution.plain Value` fills
[`Silmaril.Inst.Plain`](../../Silmaril/Logic/Inst/Builders/Core/Defs.lean)
with the standalone interfaces.

| Fields | Standalone interface |
| --- | --- |
| `Sen`, `map` | `General.Formula Value Γ`, `Formula.rename` |
| `map_id`, `map_comp` | `Formula.rename_id`, `Formula.rename_comp` |
| `Mod`, `reduct` | `General.Model Value Γ`, `Model.reduct` |
| `reduct_id`, `reduct_comp` | `Model.reduct_id`, `Model.reduct_comp` |
| `Sat`, `sat_map` | `Formula.Satisfies`, `Formula.satisfies_rename` |

`General.Institution.roomFunctor Value` is the resulting `Scope Sorts ⥤ Room`,
and `General.Institution.institution Value` is the packaged institution.
`General.Institution.satisfaction` exposes the corridor's iff on the
standalone formulas and models. A reduct restricts the single rigid
valuation and projects every flexible state at the same instant. Rooms use
actual behaviors and their model categories are discrete. Flexible hiding
still compares its projected witnesses up to stuttering as in standalone
General TLA. A presentation with stutter classes as model objects would
need quotient descent for reducts and satisfaction.

These morphisms express name changes and scope extensions for fixed carriers.
The satisfaction law covers all scoped formulas, including explicit
`ENABLED` and flexible hiding. The successor-lifting proof explains the
injectivity requirement. Semantic refinement via `Refines` transports
satisfying behaviors along a computed state function. For a substitution
along such a function to commute with `ENABLED`, it would also have to
lift successors, and any extension to scoped substitution would need
semantics and laws under binders. Changes of sorts or carriers would also
need their own reindexing semantics.

## TLA+ surface syntax

`Surface.Module` is the compilation-unit tree, with public constructors for
its units, expressions and proofs. The grammar inventory follows SANY at
`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c` (the JavaCC file's SHA-256 is
`bfc981f31c205333f478b773ab108159b5e2d339b659d33b0f920d56ebf4253d`).
Lamport's *Specifying Systems*, Chapters 8 and 16, supplies the specification
notation and language reference. The TLA+ Version 2 notes cover later proof
and subexpression forms. [Pinned SANY grammar](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/javacc/tla%2B.jj)
· [Specifying Systems](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf)
· [TLA+ Version 2](https://lamport.azurewebsites.net/tla/tla2.html)

| SANY productions | Surface representation |
| --- | --- |
| `CompilationUnit`, `Module`, `BeginModule`, `EndModule`, `Extends`, `Body` | `Module` keeps its name, ordered `EXTENDS` names and ordered `ModuleUnit`s, including nested modules. |
| `VariableDeclaration`, `ParamDeclaration`, `ParamSubDecl`, `Recursive`, `ConstantDeclarationItems`, `IdentDecl`, `SomeFixDecl` | Variable groups, constants and recursive signatures. `OperatorDecl` keeps identifier arities and symbolic fixity. |
| `OperatorOrFunctionDefinition`, `IdentLHS`, `PrefixLHS`, `InfixLHS`, `PostfixLHS` | `Definition` keeps `LOCAL` and separates operator heads, bounded function heads and named instance heads. Identifier heads can bind operator parameters. |
| `Instance`, `Instantiation`, `Substitution`, `LetIn`, `LetDefinitions` | Unnamed and named instances share ordered `WITH` substitutions. `LetDecl` retains the interleaving of definitions and `RECURSIVE` declarations. |
| `PrimitiveExp`, `OpArgs`, `OpSuite`, `OpOrExpr`, `Lambda`, `BangExt`, `StructOp`, `NoOpExtension` | `Expr.ref` keeps its identifier, symbolic operator or proof-step head, its arguments and its ordered bang segments. Each named segment has its own arguments. `Selector` covers named segments, `!(args)`, `!n`, `!<<`, `!>>`, `!:` and `!@`. `OpArg` keeps expression-shaped arguments, bare symbolic operators and `LAMBDA`. |
| `Expression`, `ExtendableExpr`, `OpenExpression`, `ParenthesesExpression`, `ParenExpr`, `OpenStart`, operator token classes | Prefix, infix and postfix applications have fixed operand counts. A Cartesian product chain retains its ordered factors. Nesting retains the grouping of applications and of product chains. Expression labels retain their parameter names. |
| `String`, `Number`, `Identifier` | Decoded strings, natural numerals, exact decimal whole parts and fractional digits, and unresolved identifier text. |
| `SomeQuant`, `SomeTQuant`, `QuantBound`, `IdentifierTuple`, `UnboundOrBoundChoose`, `MaybeBound` | Bounded and unbounded rigid quantification, unbounded temporal quantification, and bounded and unbounded `CHOOSE`. Shared domains, bound identifier groups, and tuple patterns remain distinct. |
| `BraceCases`, `SBracketCases`, `TupleOrAction`, `FieldVal`, `FieldSet`, `ExceptSpec`, `ExceptComponent` | Set enumeration, filtering and mapping, bounded functions, function sets, tuple construction, records and record sets, indexing and field selection. `EXCEPT` holds ordered updates with ordered index/field components, and bare `@` has its own node. `f[i,j]`, `f[<<i,j>>]` and `F(i,j)` have distinct shapes. |
| `ReducedExpression`, `FairnessExpr`, action alternatives of `TupleOrAction` and `SBracketCases`, prefix/infix/postfix productions | Square and angle action brackets retain body and subscript. WF and SF retain observation and action. Prime, `ENABLED`, `UNCHANGED`, always, eventually, action composition, leads-to and guarantees have dedicated operator constructors. |
| `IfThenElse`, `Case`, `CaseArm`, `OtherArm`, `Junctions`, `DisjList`, `ConjList`, `JuncItem` | Conditionals, ordered CASE arms and optional OTHER, and ordered conjunction/disjunction lists. A junction list remains distinct from a binary infix tree. |
| `Assumption`, `Theorem`, `AssumeProve`, `NewSymb` | Optional theorem and assumption names. Statements keep expression goals, nested and labeled ASSUME/PROVE, the mode of each keyword, and NEW variable, bounded constant or level-qualified operator hypotheses. |
| `Proof`, `UseOrHideOrBy`, `StepStartToken`, `Step`, `QEDStep` | Proof omission, explicit OMITTED, OBVIOUS, BY and ordered hierarchical proofs with a dedicated closing QED and its optional proof. Citations keep facts and DEF lists, expression and MODULE entries, and ONLY for USE and BY. Step headers retain numeric or relative levels and optional names. |
| `DefStep`, `HaveStep`, `TakeStep`, `WitnessStep`, `PickStep`, `CaseStep`, `AssertStep` and the INSTANCE and USE/HIDE step alternatives | `StepBody` records each form, including SUFFICES, and carries a child proof on assertion, SUFFICES, PICK and CASE. TAKE and PICK retain binder groups, and WITNESS retains its expression list for later interpretation. |

The tree omits the ignored `Prelude` pragma, source ranges, comments, module
rules made of dashes or equals signs, separators, indentation, redundant
parentheses, and optional proof punctuation and markers such as PROOF and
DEFINE. It normalizes synonymous declaration and theorem keywords,
numeral bases, string escapes, and the dedicated operator spellings.
Other symbolic operators retain their spelling and fixity. The usual
identifier and parameter-list forms of labels are represented. The broader
JavaCC label lookahead can accept nonidentifier heads or parameters before
semantic checking. The action bracket represents a single body and the
decimal form represents decimal digits. The grammar's permissive shared
bracket and numeral productions can also admit apparent action operand
lists or base-prefixed decimal pieces outside these forms.

The tree types enforce operand counts for fixed arity operators, a separate
QED for each hierarchical proof, and the distinction between a bounded
function head and an operator head. They leave nonempty-list requirements,
identifier and literal lexing, reserved symbols, precedence, admissible
action subscripts, proof-level consistency and other concrete syntax checks
to the parser or a validation layer. For example, one can construct an
empty `EXCEPT` update list or an empty `BY` citation list. A later semantic
pass must resolve operators, labels, selectors, step references and module
instances, check arities and substitutions, establish binding and `@` scope,
check ASSUME/PROVE modes and TLA+ expression levels, and interpret proof
obligations. Position maps and diagnostics can accompany a tree externally.
The native [source parser](tla-parser.md) produces these trees from TLA+
modules and expressions. Its coverage table describes the supported syntax and
the remaining productions. The [scalar elaborator](tla-elaborator.md) checks
state predicates and actions. The [Quint import path](tla-quint-import.md)
connects both stages on intact exports. TLC configuration, PlusCal translation
and proof checking are separate work.

### Checked surface examples

The examples pair TLA+ source with handwritten Lean trees for a bounded FIFO
queue with weak fairness and a hierarchical proof, and a dispatcher with a
nested worker module, parameterized instantiation and record updates.
Lean also checks focused examples for labels and selectors, operator
arguments, LET with RECURSIVE, temporal binding, and nested SUFFICES.
Lean checks the AST constructors and shape. SANY can process the TLA+
source independently. [Surface examples](../../Silmaril/Logic/Temporal/TLA/Surface/Examples.lean)

~~~sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Surface.Defs \
  +Silmaril.Logic.Temporal.TLA.Surface.Examples
~~~

### Versioned S-expression codec

The [version 1 wire schema](tla-surface-sexp.md) covers the entire Surface AST
and includes the positional field types for every constructor. The
`Silmaril.ProofFormats.TLA.SurfaceSExp.Thms` header exposes the module and
expression APIs and their tree, text and UTF-8 byte round trips. Successful
decoding implies that re-encoding reproduces the exact S-expression tree.

~~~sh
lake build --wfail +Silmaril.ProofFormats.TLA.SurfaceSExp.Thms \
  +Silmaril.ProofFormats.TLA.SurfaceSExp.Examples
~~~

## Checked examples and coverage

[Simple examples](../../Silmaril/Logic/Temporal/TLA/Examples.lean) cover
weakly fair latch progress, the distinction between WF and SF, a parity
invariant, and a hidden initialization step.
[General examples](../../Silmaril/Logic/Temporal/TLA/General/Examples.lean)
hide an initialization step after widening the scope by a Nat clock,
prove that the translated body has no synchronous witness, distinguish a
flexible Boolean witness from a single rigid value, and test successor
lifting and its failure under identification. A refinement example
computes a Boolean latch observation from a Nat clock.
[Institution examples](../../Silmaril/Logic/Temporal/TLA/General/Institution/Examples.lean)
exercise a corridor that identifies two rigid names and adds an
unobserved flexible flag. They check the reduct's coordinates and
satisfaction of the translated `ENABLED` and flexible hiding formulas.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Thms +Silmaril.Logic.Temporal.TLA.Examples \
  +Silmaril.Logic.Temporal.TLA.General.Thms +Silmaril.Logic.Temporal.TLA.General.Examples \
  +Silmaril.Logic.Temporal.TLA.General.Institution.Thms \
  +Silmaril.Logic.Temporal.TLA.General.Institution.Examples
```

| Area | Formalized | Remaining |
| --- | --- | --- |
| Terms and actions | Typed variable lookup, denotational expressions and actions, rigid existential quantification, explicit state-level `ENABLED`, and scalar source elaboration | Wider source elaboration and general capture-avoiding term substitution |
| Temporal formulas | Typed Simple and General TLA syntax and semantics, rigid and flexible quantifiers, whole-state stutter invariance, and scoped reindexing | A derivation calculus with the syntactic substitution rules of Fig. 9, machine closure, completeness results, and a Lean comparison with a separate stutter-reduction operator |
| Specifications | Simple TLA fairness, invariant and progress rules, and semantic state-map refinement | General refinement substitution and auxiliary-variable theorems |
| Integration | The General TLA room functor and satisfaction condition for fixed carriers, a named TLA+ surface AST with a verified S-expression codec and native parser including hierarchical proofs and step references, and bounded checks of two pinned Quint imports | SANY source compatibility gaps, wider elaboration, and general exporter correctness |
