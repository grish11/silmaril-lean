# Free undefined behaviour in Isotope refinement

In the ordered institution, the inequation `a ⊑ b` is interpreted as
`⟦a⟧ ≤ ⟦b⟧`. In the observational institution it is inclusion of the
outcomes of `a` in those of `b`. UB, which permits every outcome, is on the
right of `t ⊑ ub`. A compiler contract can accordingly place the target on
the left and the source on the right. See [ordered satisfaction][ordered],
[observational satisfaction][obs], and [the compiler convention][compiler].

## Construction

The native term and region grammars have empty-type elimination. Literal UB
is introduced here through the extended presentation and the unit-fed
instruction spelling. [LetCase typing][case-typing] [LambdaSSA syntax][ssa-syntax]
[LambdaRTL syntax][rtl]

- `UB.dialectMonad e` acts on `InstrSig τ ε` for fixed types, effects, and UB
  effect `e`. A primitive has one typed input and one result. The new symbol
  at result type `A` has profile `unit → A` and effect `e`. A morphism
  extending a relabelling can choose any symbol with precisely that profile.
  The unbundled `SignatureMap` also changes types and effects. A corresponding
  lift needs to preserve unit and transport the chosen effect as well as the
  ordinary typing and effect premises. [Primitive extension][primitive]
  [Instruction morphisms][instr] [Varying signatures][sigmap]
- `UB.signatureMonad` acts on the contextual `PSig` used by the ordered
  institution. It adds a literal arity-zero operation per judgment sort.
  For LetCase and LetIter a sort includes a bound context and a result type,
  with the free-variable context fixed by the presentation. The independent
  explicit constructor `Expr.ub` has the unique fold into any algebra for
  the extended signature. [Explicit syntax][syntax] [Signature monad][signature]
- `UB.Specification.monad` acts on the institution's specifications. A map
  must send axioms to consequences. The extension transports the old axioms
  and adds `t ⊑ ub` for **every** term at its sort, including expressions
  under binders. `homEquiv` states the universal property for targets with
  designated nullaries above every denotable term. Restriction along the unit
  and extension using the designated symbols are inverse. In each monad the
  unit includes the old operations and multiplication identifies the inner
  and outer fresh symbols. In the ordered case the two symbols may still be
  distinguished before applying multiplication. [Specifications][spec]
  [Institutional consequence][institution]
- Monotone algebra operations place the inequalities under well-sorted
  constructors. The whole expression in any such context lies below UB at
  the result sort. An equation saying a context around UB evaluates to UB
  would need separate absorption laws. In arbitrary validating algebras the
  top rule bounds the image of the syntax fold. In the initial ordered
  quotient every element is represented by syntax, and `initial_le_ub`
  bounds the entire carrier at every sort. The ground inequations alone
  cannot constrain elements outside that image. `model_without_top` gives
  a two-point validating algebra whose carrier has no greatest element.
  [Ordered algebra and quotient][models]
  [Initial model][spec]

## Ordered LetCase bridge

`refinement_iff` preserves and reflects refinement between literal-unit
endpoints. `quotientIso` identifies the explicit quotient by mutual
refinement with the quotient of canonical native terms by the inherited
native order. The native presentation uses the full well-typed extended
dialect as syntax. Its generators are the relabelled original sentences and
`t ⊑ op (ub A) unit` for every native `t : A`. The proof uses monotone
constructor operations, retains the chosen primitive effect, and imposes no
purity requirement on it. Canonical elaboration always supplies literal unit,
so it never erases an effectful operand. Readback on arbitrary operands is
used internally to compare these generated axioms. [Bridge][case-refinement]

With the original sentences taken from `caseTheory`, `preserves_native`
also gives a derivation in LetCase's full native refinement calculus with
the transported primitive rules and the top rule. Reflection into the
original free extension fails for that stronger target. Native case beta
drops an unselected branch containing UB, even with effectful UB and
canonical endpoints. The Boolean occurrence model validates the interpreted
axioms and distinguishes the two terms. Its `true` is greatest and
`encode_eval` gives agreement with the induced explicit interpretation.
The flag includes both branches and describes UB occurrence in syntax.
[Model][case-model] [Checked counterexample][case-regression]

## Ordered LetIter bridge

LetIter's exact typing judgments have free and bound contexts and a result
type. They carry no usage quantities or effect bound. The literal-unit
round trip holds at each such sort, including the iteration body at
`β.snoc A` with result `B ⊕ A`. The chosen UB effect is preserved on
the native instruction. Readback is inverse on canonical terms, where
each fresh instruction has a literal unit operand. `refinement_iff` and
`quotientIso` compare the explicit and interpreted orders on those terms.
The latter is generated over the full native syntax by the relabelled
old sentences and a UB upper bound for each typed native term.
[Typed round trip][iter-ub] [Ordered bridge][iter-ub-refinement]

With inherited sentences from `iterTheory`, `preserves_native` embeds
the explicit order into the full native refinement rules. The checked
regression separates native fixpoint unrolling from the interpreted
axioms. Its two-point model ignores the iteration body when reading a
loop and reads the scrutinee when reading a case. The unrolling moves
the UB body into a scrutinee, so the native equation can give a
comparison the matched axioms do not entail. This model only witnesses
the algebraic separation. [Checked fixpoint example][iter-ub-regression]

Quantitative LetIter uses a separate typing judgment. At bound `b`,
`op (ub A) unit` typechecks exactly when `Γ.Discardable` and
`ubEffect ≤ b`. In the iteration rule, the ambient context `Γl`
already has `Γl.linearity = ⊤`. The body context `Γl.snoc A` is
discardable exactly when the incoming state's type admits discarding
(`Quantity.affine ≤ quantity A`). A linear state blocks literal-unit
UB in that body even at the top effect bound. The stable rewrite
presentation in `topRules` keeps formed endpoints under native
weakening and pure substitution. The comparison to literal UB holds
exactly for formed left endpoints in discardable contexts.
`typeIterLiteralBody` adds the ordinary iteration guard `iterable b`,
and `iter_body_refines_literal` uses native iteration congruence at the
original context split. [Quantitative typing and refinement][iter-ub-quant]

## LambdaSSA's empty-label boundary

In the exact LambdaSSA typing judgment, a region with no external labels
must contain a local block. `not_noLocalBlocks` excludes even regions that
wrap their bodies in zero-block CFGs. A unit-state CFG that branches to
itself gives a typed region at every value and label context. A unit-fed
instruction can be sequenced before that CFG, with the local backedge
ignoring its result. Exact LambdaSSA typing here has no quantitative
usage or effect-bound premise. [Typing][ssa-typing] [Witnesses][ssa-ub-defs]

`Refines` compares sets of return, fault and divergence observations by
inclusion in every model of the observational institution. In the
`faultModel` every primitive faults, with no successful primitive
transitions and no primitive divergence. The unit-fed prefix faults
and the bare CFG diverges. A simultaneous upper bound would need both
observations from the same initial state. Mutual induction through
nested CFGs and block traversal proves that fault and internal divergence
are exclusive when successful primitive steps are deterministic and a
faulting primitive call cannot also return. Thus `no_common_upper_bound`
and `no_greatest` hold for every exact typing interface of an alphabet
with a unit-taking operation. This includes the fresh `unit → A`
instruction in `UB.dialect P e`, for any effect label `e`. The obstruction
quantifies over all typed native regions, so it also bounds what can be
encoded using typed native substitution or feedback. [Observation order][ssa-observations]
[Obstruction][ssa-ub] [Dialect regression][ssa-ub-regression]

At a fixed model, an empty-label region has no finite return. Its
observations are contained in the set of all faults and divergences.
The unit-fed prefix attains that greatest set if its primitive can fault
from every initial state to every final state and can, at each initial state,
either diverge or return to the backedge. The regression instantiates this
with a model in which the instruction both faults and can diverge.
Greatest behaviour here is a law of that model. [Fixed-model result][ssa-ub]
[Model regression][ssa-ub-regression]

### Explicit region UB with substitution and feedback

The independent `Overlay.Region` embeds any exactly typed native region,
adds a UB region at every interface, and provides label substitution and
feedback. A continuation or block receives the exit payload in its own
value binder and retains the original captured context. Native regions may
contain arbitrary nested CFGs. [Overlay syntax][ssa-ub-overlay-defs]

For each observational model, bound environment and initial state, the
carrier is `WithTop (Set Outcome)`. An outcome carries a scoped exit and
payload, a fault state, or divergence. The refinement order is pointwise
subset on ordinary sets with a distinct greatest UB element. An ordinary
universal set stays ordinary. The projection back to native observations
recovers the original observations on every native region, and the embedding
preserves and reflects the original refinement preorder. [Conservativity][ssa-ub-overlay]

`lsubst_mono` proves directed congruence in the source and all continuations.
Sequencing propagates source faults and divergence and runs continuations
only on successful exits. UB in the source or a reached continuation lifts
the whole behaviour to greatest at that initial state. Substituting into UB
preserves UB even when the target has new labels. For all-native inputs,
`denote_native_lsubst` proves exact agreement with one typed dispatch CFG
whose blocks run the continuations, including faults, external divergence,
and internal divergence of the existing native regions. [Substitution laws][ssa-ub-overlay]

Using ordinary universal outcomes as UB would lose this absorption law.
An empty label interface has no successful exit, so ordinary sequencing
cannot turn even its universal set into a return at a target label.
The regression uses a native region that already has all empty-interface
outcomes in one model. Its ordinary projection equals the projection of
explicit UB at the source, yet their substituted projections differ at a
single-exit target. Thus ordinary outcome equality at a fixed model is
insufficient for a compositional interpretation with both native sequencing
and absorbing UB. The lifted order retains precisely the distinction used
in this counterexample. [Checked obstruction][ssa-ub-overlay-regression]

Feedback splits the outgoing interface as `R ++ L`. An ordinary return to
`R` invokes the corresponding local block with the returned payload and
machine state. A return to `L` exits. Fresh top occurs exactly when a finite
path of ordinary internal returns reaches a component at fresh top. Below
top, finite paths collect external returns and faults, and divergence comes
from a finitely reached component divergence or an actual infinite
sequence of internal returns. `feedback_mono` proves directed congruence
in the entry and all blocks, including refinements that expose UB earlier.
The top and ordinary parts also satisfy one-step unfolding.
[Feedback laws][ssa-ub-feedback]

For native entry and blocks, `denote_native_feedback` agrees with the
repository's typed recursive CFG at every existing observational model.
The regression checks a block whose first visit takes a backedge and whose
second visit reaches UB, an immediate exit that bypasses a UB block, and a
native self-loop whose divergence is absent from finite closure.
[Native agreement][ssa-ub-feedback] [Regressions][ssa-ub-feedback-regression]

Feedback uniformity compares two graphs with the same external interface.
The local theorem assumes that at each reachable source point, a
deterministic point map sends each source step to a target step and lifts
every step out of the image to a source successor with that exact image. The matched points must agree on
fresh UB and ordinary external returns, faults, and divergence. These
conditions are required only on reachable source points. They preserve and
reflect finite paths, reached UB, and actual infinite paths. The reverse
infinite proof lifts the selected target path one step at a time, choosing
a source successor at each step. The exact criterion for equality of
closed behaviours is agreement on whether UB is reachable and, below UB,
equality of the resulting ordinary outcome sets. [Uniformity][ssa-ub-uniformity]

A type-preserving label map keeps payloads and machine states and may merge
labels of the same type. `close_slide` proves the deterministic routing
instance of the Conway sliding law. Closing a body with routing on its
block inputs gives the same behaviour as closing it with routing on its
internal returns. Permutations give block relabeling invariance as a
corollary. The one-way counterexample preserves local marks and ordinary
outcomes on reached source points, yet a new target edge can expose UB or
enable infinite replay.
[Sliding and relabeling][ssa-ub-uniformity] [Checked counterexample][ssa-ub-uniformity-regression]

Two-level elimination views the same overlay semantics as a graph of
ordinary transfers, local UB and terminal observations. The graph's
one-shot closure agrees definitionally with `Feedback.close`. Closing
the inner group exposes each transfer to an outer point as a boundary
outcome, carrying the label, payload and machine state. The outer closure
consumes these boundary outcomes. `close_two_levels` proves equality
with the flat closure for the typed hidden interface `I ++ O`.
`close_partition` allows any partition of the invocations.

Finite paths split at outer visits. An outer step consists of zero or more
inner transfers and a final original edge into an outer point, so every
such step consumes at least one original edge. If a reachable inner UB
suppresses an otherwise available boundary transfer, the outer closure
already has a witness to UB. Below UB, the finite terminal comparisons
retain the original outcomes.

For a selected infinite flat path, either all visits after some index
are inner, or a later outer visit exists after every index. The proof
in the first case uses the finite prefix to reach the final inner replay.
In the second case `Nat.find` selects the least next outer visit, so the
intervals between selected visits are finite inner segments. In reverse,
an inner replay can be prefixed by the finite flattened outer path.
An infinite outer replay provides nonempty flat segments. Classical
choice selects a real successor at each original step, maintaining a
finite suffix to a segment boundary. The regressions exercise both kinds of
replay, a finite external outcome, and early UB in an inner segment.
Full Conway and Elgot laws remain open.
[Elimination theorem][ssa-ub-elimination] [Regressions][ssa-ub-elimination-regression]

### Descent through the native CFG entry quotient

`cfgDenotation` lifts the map `r ↦ denote (.native r)` through the
installed `Region.CfgQuotient` at each exact value and label interface.
`cfgEquiv_obs` covers empty CFG elimination, an outward entry branch,
and unfolding a local entry branch into its block. It uses the existing
observational congruences for lets, cases, and CFGs and preserves returns,
faults, and both sources of may-divergence in every observational model.
The descended map supports overlay substitution and recursive CFG assembly.
Semantic relabeling and two-level elimination apply to feedback over the
resulting quotient denotations. [Native quotient][ssa-cfg-quotient]
[Descent][ssa-ub-native-quotient]

The guarded `Paper.Hom` and the native `ContinuationHom` admit checked
counterexamples to the same representative contract. Paper's product η
identifies a split and rebuild with a direct return. A bound value of unit
at the product-typed input makes only the direct return succeed. Native
initiality identifies a return with an empty-typed elimination, which
the same model separates when it supplies unit at an empty-typed input.
Both witnesses have constructor-valued branch arguments and use no
primitive transitions. The observation model indexes bound values by scope
and imposes no payload shape. Shape-aware environments would exclude
these witnesses. The installed categorical soundness theorem for Paper
uses a coherent typed region denotation and its stated categorical
hypotheses. [Paper soundness][ssa-paper-soundness]
[Obstructions][ssa-ub-descent-obstruction]

The regressions check one UB-producing branch of a nondeterministic
producer, an outward CFG entry that bypasses blocks leading to UB after
substitution, and a local entry unfolding whose infinite replay remains
ordinary divergence. The outward example also checks semantic relabeling
and staged feedback on the native quotient inputs.
[Descent regressions][ssa-ub-descent-regression]

### Shape-respecting observations

Over the free type algebra `Ty κ`, the shaped model reuses the runtime
typing of the LambdaSSA resumption machine. The model assigns types to atoms
and requires every bound slot to have its declared type. Unit, pairs and
injections retain their runtime tags, and empty has no runtime inhabitant.
When a primitive succeeds on a source-typed argument, its payload must have
the target type. Fault and primitive-divergence relations have no reply
payload. The semantics uses the original observation relations and lifted
subset order. [Model][ssa-ub-shaped-model]

Finite evaluation preserves expression types and the payload type of each
native region exit, including through CFG blocks. In the overlay, reachable
ordinary returns carry the declared label type through substitution and
feedback. This uses finite path induction for feedback transfers. An
infinite path contributes divergence, and fresh UB is greatest in the
unchanged lifted order. [Preservation][ssa-ub-shaped-laws]

The installed variable product η step preserves the full lifted behaviour
at every shaped input and state. Native initiality's exact constructor-value
premise entails that the value context has no shaped model. The fixture
passes a primitive-produced pair through an internal CFG label, checks
product η on that payload, and exhibits a faulting empty-result primitive
that separates the equation when the constructor-value guard is dropped.
[Laws][ssa-ub-shaped-laws] [Fixture][ssa-ub-shaped-regression]

### Native continuation quotient in shaped models

`ContinuationHom` is the quotient of constructor-branch continuation
families by pointwise `SubstitutionEquiv`. At input label `i`, its shaped
denotation takes a model for the exact context `L.get i :: Γ` and uses the
native representative at the output interface `K`.
[Quotient][ssa-native-continuation] [Denotation][ssa-ub-shaped-continuation]

| Installed relation | Generators and closure used by the descent |
|---|---|
| `CfgEquiv` | `cfgZero`, `cfgBrExit`, `cfgBrLocal`, reflexivity, symmetry, transitivity, and congruence for let₁, let₂, case, and recursive CFG. These reuse the unrestricted native CFG observation proof. |
| `RewriteEquiv` | `entry` embeds `CfgEquiv`. `letBr` uses constructor-value substitution. `caseInl` and `caseInr` evaluate the same argument and select the same arm. The relation includes symmetry, transitivity, and the same four congruences. |
| `SubstitutionEquiv` | `base` embeds `RewriteEquiv`. `letValue` and `caseValue` use state-preserving constructor substitutions. `caseCfg` routes once into the selected arm. `cfgOutward` shifts every exit beyond the local blocks. `initial` requires a constructor value of empty type. The relation includes symmetry, transitivity, and the same four congruences. |

The shaped congruences check successful term replies before entering
let and case bodies. CFG entry and each successful backedge establish
the target label type. Finite execution and faults follow this invariant,
and coinduction carries it through infinite replay. Constructor-value
substitution preserves returns and final states, faults, and both
sources of divergence. The fixture reaches a rewritten block with either
tag from one nondeterministic primitive. One tag replays the backedge
and the other exits. The primitive can also fault.
[Regression][ssa-ub-shaped-continuation-regression]

### Guarded Paper collapse and simulation square

The exact `Paper.Eqv.collapsePost` generator preserves lifted observations
in shaped models. The theorem allows arbitrary typed outgoing
continuations, including effectful ones. It pushes the common literal
substitution through both CFG forms with the proper value and label lifts.
The operational proof then follows the native dispatch relation. A
two-label graph keeps both possible backedges before two-level elimination.
Its staged graph represents the nested CFG, while merging the labels
represents the flat CFG. Step transport in both directions retains the
payload and machine state. The native observations include successful
exits, faults, divergence inside a primitive or body, and infinite CFG
replay. The proof of the underlying duplicate-label observation law works
with arbitrary native primitive relations. [Collapse][ssa-ub-paper-collapse]
[Stateful regression][ssa-ub-paper-regression]

For `Paper.Eqv.uniform`, the installed premises guard the entry and source
body's branch arguments and give a constructor state map `a`. The target
body `q` is exactly typed and may have effects. The premise equates the
literal substitution of the lifted local map into the source body with
substitution of the lifted target body into `br 0 a`. The shaped lemmas
interpret the right-hand region as a single binding of `a` followed by
`q`. The whole left-hand region forwards each successful source exit
at the state the source reached. The local payload passes through `a`
and external payloads pass through unchanged. Under any nested CFG
the protected prefix keeps its dispatch labels and payloads. This
preserves all faults and both primitive divergence and internal replay.
[Installed rule][ssa-ub-paper-rewrite] [Forwarding][ssa-ub-paper-uniformity]

`uniform_of_observed_square` takes observational equality of the exact
literal square as its induction premise and proves equality for the
installed uniformity endpoints. A chosen target backedge with payload
`d′` and final state `s′` lifts to a source backedge ending at the same
`s′` with a payload that maps to `d′`. The typing invariant lets the
square be applied again at that source payload, even for a non-injective
state map. Forward transport alone permits additional target steps and can
add internal replay. [Uniformity][ssa-ub-paper-uniformity]
[One-way discriminator][ssa-ub-uniformity-regression]

`uniform_native_square` discharges the premise when the square has a
native `SubstitutionEquiv` derivation. The fixture checks the installed
Paper constructor with a native let-value rewrite in its square, a
non-injective constructor map, and effects inside a protected nested CFG.
It observes a return at the updated state, a fault, primitive divergence
and internal replay. [Native-square fixture][ssa-ub-paper-uniformity-regression]

### Shaped descent for the guarded Paper quotient

`Shape.Paper.eqv_denote` interprets all constructors of the installed
`Paper.Eqv` over free SSA types in shaped models. `Shape.Paper.denote`
descends to the existing continuation quotient `Paper.Hom` by applying
the theorem pointwise to exactly typed representatives. The proof assumes
typed environments and successful primitive replies of the declared type.
Primitive transitions may be nondeterministic and stateful, and the
fault and primitive divergence relations remain arbitrary.
[Shaped descent][ssa-ub-paper-descent]

| Installed constructors | Operational argument |
|---|---|
| `cfgEta` | Native substitution soundness covers the native subrelation. The separate `etaPost` step compares dispatch from the entry's selected payload, then runs the same arbitrary postcontinuation. |
| `productBeta`, `productEta` | The constructor pair has two pure components, bound in de Bruijn order. Product η uses the existing shaped product law. |
| `symm`, `trans`, `let₁`, `let₂`, `case`, `cfg` | Reuse observational congruence with typed replies at each reached binder or local block. |
| `lsubstCongr`, `lsubstPost` | A guarded literal substitution runs its continuation only after a successful producer exit, using that payload and final state. It preserves internal transitions and infinite replay, carries through producer faults and divergence, and admits new observations from a reached continuation. |
| `substVars`, `renameLabels` | Realize in-scope constructor images as a typed environment. Reflect label renamings through successful exits, preserving faults and divergence. |
| `collapsePost`, `uniform` | Reuse duplicate-label elimination and apply `uniform_of_observed_square` to the recursive hypothesis for the exact literal square. |

The stateful fixture also checks a uniformity square derived from Paper
product β and an instance of CFG η with an effectful postcontinuation.
The quotient maps native representatives to their ordinary observations
in the fresh-top overlay. The enriched Paper presentations have separate
generators and require their own soundness theorems.
[Regression][ssa-ub-paper-uniformity-regression]

### Guarded Paper category interpretation

For a fixed shaped model and captured environment, `Shape.Paper.interpretation`
maps the installed guarded `Paper.Interface` category to shaped
stateful observations. Objects carry exact label types. An arrow receives
a typed payload and a machine state and returns an existing lifted
`Behaviour`. Each ordinary return has the type of its exit label. Identity
returns the incoming label, payload and state. Composition uses
`Behaviour.bind`, which invokes the second arrow at the first arrow's final
state. Faults and may-divergence propagate, and fresh top propagates from
the first arrow or a reached continuation. The target satisfies both identity
laws and associativity. [Target category][ssa-ub-shaped-category]

The map on arrows is the descended `Paper.Hom` denotation at the chosen
typed payload. Its composition proof interprets the actual literal
`ContinuationFamily.compose` representative, including the weakening that
keeps the producer's input out of the second arrow's captures. The guarded
literal substitution theorem equates it with sequencing at the returned
state and payload. This preserves faults, primitive divergence, and
infinite CFG replay. The same functor restricts to the installed
empty-capture singleton category via `singletonInterpretation`.
[Functor][ssa-ub-paper-category]

The singleton regression runs a nondeterministic producer that updates
state from zero to one and a continuation whose successful execution
requires state one and returns at state three. It checks faults in both
arrows, a primitive divergence in the continuation, and infinite replay
in the producer. The source uses native representatives. Preservation of
structural operations and iteration is a separate question.
[Composition regression][ssa-ub-paper-category-regression]

### Exact sums and the empty type

The shaped observation category has a binary coproduct at the singleton
label of exact type `A ⊕ B`, with its universal property against any
shaped target interface. The injections return the chosen tag and keep
the state. Copairing passes the unwrapped payload and incoming state to
the selected arrow and returns its entire behaviour, including faults,
may-divergence, and fresh top. Every shaped sum payload is a left or right
tag with its declared type. The empty-typed singleton is initial because
it has no well-typed input. These facts follow from the free runtime
shapes for any atom typing relation.
[Target laws][ssa-ub-shaped-exact-sum]

The guarded singleton interpretation maps the installed exact injections,
copair and empty eliminator to these operations. The image of the exact
sum cocone is colimiting. The binary and initial proofs give the Mathlib
`PreservesFiniteCoproducts` property. The stateful regression takes the
installed Paper copair of two effectful arrows, checks distinct final
states and faults, and verifies that the right arm's fault and divergence
are absent from the left-tagged execution.
[Preservation][ssa-ub-paper-exact-sum] [Regression][ssa-ub-paper-exact-sum-regression]

### Product values and fixed-factor actions

The shaped singleton target identifies a product payload with a pair
of typed payloads. Building and splitting the pair are inverse. For
state-preserving value maps, pairing is pointwise and the two projections
determine it uniquely. The guarded singleton interpretation maps the
installed projections and diagonal to these value maps. It also maps
each constructor return to a value map and sends the installed
`pairArrows` to pointwise pairing whenever both interpreted legs are
certified to be value maps. The shaped model constrains successful
primitive reply types. An effect annotation alone supplies no operational
purity law. The regression gives a syntactically pure return whose
primitive changes the state in an admissible shaped model.
[Value laws][ssa-ub-shaped-product] [Preservation][ssa-ub-paper-product]

Both installed fixed-factor actions interpret over arbitrary guarded
singleton arrows. The active component starts at the incoming state.
Literal substitution repackages successful returns with the fixed
component and preserves their final state. Faults and may-divergence
pass through. The stateful regression checks that increment then double
returns state four from state one, and double then increment returns
state three, with the original tagged payload pair in both results.
It also checks pairing the projections in reverse order.
The product universal property here is for typed value maps.
[Regression][ssa-ub-paper-product-regression]

### Bind-first exact-sum iteration

The installed guarded singleton `iterateSum` for a step `A → B ⊕ A`
interprets as repeated observations of that step. The left tag returns
the payload and its final machine state. The right tag transfers that
payload and final state to the next invocation. The comparison uses the
one-label native CFG, guarded literal substitution, and the typed
payload invariant at reachable blocks. The one-step unfolding composes
the interpreted step with the exact-sum copair of identity and the
interpreted iterator.

Finite returns and faults agree in both directions. May-divergence is
either divergence in a finitely reached step or an infinite chain of
ordinary repeat observations. This uses the native CFG agreement theorem,
including its coinductive divergence proof. The interpreted native
arrows yield ordinary observations. The target closure retains its
reachable-top rule for general observation arrows. The comparison is
at the installed empty-capture exact-sum iterator. Its one-step law
follows from the guarded source law and exact-sum preservation.

The regression makes a state-changing request before a tag-producing
request. From state zero it repeats once before returning at state two,
faulting at state twelve, or diverging in the second step. From state
two it has an infinite chain of repeats.
[Preservation][ssa-ub-paper-iteration] [Regression][ssa-ub-paper-iteration-regression]

### Iteration refinement

The empty-capture `iterateSum` is monotone at each shaped model for
pointwise inclusion of complete step behaviours over typed inputs and
machine states. More permissive behaviours are on the right. Ordinary
outcomes use subset inclusion, and fresh UB is greatest. Retagging
preserves this order, so the repeated-observation comparison transports
the existing feedback monotonicity theorem to the guarded iterator.
An `Overlay.Refines` proof on typed step representatives supplies the
pointwise hypothesis in every shaped model.

A fault is a finite outcome at its exact final state. Divergence has
its own observation and can arise in a finite reached step or from an
infinite chain of repeats. With an ordinary upper behaviour each path
is matched at the same payload and intermediate state. If a reached
upper step exposes fresh UB, the upper closure is top.

The regression adds a fault while keeping the repeat to state one and
checks that the return survives. A second comparison matches every
step after erasing only the repeat's final state. Changing that state
from one to two removes the original return and reaches a fault
instead, so the erased comparison does not imply iterator refinement.
[Monotonicity][ssa-ub-paper-iteration] [Refinement regression][ssa-ub-paper-iteration-refinement]

### Exact-sum iteration of explicit overlay steps

An exactly typed overlay step with one input binder and one exact-sum
exit interprets directly as a shaped singleton arrow at a fixed capture
environment.
`iterateOverlay` closes that arrow through the existing directed feedback
and returns an arrow whose ordinary successful outputs have the result
type. The same `WithTop (Set Outcome)` carrier applies at each initial
machine state. `Overlay.Refines` on two steps implies pointwise
refinement of their iterators through the existing feedback order.

The closed behaviour is greatest exactly when finitely many ordinary
right-tagged repeats reach a step at fresh top, including zero repeats.
Every repeat carries a typed payload and its exact final machine state.
A start whose first step is ordinary and has no repeat sees exactly the
terminal observations of that step. With native representatives the
whole shaped arrow agrees with the installed guarded `iterateSum`,
including ordinary divergence.

The regression runs the same overlay step at two initial states. From
one it repeats at a new state and takes the explicit `ub` continuation,
so the result is greatest. From the other it returns at once, and its
exact ordinary singleton behaviour is independent of the unused
continuation. Replacing an ordinary continuation with `ub` is checked
as a typed refinement. This regression uses the empty-capture instance.
[Overlay iteration][ssa-ub-shaped-overlay-iteration] [Regression][ssa-ub-shaped-overlay-iteration-regression]
[Native agreement][ssa-ub-paper-iteration]

### Fixed capture packs

A step in context `[A, X]` can iterate on a product input `X × A`.
The outer product is unpacked once. Its left field supplies the fixed
capture of type `X`, which can itself contain products, and its right
field supplies the initial loop payload. Every right-tagged repeat
changes only the loop payload and machine state. Fresh top at an
initial input and state is equivalent to a finite path of such repeats
to a step at fresh top, with the original capture in scope throughout.
The existing `Overlay.Refines` order gives pointwise monotonicity.

At a fixed typed environment, the interpretation agrees with the
installed `CfgEta.TypeCategory.iterateSum` projected to Paper and with
`Paper.feedback` using the installed exact-sum dispatcher. For the
product input, the concrete native packing equation compares the
overlay arrow with `let₂ (var 0)` around that native iterator
representative. The body skips the original product slot after binding
the seed at slot zero and the capture at slot one. This equation keeps
the whole observed behaviour, including faults and both sources of
may-divergence. The product-input comparison uses one capture binder of
arbitrary exact type.

The literal-UB regression starts both runs with the same seed and
machine state zero. Both repeat with a changed payload at state one.
The first capture then reaches UB. The second reaches an ordinary
return at state two.
[Packed iterator][ssa-ub-shaped-capture-iteration] [Native comparisons][ssa-ub-paper-capture-iteration]
[Regression][ssa-ub-shaped-capture-regression]

### Certified finite deterministic iteration

The finite checker compares two overlay steps in the same shaped model.
Its carrier enumerates supported captures and pairs of loop payload and
machine state. The caller supplies executable tables and a certificate
that each row equals the complete observation of the corresponding
typed step. A repeat names another coded invocation under the same
capture. Returns and faults carry an exact final state. The result
payload and final-state decoders are injective, so comparison of the
codes reflects comparison of ordinary singleton observations.

The evaluator scans at most as many rows as there are invocation codes
along the deterministic path. If that scan sees only repeats, the path has
revisited a code and repeats forever. The proof constructs the infinite
feedback path and excludes any reachable terminal row or fresh UB.
This gives an ordinary divergence observation, which is also the
result of an in-step divergence row. A reached UB row instead yields
fresh top. Exact classification gives a Boolean decision for the
existing shaped observation order at every coded start, with more
permissive behaviour on the right. Each certified row must have exactly
one ordinary outcome or be fresh top. Empty and nondeterministic step
behaviours are outside this table presentation.

The certified regression reaches literal UB after a state-changing
repeat, follows a two-state cycle with no reachable UB, and checks an
ordinary fault and an in-step divergence. Replacing the UB continuation
with an ordinary return passes refinement toward the UB variant. The
reverse comparison fails.
[Checker and exactness][ssa-ub-finite-iteration] [Certified regression][ssa-ub-finite-regression]

## Coverage and gaps

| Language | Refinement and institutions in the repository | UB construction and remaining hypotheses |
|---|---|---|
| LetCase | The exact typed preorder gives `caseTheory` and ordered algebra models. The separate operational institution observes results, faults and divergence. | Instantiate the ordered monad with `casePSig` or the specification of `caseTheory`. `typedEquiv` proves both typed round trips between explicit UB and native terms generated with `op (ub A) unit`, including under binders. The interpreted order preserves and reflects on these endpoints. Arbitrary unit-typed operands can have effects, and an operational equivalence needs to preserve their evaluation and justify the sequencing and UB laws in the chosen observation model. [Ordered theory][let-theory] [Typed round trip][case] [Ordered bridge][case-refinement] [Observations][obs] |
| LetIter | `iterTheory` gives ordered refinement models. The separate quantitative `Refinement.Thms` also has categorical initiality and singleton-input completeness. Operational stuckness yields an undefined outcome, while the observational institution tracks returns, faults and divergence. | The exact literal-unit round trip and ordered quotient comparison include the iteration binder. Quantitative literal-unit UB is limited to discardable contexts and compatible effect bounds. A linear input would require a resource-consuming encoding or a different typing rule for UB. [Ordered theory][let-theory] [Ordered bridge][iter-ub-refinement] [Quantitative typing][iter-ub-quant] [Categorical initiality][quant] [Undefined outcome][iter-beh] |
| LambdaSSA | Typed terms use unary instructions and regions have separate value and label contexts. The CFG entry quotient uses `CfgEquiv`. The continuation quotients install additional equations. The observational institution has inclusion of outcomes, with an observational isomorphism to LetIter for single-exit regions. | The primitive monad supplies a unit-taking expression instruction. Every exact typing interface, including the empty-label boundary, has a countermodel to uniform greatest refinement by a native region. At a fixed model with the stated saturation assumptions the unit-fed prefix is greatest at the empty interface. The independent exact-typed overlay adds a distinct greatest element with monotone substitution and feedback, each with exact all-native CFG agreement. The overlay denotation descends through the native CFG entry quotient in all models and through native `ContinuationHom` and guarded `Paper.Hom` in shaped models over free types. [Continuation descent][ssa-ub-shaped-continuation] [Paper descent][ssa-ub-paper-descent] [CFG descent][ssa-ub-native-quotient] [Empty-label boundary][ssa-ub] [Explicit overlay][ssa-ub-overlay] [Feedback][ssa-ub-feedback] [Typing][ssa-typing] [Rewrite quotient][ssa-rewrite] [Observational isomorphism][ssa-obs] |
| LambdaRTL | The acyclic model interprets unary applications in a monad; its alphabet institution takes the observation relation as a parameter. It distinguishes lexical SSA, projected RTL and full RTL store observations. The separate machine RTL adapter reports stuckness as an undefined outcome. | A top region needs a chosen store/label observation order and a typed result and continuation interface. Its interpretation must dominate all observations for every environment at the selected boundary. An instruction relabelling or a lawful monad supplies no such law. [Syntax and model][rtl] [Institution][rtl-inst] [Machine RTL outcomes][rtl-beh] |

An effect bound of `⊤` permits all effects in the typing system. It does
not establish that any computation is greatest. The effect used for a fresh
primitive remains a parameter, and assigning the pure effect would also
invoke existing purity obligations. For a
behaviour-set model one can ask for the existing convention exemplified by
MIR's `ubClose_of_undefined`, which yields the universal outcome set.
Neither the monadic model interfaces nor weak interaction-tree equivalence
provide that UB order or its sequencing laws. [Effect system][effects]
[Empty elimination][quant-typing] [MIR UB closure][mir] [Kleisli model][kleisli]
[Weak-tree semantics][weak-tree]

## Checks

```sh
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Refinement.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.ExactSum.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Product.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Refinement.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Capture.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Regression
```

[ordered]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Ordered.lean
[obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Basic.lean
[compiler]: compiles-to.md
[primitive]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Primitive/Thms.lean
[instr]: ../../Silmaril/Raw/SSA/Isotope/Institution/InstrSig.lean
[sigmap]: ../../Silmaril/Raw/SSA/Isotope/Morphism/Instructions/Signature.lean
[syntax]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Syntax/Defs.lean
[signature]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Thms.lean
[spec]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Specification/Thms.lean
[institution]: ../../Silmaril/Logic/Institution/Theory.lean
[models]: ../../Silmaril/Raw/SSA/Isotope/Logic/Metatheory/Theory/OrderedModel.lean
[case-typing]: ../../Silmaril/Raw/SSA/Isotope/LetCase/LocallyNameless/Typing.lean
[ssa-syntax]: ../../Silmaril/SSA/Isotope/LambdaSSA/Defs.lean
[case-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Thms.lean
[case-model]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Model/Thms.lean
[case-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Regression.lean
[case]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Thms.lean
[let-theory]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Isotope.lean
[iter-ub]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Thms.lean
[iter-ub-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Refinement/Thms.lean
[iter-ub-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Regression.lean
[iter-ub-quant]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Quantitative/Thms.lean
[quant-typing]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Typing.lean
[quant]: ../../Silmaril/SSA/Isotope/Refinement/Thms.lean
[iter-beh]: ../../Silmaril/Raw/SSA/Isotope/LetIter/Semantics/Behaviour.lean
[ssa-typing]: ../../Silmaril/SSA/Isotope/LambdaSSA/Typing/Defs.lean
[ssa-rewrite]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Syntactic/Defs.lean
[ssa-obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Isomorphism.lean
[rtl]: ../../Silmaril/SSA/LambdaRTL/Defs.lean
[rtl-inst]: ../../Silmaril/SSA/LambdaRTL/Institution/Defs.lean
[rtl-beh]: ../../Silmaril/Raw/Machine/RTL/Behaviour.lean
[effects]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Effects.lean
[mir]: ../../Silmaril/Raw/Compiler/Mir/Semantics.lean
[kleisli]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Kleisli/Thms.lean
[weak-tree]: ../../tests/ssa/LetIterWeakTreeSoundness.lean
[ssa-observations]: ../../Silmaril/SSA/Isotope/Institution/Observational/Thms.lean
[ssa-ub-defs]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Defs.lean
[ssa-ub]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Thms.lean
[ssa-ub-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Regression.lean
[ssa-ub-overlay-defs]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Defs.lean
[ssa-ub-overlay]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Thms.lean
[ssa-ub-overlay-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Regression.lean
[ssa-ub-feedback]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Thms.lean
[ssa-ub-feedback-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Regression.lean
[ssa-ub-uniformity]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Uniformity/Thms.lean
[ssa-ub-uniformity-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Uniformity/Regression.lean
[ssa-ub-elimination]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Elimination/Thms.lean
[ssa-ub-elimination-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Elimination/Regression.lean
[ssa-cfg-quotient]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Syntactic/Defs.lean
[ssa-paper-soundness]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/Soundness/Thms.lean
[ssa-ub-native-quotient]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Thms.lean
[ssa-ub-descent-obstruction]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Obstruction/Thms.lean
[ssa-ub-descent-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Regression.lean
[ssa-ub-shaped-model]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Defs.lean
[ssa-ub-shaped-laws]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Thms.lean
[ssa-ub-shaped-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Regression.lean
[ssa-native-continuation]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Category/Defs.lean
[ssa-ub-shaped-continuation]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Continuation/Thms.lean
[ssa-ub-shaped-continuation-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Continuation/Regression.lean
[ssa-ub-paper-rewrite]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/Defs.lean
[ssa-ub-paper-collapse]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Thms.lean
[ssa-ub-paper-uniformity]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Uniformity/Thms.lean
[ssa-ub-paper-descent]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Descent/Thms.lean
[ssa-ub-shaped-category]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Thms.lean
[ssa-ub-paper-category]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Thms.lean
[ssa-ub-paper-category-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Regression.lean
[ssa-ub-shaped-exact-sum]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/ExactSum/Thms.lean
[ssa-ub-paper-exact-sum]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/ExactSum/Thms.lean
[ssa-ub-paper-exact-sum-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/ExactSum/Regression.lean
[ssa-ub-shaped-product]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Product/Thms.lean
[ssa-ub-paper-product]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Product/Thms.lean
[ssa-ub-paper-product-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Product/Regression.lean
[ssa-ub-paper-uniformity-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Uniformity/Regression.lean
[ssa-ub-paper-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Regression.lean
[ssa-ub-paper-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Thms.lean
[ssa-ub-paper-iteration-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Regression.lean
[ssa-ub-paper-iteration-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Refinement/Regression.lean
[ssa-ub-shaped-overlay-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Thms.lean
[ssa-ub-shaped-overlay-iteration-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Regression.lean
[ssa-ub-shaped-capture-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Capture/Thms.lean
[ssa-ub-paper-capture-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Capture/Thms.lean
[ssa-ub-shaped-capture-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Capture/Regression.lean
[ssa-ub-finite-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/Thms.lean
[ssa-ub-finite-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/Regression.lean
