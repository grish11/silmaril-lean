# LambdaIter family and flat CFG semantics

The two flat graph representations below have different variable interfaces. The forward
three-address graph uses named registers and a shrinking suffix of a block list. The typed
Isotope graph uses positional variables and finite labels, with a shared captured context and a
typed payload per label. The suffix semantics can report an earlier label as an exit. The finite
Isotope graph can instead follow cyclic internal edges.

**Scope.** “Absent” refers to the identified current headers and implementation files in the
row. “Not audited” leaves the question open. The model hypotheses listed here govern the stated
comparisons.

| Calculus or boundary | Syntax, semantics and models | Translations, institutions and missing comparisons |
| --- | --- | --- |
| LetSeq | [Locally nameless syntax](../../Silmaril/Raw/SSA/Isotope/LetSeq.lean), proof-relevant typed [monadic denotation](../../Silmaril/Raw/SSA/Isotope/LetSeq/Semantics/Monadic.lean), and [`eval_iff_denote`](../../Silmaril/Raw/SSA/Isotope/LetSeq/Semantics/OperationalDenotation.lean) for finite outcomes. The comparison uses `StateT σ SetM`, a compatible instruction relation and matching encoded free and bound environments. [`syntacticModelIsInitial`, `semantic_iff`](../../Silmaril/Raw/SSA/Isotope/Theory/Models/LetSeq.lean) concern operation algebras satisfying the base equations. | [`LetSeq.inst`](../../Silmaril/Raw/SSA/Isotope/Institution/LetSeq.lean) gives the equational institution. [`seqCaseCoHom`](../../Silmaril/Raw/SSA/Isotope/Institution/Inclusions.lean) has [unconditional borrowing](../../Silmaril/Raw/SSA/Isotope/Institution/Borrowing.lean). The inclusion preserves [typed monadic denotation](../../Silmaril/Raw/SSA/Isotope/Morphism/SeqCase/Monadic.lean) and preserves and reflects [operational evaluation](../../Silmaril/Raw/SSA/Isotope/Morphism/SeqCase/Operational.lean). Full Freyd categorical initiality and an ITree comparison were not audited. |
| LetCase | [Locally nameless syntax](../../Silmaril/Raw/SSA/Isotope/LetCase.lean) with sums and case; proof-relevant typed [monadic denotation](../../Silmaril/Raw/SSA/Isotope/LetCase/Semantics/Monadic.lean). [`eval_iff_denote`](../../Silmaril/Raw/SSA/Isotope/LetCase/Semantics/OperationalDenotation.lean) has the same comparison hypotheses as LetSeq. [`syntacticModelIsInitial`, `semantic_iff`](../../Silmaril/Raw/SSA/Isotope/Theory/Models/LetCase.lean) concern the base equational algebras. | [`LetCase.inst`](../../Silmaril/Raw/SSA/Isotope/Institution/LetCase.lean), [`caseIterCoHom`](../../Silmaril/Raw/SSA/Isotope/Institution/Inclusions.lean) and [unconditional borrowing](../../Silmaril/Raw/SSA/Isotope/Institution/Borrowing.lean). The inclusion has [monadic](../../Silmaril/Raw/SSA/Isotope/Morphism/CaseIter/Monadic.lean) and [operational](../../Silmaril/Raw/SSA/Isotope/Morphism/CaseIter/Operational.lean) agreement. [`CaseSSA`](../../Silmaril/Raw/SSA/Isotope/Morphism/CaseSSA.lean) embeds expressions into Isotope λSSA with [operational agreement](../../Silmaril/Raw/SSA/Isotope/Morphism/CaseSSASemantics.lean). Full Freyd categorical initiality and an ITree comparison were not audited. |
| LetIter | [Proof-relevant `sound` and `categorical_denote_eq`](../../Silmaril/SSA/Isotope/LetIter/Thms.lean) compare equations and their Kleisli arrows for lawful Elgot monads. [Thesis categorical models](../../Silmaril/SSA/Thesis/Categorical/Thms.lean) give initiality into their strong Elgot Freyd models with the thesis model laws and typing coherence. The two formulations have an [explicit bridge](../../Silmaril/SSA/Isotope/Bridge/Thms.lean). [Closed let-η counterexample](../../Silmaril/SSA/Isotope/LetIter/Counterexample/Thms.lean) limits soundness for the weaker unrestricted exact categorical interface. | [`LetIter.inst`](../../Silmaril/Raw/SSA/Isotope/Institution/LetIter.lean) is equational. [`iterSSAIso`](../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Isomorphism.lean) is an isomorphism after the observational quotient, for single-exit λSSA. [`Silmaril.Semantics.ITree`](../../Silmaril/Semantics/ITree/Thms.lean) supplies a lawful Elgot model and [`ITree.Interpret.initial`](../../Silmaril/Semantics/ITreeInterpret/Thms.lean) gives unique interpretation for a handler into a lawful Elgot monad under the tree smallness hypothesis. The [written-source tree development](../../Silmaril/SSA/Isotope/LetIter/PaperExpression/Source/FreeTree/Response/Thms.lean) has its own hypotheses and observations. Its full coverage was not audited here. |
| Acyclic λSSA and acyclic λRTL | The named [`Region`](../../Silmaril/SSA/LambdaRTL/Defs.lean) has lexical `evalSSA` and mutable `evalRTL`. The instruction `Model` is over one value carrier with monadic operations and total input stores. [`evalObs_eq_evalSSA` and `evalObs_eq_evalSSA_of_isSSA`](../../Silmaril/SSA/LambdaRTL/Thms.lean) drop the final store and assume `LawfulMonad` plus `NoClobber` or `IsSSA`, respectively. | [`ssaToRTL`](../../Silmaril/SSA/LambdaRTL/Institution/Defs.lean) goes from SSA to the observation-only RTL institution. `rtlFull` observes the final store as well. [`versionTop_evalSSA`](../../Silmaril/SSA/LambdaRTL/Version/Thms.lean) and [`versionCoHom`](../../Silmaril/SSA/LambdaRTL/Version/Institution/Defs.lean) go in the other direction using initial version zero and `unpair (pair a b) = pure (a, b)`. A typed store model and categorical interpretation are absent from these headers. |
| λSSA with general CFGs | Isotope [`Region` and `Region.Eval`](../../Silmaril/SSA/Isotope/LambdaSSA/Defs.lean) use positional variables and jumps. [`Region.denote`](../../Silmaril/Raw/SSA/Isotope/LambdaSSA/Denotation/Monadic/Region.lean) uses exact typing, typed label coproducts and Elgot iteration. The [categorical graphs](../../Silmaril/SSA/Isotope/LambdaSSA/Categorical/Thms.lean) use distributive Freyd structure with strong Elgot iteration for regions. [`categoricalTermDenote_eq` and `categoricalRegionDenote_eq`](../../Silmaril/SSA/Isotope/LambdaSSA/Kleisli/Thms.lean) specialize to Kleisli models with the corresponding typing-coherence premises and a lawful Elgot monad for regions. | The [observational compilations](../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Compilations.lean) and quotient isomorphism above use operational observations. [Machine RTL](../../Silmaril/Machine/RTL/Thms.lean) is a separate SSA-form register machine; `toLambdaSSA_eval_iff` assumes a matching call oracle, and [`ofLambdaSSA_eval_iff`](../../Silmaril/Machine/OfLambdaSSA/Thms.lean) is restricted to `RootFits`. A general typed operational-to-monadic adequacy theorem for this row was not audited. |
| λRTL with loops | [`Loop.Region`](../../Silmaril/SSA/LambdaRTL/Loop/Defs.lean) extends the named syntax with a self-recursive handler. [`Loop.Region.evalObs_eq_evalSSA_of_isSSA`](../../Silmaril/SSA/LambdaRTL/Loop/Thms.lean) uses a lawful Elgot monad and the loop SSA judgment. | [`acyclicToLoopSSA` and `loopSSAToRTL`](../../Silmaril/SSA/LambdaRTL/Loop/Institution/Defs.lean) are comorphisms at the exit/payload observation. A lowering of those loops to the forward CFG is absent from these headers. |
| Flat typed SSA | [`FiniteCFG.HasType` and `erase_hasType_iff`](../../Silmaril/Raw/SSA/Isotope/LambdaSSA/Flat.lean) relate heterogeneous block arguments and typed exits to ordinary λSSA CFG typing. [`encodeCFG_hasType`](../../Silmaril/Raw/SSA/Isotope/Morphism/SSAIter/Encode.lean) checks the finite-sum LetIter encoding. | [`encodeCFG_eval`](../../Silmaril/Raw/SSA/Isotope/Morphism/SSAIter/Correctness.lean) preserves finite evaluation under matching captured environments and the same primitive relation. [`encodeCFG_diverges`](../../Silmaril/Raw/SSA/Isotope/Morphism/SSAIter/Divergence.lean) is the forward divergence comparison. A translation between this representation and the named forward graph is absent from the cited modules. A separate flat institution and an ITree-specific adequacy result were not audited. |
| Forward flat SSA / mutable RTL | [`CFG`, `flatten`, `toRegion`, `run`](../../Silmaril/SSA/LambdaRTL/CFG/Defs.lean) operate on explicit block arguments. [`run_flatten` and `run_eq_toRegion`](../../Silmaril/SSA/LambdaRTL/CFG/Thms.lean) preserve the full mutable result in a lawful monad. | [`validate_obs_eq_evalSSA`](../../Silmaril/SSA/LambdaRTL/CFG/Version/Thms.lean) requires validator acceptance and a dominance-scoped source region. `validate_versionTop_obs` replaces source SSA with the pair law and version-zero input. Both compare to the existing **region** semantics. At the audited baseline, a direct lexical runner for forward blocks was absent. Classical φ syntax, global name uniqueness, cyclic flat lookup and a flat CFG institution are outside this bridge. |

The public thesis formalization provides a separate reference point. Its
[`TypedDominanceWellFormedFlat`](https://github.com/imbrem/thesis/blob/69a8126f2d3eb6d32050e0bd9511251b33dbcea7/formalization/thesis/Isotope/TAC/Bridge/DomFlatSemantics.lean)
denotes via a typed chosen dominator tree. `CoherentReordering` carries the evidence that
the reorderings have equal lexicalizations. The thesis also proves a direct complete-Elgot
[`denote_convert_cfg`](https://github.com/imbrem/thesis/blob/69a8126f2d3eb6d32050e0bd9511251b33dbcea7/formalization/thesis/Isotope/TAC/Densem/MonadicValid.lean)
for its φ-free classical source CFG, assuming the model's failure law and an input defined
on the source variables. These use the thesis graph and store definitions.

## Forward CFG agreement

`CFG.runSSA` executes the same forward block list as `CFG.run`. It gives each
selected block the graph's original environment and the incoming parameter.
The mutable runner instead extends the store at the jump site. The same suffix
order governs both runners, including when a label is repeated.

```mermaid
flowchart LR
  A["Forward RTL CFG"] -->|"CFG.versioned"| B["Forward SSA CFG"]
  A -->|"CFG.toRegion"| C["Acyclic λRTL region"]
  B -->|"CFG.toRegion"| D["Acyclic λSSA region"]
  C -->|"Version.versionTop"| D
```

The vertical paths preserve the mutable result and the lexical result,
respectively, by `CFG.run_eq_toRegion` and `CFG.runSSA_eq_evalSSA`. The names and
labels have decidable equality, and both comparisons use a lawful monad.
`CFG.versioned_toRegion` states the exact equality
`g.versioned.toRegion = Version.versionTop g.toRegion`.
`CFG.versioned_runSSA` uses it to give the same exit label and payload from
either path, assuming the pair law and source inputs at version zero.
`CFG.versioned_isSSA` gives dominance-scoped SSA, and
`CFG.versioned_blockLabels` preserves the ordered block-label list including
repetitions.
[Flat versioning header](../../Silmaril/SSA/LambdaRTL/CFG/Version/Flat/Thms.lean)

`CFG.ofRegion?` recognizes precisely the image of `CFG.toRegion`. It peels
outer joins to recover the block list and keeps conditional terminators inline.
The existence proof shows that structured versioning preserves this image.
At runtime the total `CFG.versioned` runs the structured versioner and the
reifier, using an erased proof that the reifier succeeds. This preserves
the original labels and the forward suffix lookup convention, including
targets absent from the current suffix.
[Reifier definitions](../../Silmaril/SSA/LambdaRTL/CFG/Version/Flat/Defs.lean)

For running the **same** CFG in both modes,
`CFG.runSSA_eq_obs_of_isSSA` uses the readback's `IsSSA` judgment with the same lawful monad.
[Forward CFG theorem header](../../Silmaril/SSA/LambdaRTL/CFG/Lexical/Thms.lean)

The diamond regression has two named branch blocks and a shared join. The
unversioned mutable graph returns 12 or 21 after overwriting a live-in, whereas
reading the same graph lexically leaves the original value 7 at the join. The
generated flat graph passes the new value in its jump argument and gives
the two mutable results. The regression checks that the generator returns
the expected block list and both runs compute directly on that output.
[Checked regression](../../Silmaril/SSA/LambdaRTL/CFG/Lexical/Examples/Thms.lean)

```sh
lake build --wfail Silmaril.SSA.LambdaRTL.CFG.Version.Flat.Thms \
  Silmaril.SSA.LambdaRTL.CFG.Lexical.Examples.Thms \
  Silmaril.SSA.LambdaRTL.CFG.Version.Examples.Thms
```
