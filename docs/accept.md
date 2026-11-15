# Acceptance: generic languages, checkers and verdicts

`Silmaril.Semantics.Accept` (namespace `Silmaril.Accept`, region `Semantics`, Mathlib only)
is the generic vocabulary for saying that a checker, a program or a runner *accepts* a set of
values. It contains nothing specific to WebAssembly, WIT or bytes; those developments
instantiate it.

A language over `α` is Mathlib's `Set α`: there is no wrapper type, so all of Mathlib's set
lattice, images and preimages apply directly.

## Stable API

These names are intended for downstream integration; changes go through review.

### `Silmaril.Semantics.Accept.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `ofBool check` | `{a \| check a = true}` |
| `Sound check L` | `∀ a, check a = true → a ∈ L` |
| `Complete check L` | `∀ a, a ∈ L → check a = true` |
| `Decides check L` | `∀ a, check a = true ↔ a ∈ L`; `decides_iff` (sound ∧ complete), `decides_iff_ofBool_eq` |
| `checker L` | `decide (· ∈ L)`; `decides_checker` |
| `acceptsSome run acc` | some outcome of `run a` is in `acc` (existential acceptance) |
| `acceptsAll run acc` | every outcome of `run a` is in `acc` (vacuous with no outcome) |
| `rejectsSome run rej` | some outcome of `run a` is in `rej` |
| `neverRejects run rej` | no outcome of `run a` is in `rej` (universal safety) |
| `detRun f` | the runner `fun a => {f a}` of a total function |
| `upTo size n L` | members of `L` with `size a ≤ n` |

Key laws: `compl_rejectsSome` (never-rejection is the complement of *some* rejection, not of
acceptance), `compl_acceptsSome`, `acceptsAll_subset_neverRejects` (needs disjoint verdicts),
`acceptsAll_subset_acceptsSome` (needs every input to have an outcome),
`neverRejects_not_subset_acceptsSome` (an input with no outcome separates them), the
deterministic collapse `acceptsSome_detRun`/`acceptsAll_detRun`/`neverRejects_detRun`,
`Decides.and`/`or`/`not`/`comp`/`upTo`, and `iUnion_upTo`/`eq_iff_upTo_eq` for size slices.

### `Silmaril.Semantics.Accept.Order.Defs` / `Thms`

Programs of any carrier `X`, compared by `lang : X → Set α`.

| Name | Meaning |
| --- | --- |
| `LangPre lang` | type synonym of `X`, **preorder** `x ≤ y ↔ lang x ⊆ lang y`; `LangPre.of`, `.val`, `.toLang` |
| `LangPre.map f hf` / `LangPre.embed f hinj hf` | monotone map / order embedding along a language-preserving (injective) `f` |
| `LangPre.subtypeEmb p` | sub-carrier `Subtype p` as an order embedding |
| `langSum l₁ l₂`, `inlEmb`, `inrEmb` | two shapes `X ⊕ Y` in one preorder; inclusions are order embeddings |
| `langSigma lang`, `sigmaEmb lang i` | a family of shapes `Σ i, X i` |
| `RespectsLang s lang` | class: `s x y → lang x = lang y` |
| `LangQuot s lang` | `Quotient s` with the descended language; a **preorder** (`mk_le_mk_iff`) |
| `LangQuot.toLangEq` | monotone, order-reflecting, surjective comparison with `LangEq`; injective iff `s` identifies all equal-language programs (`toLangEq_injective_iff`) |
| `LangEq lang` | `Quotient (Setoid.ker lang)`, a **partial order** (`mk_eq_mk_iff : mk x = mk y ↔ lang x = lang y`) |
| `LangEq.toSetEmb`, `LangEq.rangeIso`, `LangEq.antisymmIso` | `LangEq lang ↪o Set α`, `≃o Set.range lang`, `≃o Antisymmetrization (LangPre lang) (· ≤ ·)` |

Shapes are disjoint as programs, but not up to language: `inl_antisymmRel_inr_iff` and
`LangEq.mk_inl_eq_mk_inr_iff` show that a left and a right program are identified exactly when
their languages agree. A supplied equivalence must be proved to respect the language
(`RespectsLang`) before its quotient carries an order.

Examples: `Silmaril/Semantics/Accept/Order/Examples.lean`.

### `Silmaril.Semantics.Accept.Bounded.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `within μ b` | `{a \| μ a ≤ b}` for a measure `μ : α → β` into any preorder (length, format depth, pairs of them via `within_prod`) |
| `SoundOn D c L` | `∀ a ∈ D, c a = true → a ∈ L` |
| `CompleteOn D c L` | `∀ a ∈ D, a ∈ L → c a = true` |
| `DecidesOn D c L` | `∀ a ∈ D, (c a = true ↔ a ∈ L)`; outside `D` the checker may answer anything |

Laws: `decidesOn_iff`, `decidesOn_univ` (and the sound/complete versions) recover the
unrelativised notions; `SoundOn.anti`/`CompleteOn.anti`/`DecidesOn.anti` (smaller domain),
`DecidesOn.within_mono` (smaller bound), `SoundOn.mono`/`CompleteOn.mono` (language),
`…union`/`…iUnion`; exhaustion `complete_of_forall_within`/`decides_of_forall_within`;
`decides_inter_iff : Decides c (L ∩ D) ↔ DecidesOn D c L ∧ Sound c D` and
`DecidesOn.andBound` for checkers that enforce their bound; `upTo_eq_inter_within`.

Bounded completeness is a modelling choice, not a law of the library. A one-shot interface
with a fixed input buffer can only be complete on inputs that fit. A streaming checker can be
complete on inputs of unbounded total size. A semantic specification needs no bound, and an
executable total checker may or may not need one. Use `Decides` when the checker is complete
everywhere and `DecidesOn (within μ b)` when it is complete only up to a bound.

Examples: `Silmaril/Semantics/Accept/Bounded/Examples.lean` (a toy document format with
depth, a total checker and a depth-enforcing one).

### Choosing a quantifier

* A *validator* or *parser* that must accept the value: `acceptsSome` (some run succeeds) or,
  for a deterministic checker, `Decides`.
* A *safety* property (“this input never makes the program reject/trap”): `neverRejects`.
  It holds vacuously for inputs with no outcome, so it does not imply acceptance.
* A *robust* acceptance (“every run accepts”): `acceptsAll`.

Examples and regression tests: `Silmaril/Semantics/Accept/Examples.lean`.

### `Silmaril.Semantics.Accept.Rel.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `α -|> β` | scoped notation (`open scoped Silmaril.Accept`) for Mathlib's `SetRel α β = Set (α × β)` |
| `outcomes R` | `fun a => {b \| (a, b) ∈ R}`, the runner of a relation |
| `pullSome R L` | `R.preimage L`: some output in `L` |
| `pullAll R L` | `R.core L`: every output in `L` (vacuous with none) |
| `ofPartial f` | relation of `f : α → Option β` (`f a = some b`) |
| `ofTotal f` | `Function.graph f` |
| `partialComp f g` | Kleisli composition `fun a => (f a).bind g` |
| `pdom f` | `{a \| (f a).isSome}` |
| `IndexedLang A` | `∀ i, Set (A i)` |
| `eraseSigma L` / `fiberLang M` | to and from `Set (Σ i, A i)`; `indexedLangIso` is an order isomorphism |
| `eraseSome L` / `eraseAll L` | `⋃ i, L i` / `⋂ i, L i` over a common carrier |

Rejection quantifiers: `neverRejects (outcomes R) rej = pullAll R rejᶜ`;
`compl_pullSome : (pullSome R L)ᶜ = pullAll R Lᶜ`; for a partial function, `none` is in every
`pullAll` and no `pullSome` (`mem_pullAll_ofPartial_of_none`,
`not_mem_pullSome_ofPartial_of_none`), and `pullSome_ofPartial_eq`/`pullAll_ofPartial_eq`
relate them through `pdom`. `not_mem_eraseSome` (rejected at every index) and
`not_mem_eraseAll` (rejected at some index). Composition: `pullSome_comp`, `pullAll_comp`,
`ofPartial_partialComp`, `ofTotal_comp`, `ofPartial_some_comp`. Checkers:
`Decides.optionAny`, `Decides.optionAll`, `Decides.sigma`, `Decides.fiber`.

Examples: `Silmaril/Semantics/Accept/Rel/Examples.lean`.

### `Silmaril.Semantics.Accept.Success.Defs` / `Thms`

Successful-value projections of relations whose outputs carry a status (`Option`, `Except`,
or a sum with `inl` = `ok`, the convention of the WIT `result<T, E> ↦ T ⊕ E` interpretation
in `Silmaril/Wasm/Component/Reference/WIT/Interp/Defs.lean`).

| Name | Meaning |
| --- | --- |
| `succ f R` | `R ○ ofPartial f` for an extractor `f : γ → Option β`: outputs `c` with `f c = some b`, as `b` |
| `optionOk` | `id : Option β → Option β` |
| `exceptOk` / `exceptErr` | `.ok b ↦ some b` / `.error e ↦ some e` (`exceptOk_eq_toOption`) |
| `sumOk` / `sumErr` | `inl b ↦ some b` / `inr e ↦ some e` (`sumOk_eq_getLeft?`) |
| `someVals R` | `succ optionOk R`; `mem_someVals : (a, b) ∈ someVals R ↔ (a, some b) ∈ R` |
| `okVals R` / `errVals R` | `succ exceptOk R` / `succ exceptErr R`; `mem_okVals`, `mem_errVals` |
| `inlVals R` / `inrVals R` | `succ sumOk R` / `succ sumErr R`; `mem_inlVals`, `mem_inrVals` |

Laws: failures are dropped (`not_mem_dom_succ`: an input whose outputs all fail is outside
`(succ f R).dom`; `not_mem_dom_someVals`/`okVals`/`inlVals`; `mem_dom_succ`); functoriality
`succ_comp : succ g (succ f R) = succ (partialComp f g) R`, `succ_some`, `succ_mono`,
`succ_union`, `succ_empty`; `succ_ofPartial : succ f (ofPartial g) = ofPartial (partialComp g f)`,
`succ_ofTotal : succ f (ofTotal g) = ofPartial (f ∘ g)`; pullbacks
`pullSome_succ : pullSome (succ f R) L = pullSome R {c | ∃ b ∈ L, f c = some b}` and
`pullAll_succ`; `succ_single` (single-valued `R` gives single-valued `succ f R`, stated
directly).

Limitations: `succ` only *drops* failures. Whether an input fails on every run, on some run,
or has no run at all is not distinguished by `succ f R`; keep `R` (or use `errVals`) to see
failures. In particular `pullAll (succ f R) L` holds vacuously for inputs that always fail.

Examples: `Silmaril/Semantics/Accept/Success/Examples.lean`.

Byte languages, simple WIT types and the inputs accepted by Wasm modules and components
instantiate this vocabulary: see [accepted inputs](projects/accepted-inputs.md).

### `Silmaril.Semantics.Accept.Func.Defs` / `Thms`

The functional shape of a relation `R : α -|> β`, for example the (input, output) pairs
observed from program traces.

| Name | Meaning | Mathlib / CSLib bridge |
| --- | --- | --- |
| `Total R` | every input has an output (left-total) | `Relator.LeftTotal`, `R.dom = univ`, CSLib `Relation.Serial` (homogeneous) |
| `SingleValued R` | at most one output per input (right-unique) | `Relator.RightUnique`, `∃ f : α →. β, f.graph' = R` |
| `Surjective R` | every output is produced (right-total) | `Relator.RightTotal`, `R.cod = univ` |
| `Injective R` | an output determines its input (left-unique) | `Relator.LeftUnique`, `SingleValued R.inv` |
| `Functional R` | `Total R ∧ SingleValued R` | `∀ a, ∃! b, a ~[R] b`, `∃! f, Function.graph f = R` |
| `OneToOne R` | `Functional R ∧ Injective R ∧ Surjective R` | `OneToOne (ofTotal f) ↔ Function.Bijective f` |
| `toPartial R` | classical choice of an output, `none` if there is none | `ofPartial (toPartial R) = R` if single-valued; `toPartial (ofPartial f) = f` |
| `toFun h` | classical choice of an output, for `h : Total R` | `Function.graph (toFun h) = R` if single-valued; `toFun_ofTotal` |

`SingleValued R ∧ Injective R ↔ Relator.BiUnique`. `ofPartial f` is single-valued, total iff
`pdom f = univ`, and injective iff `Set.InjOn f (pdom f)`; `ofTotal f` is functional,
surjective iff `Function.Surjective f`, injective iff `Function.Injective f`. Composition
(`○`) preserves all four notions; `R.inv` swaps `Total` with `Surjective` and `SingleValued`
with `Injective`; subsets preserve `SingleValued` and `Injective`, supersets `Total` and
`Surjective`. Pullbacks: `SingleValued.pullSome_subset_pullAll`,
`Total.pullAll_subset_pullSome`, `Functional.pullSome_eq_pullAll`.

Examples (total but not single-valued, single-valued but not total, injective but not
surjective, surjective but not total): `Silmaril/Semantics/Accept/Func/Examples.lean`.

### `Silmaril.Semantics.Accept.IO.Defs` / `Thms`: relational I/O acceptance

Namespace `Silmaril.Accept.IO`. A program that reads inputs and writes outputs accepts a
*relation*. "Input `a` triggers output `b`" is defined by **scopes** (call IDs or protocol
boundaries), not by temporal order: only events of the same scope are related, so outputs of
interleaved invocations, of nested/reentrant calls, and outputs before the input are not
attributed to it.

| Name | Meaning |
| --- | --- |
| `Ev K X I O C` | role-decoded event of scope `k : K`: `enter k x` (entry point invoked, `x : Option X`, `none` = unobserved), `inp k i`, `out k o`, `exit k c` (`c : Option C`, `none` = trap/abort/undecoded) |
| `localView k t` | the events of scope `k`, in order (`Loc X I O C`) |
| `Run I O C` | `input`, `outputs` (in order), `result : Option C` |
| `windows l` | one run per input occurrence: outputs after it up to the next input or the exit; result the exit's value when the scope exits first |
| `entryRun l` | the run of an observed entry: argument as input, all outputs of the scope, return value |
| `inputRuns t` / `entryRuns t` | runs over all scopes of a trace (computable) |
| `inputRunsOf T` / `entryRunsOf T` | runs of a trace model `T : Set (List (Ev …))` |
| `ScopeViews T` | the local views of `T`; runs depend only on it (`inputRunsOf_congr`) |
| `triggers S` | (1) `(a, b)`: some run with input `a` outputs `b` (every occurrence, returned or not) |
| `episodes S` | (2) `(a, (bs, c))`: a run with input `a` output exactly `bs` then returned `c` |
| `retTriggers S` | (3) `(a, b, c)`: `b ∈ bs` for an episode `(a, (bs, c))` |
| `returns S` | (4) `(a, c)`: classic input/return relation (outputs forgotten) |
| `Tag`, `bracket`, `decode dec` | scope assignment for well-bracketed traces by a stack (IDs = position of `enter`) |

Key laws: `mem_windows`, `mem_inputRuns`, `mem_entryRuns`, `localView_insert_other`,
`inputRuns_congr` (interleavings with equal local views have equal runs), `returns_eq_image`,
`triggers_of_mem_retTriggers`, `image_retTriggers_eq` (needs every run to return; a trapped run
is a counterexample in `Examples`), `mem_episodes_iff_run`, transport `triggers_image_map`,
`episodes_image_map`, `returns_image_map`, monotonicity.

Choosing the reading: an *imported* `input()` (or `input(a)`) whose value drives later
imported `output(b)` calls is the window reading (`inputRunsOf`); an *exported* `f(a)` is the
entry reading (`entryRunsOf`). The decoder decides which raw events have which role, so both
call directions are explicit in the decoded data. Successful-value projections of `Option` or
`result`-like returns compose with a partial function (`SetRel.comp R (ofPartial f)`).

Limits: `bracket` assumes well-bracketed traces (nested calls close before their callers);
asynchronous or overlapping calls need a decoder that supplies call IDs and uses `Ev`
directly. The decoder must tag every scope-opening and -closing event (`enter none` for
unobserved entry points). Within a scope, the window reading attributes an output to the most
recent input; a protocol with another causal structure needs its own decoder. Examples:
`Silmaril/Semantics/Accept/IO/Examples.lean`.
