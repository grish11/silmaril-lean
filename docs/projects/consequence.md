# Consequence systems: core API

This page covers the core of `Silmaril.Consequence`: what is defined, what is proved, and
which modules own what. The master roadmap for consequence systems, which covers all four
tracks (core, structural derivations, Wasm/SZS protocols, explorer), is
[consequence-systems.md](consequence-systems.md). Plans live there; this page describes the
API.

## The objects

A consequence system is a relation between contexts and conclusions:

```lean
abbrev System (Ax : Type u) (C : Type v) := Ax → C → Prop     -- S a c : "a ⊢ c"
abbrev WSystem (Ax : Type u) (C : Type v) := Ax → C → Type w  -- witnesses of a ⊢ c
def WSystem.erase (W : WSystem Ax C) : System Ax C := fun a c => Nonempty (W a c)
```

`Ax` and `C` are independent types. A context does not have to be a collection of
conclusions, and **no structural rule is assumed**: reflexivity, weakening, cut, contraction
and exchange all have to be stated as hypotheses. The core supplies one such hypothesis,
`MonoWrt r S` (monotone along a relation `r` you pass explicitly), and its `Preorder` case
`AxMono`. Structural closures belong to the structural-derivations track.

Because `System` is an `abbrev`, the order and lattice structure come from Mathlib's pointwise
`CompleteBooleanAlgebra` on `Ax → C → Prop`, with no instances of our own:

| notation | meaning (`Thms`) |
|---|---|
| `S ≤ T` | `∀ a c, S a c → T a c` (`le_iff`) |
| `⊥`, `⊤` | nothing is proved, everything is proved |
| `S ⊔ T`, `S ⊓ T`, `S \ T`, `Sᶜ` | pointwise or, and, and-not, not |
| `sSup F`, `sInf F` | proved by some member of `F`, proved by every member of `F` |

`S.Sound T := S ≤ T` and `S.Complete T := T ≤ S` compare `S` with a reference system `T`.
Both together are equality (`sound_and_complete_iff_eq`).

## Four "everything follows" notions

These are separate definitions because they come apart:

| name | statement | scope |
|---|---|---|
| `Universal S` | `∀ a c, S a c`, i.e. `S = ⊤` | the whole system |
| `ProvesAll S a` | `∀ c, S a c` | one context (inconsistent or trivial) |
| `ContextConsistent S a` | `¬ ProvesAll S a` | one context |
| `ProvesFalse S ff a` / `ConsistentWrt S ff a` | `S a ff` / `¬ S a ff` | one context, relative to a chosen `ff` |

* `ProvesAll` always implies `ProvesFalse`. The converse holds exactly under
  `Explosive S ff` (`Explosive.provesFalse_iff`), and `not_explosive_ex` gives a system where it
  fails.
* Empty domains:
  * With `IsEmpty C`, every context proves everything, no context is consistent, and `⊥ = ⊤`.
  * With `IsEmpty Ax`, every system is universal.
  * Bottom-relative consistency needs some `ff : C`, so it cannot even be stated over an empty
    `C`.

## Reindexing and translations

`S.pullback f g` reindexes along `f : Ax' → Ax` and `g : C' → C`. It is functorial
(`pullback_id`, `pullback_comp`), monotone, and preserves `⊥ ⊤ ⊔ ⊓ \`.

A `Translation S T` consists of maps `ax`, `c` with `S ≤ T.pullback ax c`. It is
conservative when `T.pullback ax c ≤ S` as well.

* `Sys`, the bundled systems, form a Mathlib `Category` whose morphisms are all **sound**
  translations. Conservativity is a separate predicate on a translation (`Conservative`,
  closed under identity and composition); the category does not require it.
* `WSys` and `WTranslation` (which also map witnesses) form a category too, and
  `WSys.erase : WSys ⥤ Sys` is a functor.
* `Sys.forget : Sys ⥤ Type u × Type v` is faithful.
* A translation with given maps exists iff the inclusion into the pullback holds, and it is
  then unique (`nonempty_translation_iff`). Every translation factors through the conservative
  `toPullback` (`factor_toPullback`).

## Context shapes

| shape | `Ax` | maps from finer shapes, and what they forget |
|---|---|---|
| `SingleSystem C` | `C` | — |
| `ListSystem C` | `List C` | `ctxSingle : C → List C` (forgets nothing) |
| `NamedSystem N C`, `NatNamedSystem C` | `N → Option C` | `ctxNamed : List C → ℕ → Option C` (forgets nothing; positions become names) |
| `FinsetSystem C` | `Finset C` | `ctxFinset : List C → Finset C` (forgets order and multiplicity) |
| `SetSystem C` | `Set C` | `ctxSet : Finset C → Set C` (forgets finiteness); `ctxRange : (N → Option C) → Set C` (forgets names, order, multiplicity) |

The injectivity and non-injectivity facts are proved (`Ax/Thms`). So are the weakening
orders each map respects: `List.Subset` maps to `⊆`, `NamedLE` maps to `⊆`, and a prefix
maps to `NamedLE`. Weakening orders are always passed to `MonoWrt` explicitly, because the
`≤` on `List` is lexicographic.

## Semantics, rooms, institutions, SZS

A `Satisfaction Ax C` has its own type of models and two **independent** relations, `satAx`
and `satC`. Its consequence system is `entails a c := ∀ m, satAx m a → satC m c`.

* **SZS.** `entails a c` is the THM status of `problem a c` (`entails_iff_thm` in the current
  ontology, `entails_iff_thm2007` in the 2007 text). A failure is CSA (`not_entails_iff_csa`).
  CAX implies `ProvesAll`. When `ff` has no models, CAX is the same as proving `ff`
  (`cax_iff_provesFalse`), and `provesAll_ne_cax_ex` shows that this hypothesis is needed.
* **Monotonicity is a hypothesis.** `entails_monoWrt` needs `satAx` to be antitone along the
  relation, and nothing makes an arbitrary satisfaction monotone.
* **Morphisms.** A `Satisfaction.Hom` maps contexts and conclusions forwards and models
  backwards, with a satisfaction condition for each relation. It gives a sound translation,
  functorially (`Hom.toTranslation_id`, `Hom.toTranslation_comp`). If the model map is
  surjective, the translation is conservative.
* **Rooms (fixed-signature institutions).** `roomSatisfaction R` has contexts `Set R.Sen`, and
  its entailment is `Room.Entails` (`roomSatisfaction_entails`). A corridor gives a morphism
  through its satisfaction condition, and `roomSys : Room ⥤ Sys` is a functor. This is the
  only place where institution laws are used, and they are the corridor's satisfaction
  condition. Model morphisms are forgotten.
* **Institutions.** The target is the existing category `Room.category`
  (`Silmaril.Logic.Institution.Room`), where corridors translate sentences forwards and reduce
  models backwards.
  * An institution `I : Sign ⥤ Room` gives `institutionSys I := I ⋙ roomSys`, one system per
    signature and one translation per signature morphism.
  * A `ClassicInstitution` (`Sen : Sign ⥤ Type`, `Mod : Signᵒᵖ ⥤ Cat`) goes through
    `toRoomFunctor` to `classicInstitutionSys`. Its system at `Σ` is `(I.room Σ).Entails`, and
    `σ` translates conclusions by `I.Sen.map σ`, both by `rfl`.
  * The result is covariant in signatures. The model functor enters only through the
    satisfaction condition.

## Multiple conclusions and signed formulas

`MultiSystem C D := System (List C) (List D)`: `Γ ⊢ Δ`, with **conjunction on the left and
disjunction on the right**. A raw multi-system has no structural rule. Weakening defaults to
membership inclusion: `WeakL`, `WeakR`, `Weak`. Order- and multiplicity-sensitive weakening
stays opt-in through `MonoWrt` with `List.Sublist` or `List.Subperm`.

| name | meaning |
|---|---|
| `M.single` | the restriction to singleton succedents, `Γ ⊢ [d]` |
| `rightExt R` | `∃ d ∈ Δ, R Γ d`, the least right-weak extension of a single-conclusion `R` (`rightExt_le_iff`); it never proves `[]` |
| `multiEntails satC satD` | every model of all of `Γ` satisfies some member of `Δ` |
| `roomMulti R`, `corridorMulti f` | the room version, and its translation along corridors (functorial) |
| `posPartAlong e M`, `posPart M` | the part of `M` on formulas embedded by an explicit `e`; for `Signed`, `e := pos` |

* `rightExt` is not the semantic completion. In `rightExt_ne_multiEntails`, `⊢ [true, false]`
  holds semantically, but neither `⊢ true` nor `⊢ false` does.
* Empty sides:
  * `Γ ⊢ []` says that `Γ` has no model, i.e. the conjunction is inconsistent
    (`multiEntails_nil_right`).
  * `⊢ Δ` says that the disjunction is valid (`multiEntails_nil_left`).

`Signed A` (`pos a`, `neg a`) has Mathlib's `InvolutiveNeg`, and `negateEach l` negates every
member of a list.

* An arbitrary involutive negation may have fixed points, so it does not single out the
  positive formulas. That is why positive parts always go through an explicit embedding.
* `Signed` really does decompose: `Signed.eq_of_isPos_atom` and `Signed.neg_ne_self`.
* For heterogeneous `C` and `D`, `SignedCarrier C D A` holds the explicit maps into one carrier,
  and nothing more is assumed.
* The structural modules own the conversions `Γ ⊢ Δ` ↔ unsatisfiability of
  `Γ ++ negateEach Δ` (and the tautology form).

## Acceptors

A language `L : Set _` (the convention of `Silmaril.Accept`) lifts to a system in four ways.
Each lift is the least system with its property (`…_le_iff`):

| lift | judgements | language recovered as |
|---|---|---|
| `liftAxFF L ff` | `a ⊢ ff` for accepted `a` | `{a | a ⊢ ff}` |
| `liftTTC tt L` | `tt ⊢ c` for accepted `c` | `{c | tt ⊢ c}` |
| `liftAxAll L` | `a ⊢ c` for accepted `a`, every `c` | `{a | ProvesAll a}`, only if `C` is nonempty |
| `liftCAll L` | `a ⊢ c` for every `a`, accepted `c` | `{c | a ⊢ c}` for any `a` |

### Acceptor values, interpreters and encoded programs

The lifts above take one language. A CSLib acceptor type `X` (`Cslib.Automata.Acceptor X α`,
whose values accept words `List α`) is itself a system with acceptors as contexts, and so are
the interpreters that read programs as acceptors (`Acceptor/`):

| view | system | `· ⊢ w` holds iff |
|---|---|---|
| `System.ofAcceptor X` | `System X (List α)` | `x` accepts `w` |
| `System.ofInterpreter interp` | `System W (List α)` | `interp m` accepts `w` |
| `System.ofDecoder decode interp` | `System B (List α)` | `decode b = some m` and `interp m` accepts `w` |

The row `{w | x ⊢ w}` of a context is its language (`ofAcceptor_row`, `ofInterpreter_row`), so
`≤` between interpreter systems is language inclusion program by program
(`ofInterpreter_le_iff`). `ofInterpreter interp` is `(ofAcceptor X).pullback interp id`; along
an encoder that the decoder inverts, the bytes system restricts to the program system
(`ofDecoder_pullback_of_roundtrip`). Bytes that do not decode prove nothing
(`ofDecoder_of_eq_none`), the same row as a program that accepts nothing; keep an `Interp`
when the difference matters. One acceptor as the only context is `liftCAll` of its language
(`pullback_const_ofAcceptor`).

For Wasm (Lean names relative to `Silmaril.Wasm.Game.Accept` and `Silmaril.Wasi.Accept`):

| view | module | component | either shape |
|---|---|---|---|
| acceptor | `ofAcceptor ModuleAcceptor` | `ofAcceptor ComponentAcceptor` | `ofAcceptor ByteAcceptor` |
| interpreter | `A.withModule` | `ComponentAcceptor.interp C L acc rej mode` | `ByteAcceptor.interp A I` |
| program system | `A.moduleSystem` | `ComponentAcceptor.compSystem C L …` | `ByteAcceptor.programSystem A I` |
| bytes system | `A.bytesSystem` (`Binary.Core.decode?`) | `ComponentAcceptor.binarySystem C L …` (`parseComponent`), `bytesSystem … decode` | `ByteAcceptor.bytesSystem A C L …` |

A template `ModuleAcceptor` `A` is the module interpretation: profile, `accept`/`reject`
imports, memory, address width and environments; `A.withModule m` replaces only the module.
Component interpretations take a core semantics `C : CoreSem M` and a layout `L`. The library
fixes no `CoreSem` for the lowered `CoreMod` of `parseComponent`, whose lowering is partial and
unverified, so the component byte systems take `C` as a parameter. The either-shape decoder
tries the core decoder first, then the component one. Examples:
`Silmaril/Logic/Consequence/Acceptor/Examples.lean` (a toy acceptor) and
`Silmaril/Wasi/Component/Accept/Consequence/Examples.lean` (the empty-module binary, the
specification component).

## Institutions, logics and their propositions

`roomSys` (`Set Sen ⊢ Sen`) and `roomMulti` (`Sen* ⊢ Sen*`) already read a room as a system.
`Institution/` adds the list form, syntactic entailment, and point-wise semantics:

| construction | system | semantics |
|---|---|---|
| `roomSeq R` | `Sen* ⊢ Sen` | every model of all of `Γ` satisfies `φ` (= `Room.Entails` on the members) |
| `roomMulti R` | `Sen* ⊢ Sen*` | every model of all of `Γ` satisfies **some** `δ ∈ Δ` (= `Gentzen.Valid R.Sat`) |
| `institutionSeq I σ`, `corridorSeq f` | translations | reindexing along signature morphisms / corridors |
| `ER.listSys E`, `LogicalSystem.listSys L S` | `Sen* ⊢ Sen` | syntactic (Tarskian) entailment; `≤ roomSeq` when `L` is sound |
| `Refutation.Entails (localSat sat)`, `Gentzen.Valid (localSat sat)` | point-wise | one valuation satisfies the premises and the (some) conclusion |
| `… (validIn sat)` | model-wise | validity in a model (every valuation) |

Closure: every `Refutation.Entails sat` is `Structural.Closed tarskiRules` (reflexivity, `⊆`-weakening,
hence exchange and contraction, and multi-cut); every `Gentzen.Valid sat` is
`Gentzen.Closed defaultRules` (reflexivity, `⊆`-weakening of both sides, cut). Maps with a
satisfaction condition (`valid_map_of_sat`, `entails_map_of_sat`) are the reusable
reindexing/substitution lemma. Point-wise single conclusion is below model-wise
(`entails_localSat_le_validIn`). The converse fails, and the two multiple-conclusion systems are
incomparable (`Institution/Examples.lean`). **A model-wise succedent is not a disjunctive (LK)
succedent.**

### HOL (`HOL/`)

The HOL institution's sentences are sequents `H ⊢ p`, satisfied valuation by valuation. At the
level of propositions `HOLProp S` (bool-typed terms):

| system | Lean | reading |
|---|---|---|
| `HOLProp* ⊢ HOLProp` | `HOL.seq S` | HOL Light's sequent semantics: `seq_iff_entails`, `seq_iff_valid_toSeq` (`Γ ⊢ p` valid in the institution) |
| `HOLProp* ⊢ HOLProp*` | `HOL.gentzen S` | LK: one valuation, disjunctive succedent; `gentzen_single : gentzen.single = seq` |
| model-wise | `HOL.globalSeq S`, `HOL.globalGentzen S` | consequence between hypothesis-free sentences `⊢ p` (`globalSeq_iff_roomSeq`) |

Closure, all proved for `seq` and `gentzen`: structural (`seq_closed`, `gentzen_closed`,
`seq_exchange`, `seq_contraction`), signature extension (`seq_map`, `gentzen_map`), type
instantiation (`seq_tySubst`, `gentzen_tySubst`) and term instantiation (`seq_freeSubst`,
`gentzen_freeSubst`). Soundness: `derives_le_seq` (HOL Light kernel, pure logic) and
`logic_listSys_le_roomSeq` (sequent level). `HOL/Examples.lean` proves, over the initial
signature, `x ⊢ y` in `globalSeq` but not in `seq`, and `⊢ x, ¬x` in `gentzen` but not in
`globalGentzen`.

### Dependent type theory: the lambda cube (`Silmaril/Calculi/LambdaCube/Consequence/`)

There is no Martin-Löf type theory in the library. The dependent corners of the lambda cube
(`lambdaP` … `cc`) are the existing dependent institutions, and their sentences are judgements
`Γ ⊢ t : A`, `Γ ⊢ t ≡ u : A` that carry their own dependent context. `Semantics.seq M`
(`roomSeq`) relates lists of whole judgements. It is Tarski-closed in that outer list
(`seq_closed`) and never splits `Γ`. `derivableSys c` is theoremhood: it weakens and cuts, is
below every semantics (`derivableSys_le_seq`), and is monotone in the corner. Reflexivity is not
claimed. There is deliberately no Gentzen instance. `admissible c` (examples) is the one-model
semantics whose `seq` is admissibility.

### Gaps

* HOL: no completeness (standard semantics is incomplete for the kernel). No proved
  `Γ ⊢ Δ ↔ Γ ⊢ ⋁Δ` for HOL's defined disjunction. The kernel bridge `derives_le_seq` covers
  only the empty object theory.
* No `Sys`-valued functor for `roomSeq` (only translations per morphism) and no reflection of
  consequence along corridors.
* Lambda cube: no hypothetical-judgement calculus (judgements as premises of derivations), no
  concrete model of a dependent corner, and no substitution closure for judgements.

## Interpretations

`Interp Env Value Ax C := (e : Env) → Value → Option (System (Ax e) (C e))` reads a value, under a
typed configuration, as a system (`Interp/`).

* `Env` is static configuration: an export or function index, an ABI, a profile, a set of
  hosts. `Interp₀` is the case without configuration (`Env = PUnit`). How a runtime host
  behaves is modelled separately and enters only through `Env` or `Value`. `Ax` and `C` are
  families over `Env`, in independent universes.
* `none` means the value cannot be read, for example because it does not parse. `some ⊥` is a
  system, verified to prove nothing.
  * `sysOrBot` (and `Interp.orBot`) is the explicit projection that sends `none` to `⊥`. It
    loses the difference (`sysOrBot_not_injective`).
  * The registry's `artifactSystem X I` is `sysOrBot (X.parse.map I)` (`sysOrBot_map_iff`).
  * No lattice is claimed on `Option (System …)`; only raw systems form one.
* Operations: `ofDecode`, `map`, `pullback`, `reindex`, `comap`.
  * `pullback` commutes with the projection.
  * A general `map f` commutes only if `f ⊥ = ⊥`, and there is a counterexample without it.
* Evidence against a specification `ref`: `SoundFor`, `CompleteFor`, and `CompleteOnFor P`,
  which is completeness on a slice such as a size bound.
  * These quantify over defined readings only.
  * Soundness can be read off the projection.
  * Completeness can be read off the projection only given definedness, stated as a premise
    (`Defined`).
  * Evidence of this kind never shows that a reading is defined. That a value can be read at
    all (in the registry, that the artifact decodes and its interpretation is defined) needs its
    own certificate.

## Shapes

Descriptors for shape filters (`Shape/`):

| shape | meaning | recovers the system as |
|---|---|---|
| acceptor, `System Unit C` | a language of conclusions (`acceptorEquiv`, an order isomorphism) | `liftTTC ()`, `liftCAll` |
| rejector, `System Ax Unit` | by convention, the contexts deriving the unique bottom (`rejectorEquiv`) | `liftAxFF · ()`, `liftAxAll` |
| `SupportedAx S tt` | only `tt` proves anything | `S = liftTTC tt (ttSlice S tt)` |
| `SupportedC S ff` | only `ff` is ever proved | `S = liftAxFF (ffSlice S ff) ff` |
| `ContextFree S` | proofs do not depend on the context | some `liftCAll L` |
| `ConclusionFree S` | each context proves all or nothing | some `liftAxAll L`; `L` is unique only if `C` is nonempty |

Outside these shapes a slice does not determine the system (`slice_counterexample`).

Checker predicates on list contexts (`ListPred`):

* `SetInv` (depends only on the members) implies `PermInv`. The converse fails: the predicate
  `length = 1` is a counterexample.
* `UpClosed` (closed under membership weakening) is `SetInv ∧ AppendExtensive`.
  `AppendClosed` (closed under concatenation) is a different property: the predicate `l = []`
  has it but is not extensive.
* `SetInv` is exactly factoring through `List.toFinset`.
* `finExt` is an explicit, non-canonical extension of a checker predicate to sets. It is false
  on infinite sets.

Raw `System` stays rule-free. Bundled, proof-carrying closed systems and rule bundles belong to
the structural modules (`Structural/`, `Gentzen/`), and `MultiSystem` is the raw type of
Gentzen sequents.

## Modules and ownership

| module | contents | owner |
|---|---|---|
| `Silmaril/Logic/Consequence/Defs.lean`, `Thms.lean` | systems, order, consistency notions | core |
| `Silmaril/Logic/Consequence/Translation/{Defs,Thms}.lean` | translations, `Sys`, `WSys`, erasure functor | core |
| `Silmaril/Logic/Consequence/Ax/{Defs,Thms}.lean` | context shapes and their maps | core |
| `Silmaril/Logic/Consequence/Semantic/{Defs,Thms}.lean` | satisfaction, SZS, rooms, institutions | core |
| `Silmaril/Logic/Consequence/Accept/{Defs,Thms}.lean` | acceptor lifts | core |
| `Silmaril/Logic/Consequence/Acceptor/{Defs,Thms,Examples}.lean` | CSLib acceptors, interpreters and decoders as systems | core |
| `Silmaril/Logic/Consequence/Institution/{Defs,Thms,Examples}.lean` | list-premise room systems, logics, point-wise vs model-wise | core |
| `Silmaril/Logic/Consequence/HOL/{Defs,Thms,Examples}.lean` | HOL propositions: `seq`, `gentzen`, closure | core |
| `Silmaril/Logic/Consequence/Signed/{Defs,Thms}.lean` | signed formulas, `negateEach`, carriers | core |
| `Silmaril/Logic/Consequence/Multi/{Defs,Thms}.lean` | multiple conclusions, `rightExt`, `multiEntails`, rooms | core |
| `Silmaril/Logic/Consequence/Interp/{Defs,Thms}.lean` | interpretations, projection, evidence | core |
| `Silmaril/Logic/Consequence/Shape/{Defs,Thms}.lean` | acceptor/rejector shapes, slices, checker predicates | core |
| `Silmaril/Logic/Consequence/Examples.lean` | worked examples | core |
| `Silmaril/Logic/Consequence/Structural/…` | structural rules and derivation closures | structural derivations |
| Wasm acceptor and SZS protocol modules | Wasm evidence for the lifts | Wasm/SZS protocols |
| explorer pages, [consequence-systems.md](consequence-systems.md) | presentation and master roadmap | explorer/examples |

## Next steps for the core

* Reindexing as a functor between fibres, using the order category of `System Ax C`. Mathlib
  gives `Ax → C → Prop` its pointwise `Pi` category first, so this needs an explicit
  order-category wrapper and was left out instead of being stated for the wrong category.

* A signature-indexed version of `Satisfaction` (a functor `Sign ⥤` satisfactions) whose
  restriction to rooms is `institutionSys`.
* Whether conservative translations reflect `ProvesAll` and `ConsistentWrt`, and which
  structural properties pullbacks preserve, once the structural track has fixed its closures.
