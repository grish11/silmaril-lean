# Wasm institutions and the Wasm logic graph

This page describes the module-level Wasm logic graph. It has three parts:

- **Phase 1**: the reduction semantics of Core and Binaryen IR modules.
- **Phase 2A**: reduction semantics versus game semantics, on `Silmaril.Games`.
- **Phase 2B**: modules versus components, on `Silmaril.Wasm.Component`.

The finite converse `Games.Task.wasmRed_le_of_finite_beh` is stated as a proposition. It is
neither an axiom nor a proved theorem, and the graph results do not use it. Every comorphism
edge of the three-part `CompGraph.fullGraph₂` is model-expansive. This does not hold for every
later graph on this page: `DivGames.entryToRed` is a translation whose model-expansiveness is
not claimed. Flattening uses `Silmaril.Wasm.Component.pairLaws`; wrapping uses
`Components.wrapAdequate C` (`wrap_denU`) and `PairInr.pair_restrict_inr`.

The construction builds on the institutions of `Silmaril.Logic.Institution` (and its
`Hets.LogicGraph`) and on the Wasm notions of `Silmaril.Wasm.Binaryen.Behaviour`,
`Silmaril.Wasm.Binaryen.Equiv`, `Silmaril.Wasm.Binaryen.Contracts`,
`Silmaril.Wasm.Binaryen.PassAPI.Instances` and `Silmaril.Wasm.Equiv.Module`.

Function-level institutions (reasoning about the bodies of functions *within* a module, with
a focus on one function, a set, all functions or an abstract hole) are described in
[wasm-fn-institutions.md](wasm-fn-institutions.md) (`Silmaril.Wasm.FnInst`).

## Terminology

An **institution** packages signatures, sentences, models and satisfaction with a
change-of-signature law. A **comorphism** sends signatures and sentences forwards and models
backwards. **Model-expansive** means every source model is reached by that backwards map; this
supports preservation and reflection of consequence (**borrowing**). A sound **morphism** here
reads corridors in the opposite direction, with the appropriate sentence translation.

An **interface** selects visible exports. A **session** retains a store across a script,
whereas the grounded `wasmRed` resets to the same store for every question. **CoreSem** in
phase 2B is a supplied abstract strategy semantics, not an adequacy theorem for the Core
semantics.

## Source map

All modules are under `Silmaril.Wasm.Institution` unless stated otherwise; proofs are under
`Silmaril.Proofs.Wasm.Institution`.

| Claims | Declarations |
| --- | --- |
| Signatures, scoped formulas, semantic assignments and satisfaction | `Generic.Defs`: `Sig`, `ObsSemantics`, `Sen`, `Sat`, `sat_map_iff`, `valid_leSen_iff` |
| Translation directions, satisfaction and surjectivity | `Generic.Defs`: `Translation`, `sat_sen_iff`, `coHom_modelExpansive`, `entails_iff`, `valid_iff`, `toHom_sound` |
| Sessions, closure and Binaryen pass correspondence | `Session.Defs`, proofs `Session.Basic`: `Obj`, `Refines`, `refines_close_iff`, `passEquivValid`, `passEquivValidEquiv`, `soundPass_iff_valid`; the pass correspondence retains `BModule.Ok` preservation and assumes `m.Ok` |
| Single-invocation objects and validity | `Entry.Defs`, proofs `Entry.Basic`: `Obj`, `Refines`, `entryRef`, `entryEquiv`, validity and closure lemmas |
| Twelve phase-1 nodes, edges and projections | `Graph.Defs`: `Node`, `Edge`, `Proj`, `edgeT`, `edgeT_surjective`, `pathModelExpansive`, `valid_bir_trapsUB_iff_core_eq` |
| Graph extension and sums | `Hooks.Defs`: `LogicGraph.extend`, `sum`, `Graph.Hook`; sums allow supplied first-to-second cross comorphisms, extensions allow supplied incoming edges; expansiveness needs the stated edge hypotheses |
| Strategies, reduction and LTS translations, simulation | `Games.Defs`, proofs `Games.Basic`: `GameIfaces`, `stratSem`, `redToGame`, `ltsToGame`, `valid_of_simulation`, `valid_game_of_simulation` |
| Core grounding and the stated finite converse | `Games.Defs`, proofs `Games.Wasm`: `wasmRed`, `instEntry`, `Task.wasmRed_le_of_finite_beh`, `mem_wasmRed_iff`, `finite_beh_of_le` |
| Three-node graph and disconnected sum | `GameGraph.Defs`: `gameGraph`, `fullGraph`, `fullGraph_pathModelExpansive` |
| Abstract component semantics, wrapper and passes | `Components.Defs`, proofs `Components.Basic`: `compIfaces`, `modU`, `wrap`, `CoreSem.ofReduction`, `passEquivValid`, `programPassEquivValid`, `valid_fuse`, `valid_deadExports`, `valid_flatten` |
| Wrapper proof and right projection | proofs `Components.Wrap`: `wrap_denU`, `wrapAdequate`; proofs `Components.PairInr`: `projSimR`, `projSimR'`, `pair_restrict_inr` |
| Component edges and three-part graph | `CompGraph.Defs`: `compGraph`, `valid_wrap_iff`, `valid_flatten_iff`, `fullGraph₂`, `fullGraph₂_pathModelExpansive` |
| Current facade and translation API | `Silmaril.Wasm.InstObs.Defs`, `Api.Defs`: `Institution.ofObs`, `Comorphism.ofObs`, `Morphism.ofObs`, `ExpTranslation`, `id_sen_φ`, `ofProg`, `ofSemEquiv`, `ObsGraph.toSpec`; the identity translation expands equations, rather than being syntactic identity |
| Graph API and borrowing | `Api.Graphs.Defs`: `AllExpansive.sum`, `AllExpansive.extend`, `Graph.obsGraph`, `graph_eq`, `GameGraph.obsGraph`, `gameGraph_eq`, `fullGraph_entails_path_iff`; `Api.Thms`: worked transfer examples |
| Game readings and facade laws | `Silmaril.Games.InstFacade.Defs`: `GInst.Reading`, `Reading.coHom`, `Reading.modelExpansive`, `Reading.precomp_coHom`; `GameReadings.Defs` and `GameReadings.Thms`: `modOf_surjective`, `coHom_modelExpansive`, `coHom_entails_iff` |
| Component-to-game-institution cross edge | `CompGameGraph.Defs`: `spec` (11 comorphisms, 8 morphisms), `cross_modelExpansive`, `compCoHom_eq_path`, `moduleCoHom_eq_path`, `programCoHom_eq_path`, `pathModelExpansive` |
| Separate divergence-aware entry translation | `DivGames.Edges.Defs`: `instEntryAll`, `entryObj`, `entryToRed`; `DivGames.Spec.Defs`: `divSpec`, `redGame_modelExpansive'`, `valid_redToGame_iff'` |
| Institution facade | `Silmaril.Logic.Inst.Core.Defs` and `Silmaril.Logic.Inst.Graph.Defs`: universe aliases and dot-notation aliases |

## Files

| Module | Content |
| --- | --- |
| `Silmaril.Wasm.Institution.Generic.Defs` | generic construction `ObsSemantics ⇒ Inst`; translations ⇒ comorphisms and morphisms |
| `Silmaril.Wasm.Institution.Session.{Defs,Thms}` | session logics (`ExportRefines`, `ExportEquiv`) |
| `Silmaril.Wasm.Institution.Entry.{Defs,Thms}` | single-invocation logics (`Equiv.ModuleRefines`, `ModuleEquiv`) |
| `Silmaril.Wasm.Institution.Graph.Defs` | the 12-node Hets logic graph |
| `Silmaril.Wasm.Institution.Hooks.Defs` | graph extension by one logic, sum of graphs; phase-2 `Hook` |
| `Silmaril.Wasm.Institution.Games.{Defs,Thms}` | game, reduction and LTS logics; grounded Wasm reduction |
| `Silmaril.Wasm.Institution.GameGraph.Defs` | reduction/game graph; `fullGraph` |
| `Silmaril.Proofs.Wasm.Institution.Games.{Basic,Wasm}` | proofs |
| `Silmaril.Proofs.Wasm.Institution.{Session,Entry}.Basic` | proofs |
| `Silmaril.Wasm.Institution.Components.{Defs,Thms}` | module, component, flat, program and component-game logics; `wrap` |
| `Silmaril.Wasm.Institution.CompGraph.Defs` | module/component/game graph; `fullGraph₂` (the complete graph) |
| `Silmaril.Proofs.Wasm.Institution.Components.Basic` | proofs |

## The three-part graph

`CompGraph.fullGraph₂ C P host Env = sum(sum(phase 1, phase 2A), phase 2B)`, with no cross edges
between the three parts. Every path in it is model-expansive (`fullGraph₂_pathModelExpansive`),
so heterogeneous borrowing (`LogicGraph.entails_lift_path_iff`) applies to every path. The three
parts are:

| Part | Interfaces | Nodes | Comorphisms (all model-expansive) | Morphisms (sound) |
| --- | --- | --- | --- | --- |
| phase 1 | `Set String` (export names) | {session, entry} × {core, bir} × {equiv, refEq, refTrapsUB} | `lower`, `lift`, `equivRef`, `close` | `Proj.trapsUB`, `Proj.equiv` |
| phase 2A | `exportIfaces` (`Set String` → `exportSig`) | red, lts, game (programs: instantiated Wasm modules via `wasmRed`) | red→lts, lts→game, red→game | game→red, game→lts, lts→red |
| phase 2B | `compIfaces` (`Set ℕ` → subsets of `sigU`) | module, comp, linked, program, game | linked→comp, comp→program, {module,comp,linked,program}→game, `flatten` (comp→linked), `wrap` (module→comp) | game→each, comp→linked, program→comp, linked→comp, comp→module |

Every satisfaction condition is an instance of `Translation.sat_sen_iff`. In each case it means:
the translated program's denotation, observed back through the semantic map, is the source
program's denotation (`sem_den`), and refinement atoms keep their meaning (`atom_holds`).

## The generic construction

An `ObsSemantics Iface` gives interfaces `X` (a category), semantic objects `Sem X` with a strictly
functorial reduct `restrict : (X ⟶ Y) → Sem Y → Sem X`, programs with denotations
`den X : Prog → Sem X`, unary operators `op`, and a refinement relation `Le X` at each interface.
Its institution `S.inst : Inst.{1,0,0,0,0}` has:

* **signatures** `(V, X)`: program variables and an interface; morphisms rename variables and
  map interfaces;
* **models** at `(V, X)`: assignments `V → Sem X`. These are *semantic interpretations*, not
  programs: a variable may denote any semantic object, so a theory specifies unknown components
  loosely. Concrete programs are constants with fixed denotations. Model morphisms are
  equalities. The reduct renames variables and restricts values (for Wasm: hides exports);
* **sentences** `(τ : Z ⟶ X, φ)`: a formula `φ` built from `t ⊑ u`, `t ≐ u` and `∧` over terms
  `x | ⟨p⟩ | o(t)`, observed through the scope `Z`. The scope is part of the sentence because
  refinement is not invariant under enlarging the interface: more exports distinguish more
  programs. Translation composes the scope and renames variables;
* **satisfaction**: `β ⊨ (τ, φ)` iff `φ` holds at `Z` with each variable denoting the
  `τ`-reduct of its value and `⊑` read as `Le Z`.

The satisfaction condition (`ObsSemantics.sat_map_iff`) follows from functoriality of `restrict`
alone. `valid_leSen_iff` shows that validity of the closed sentence `p ⊑ q` at `X` is
`Le X (den X p) (den X q)`.

A `Translation F A B` over an interface functor `F` maps `B`-objects to `A`-objects naturally,
maps programs and operators forwards, and maps each `A`-atom `t ⊑ u` to a `B`-formula with the
same meaning (`atom_holds`). It yields:

* a comorphism `coHom : A.inst → B.inst` whose satisfaction condition is `sat_sen_iff`;
* model-expansiveness when every semantic map is surjective, and so borrowing (`entails_iff`,
  `valid_iff`);
* for `F = 𝟭`, an institution morphism `toHom : B.inst → A.inst` built from the same corridors,
  which is sound under the same surjectivity hypothesis.

## Nodes

Every phase-1 node uses interfaces `Set String` (export or entry names) under inclusion.

| Family | Semantic object of `X` | `Le` (refinement / equivalence) | Validity of `m ⊑ m'` at `univ` |
| --- | --- | --- | --- |
| session | instantiability and `moduleObs` per environment, for scripts over `X` | `Refines R` / `Equiv R` | `ExportRefines R P host m m'` / `ExportEquiv R P host m m'` |
| entry | `Ok` and `beh` per entry in `X` | `Refines R` / `Equiv R` | `Equiv.ModuleRefines E R` / `ModuleEquiv E R` |

Each family has two languages: Core modules (`den`) and Binaryen IR modules, which denote their
lowering. Each language has three notions: `equiv` (`Equiv Eq`), `refEq` (`Refines Eq`) and
`refTrapsUB` (`Refines TrapsUB`). Together these give 12 nodes. For the session family, the
equation `m ≐ m'` of `refEq` is also exactly `ExportEquiv Eq` (`valid_coreRef_eqSen_iff`). Other
relations `R` (for example `ExportEquiv TrapsUB`) are available as `coreRef/coreEquiv P host R`,
but they are not graph nodes.

The operators are closures `close R`. Session closure is closure under `SessionRel R`; entry
closure is closure under `R`. The central lemma is `refines_close_iff`:
`a ⊑_R b ↔ a ⊑_Eq close R b`. For `TrapsUB`, this says that traps-never-happen refinement is
plain refinement against the specification with every trap replaced by arbitrary behaviour. The
session proof relies on the fact that `SessionRel Eq` is equality (`sessionRel_eq_iff`).

## Edges

All comorphisms below use the identity signature functor and identity model maps. All are
therefore model-expansive.

| Edge | Direction | Sentence map | Satisfaction condition means |
| --- | --- | --- | --- |
| `lower f n` | bir → core | `⟨m⟩ ↦ ⟨m.lower⟩` | an IR module means its lowering (definitional) |
| `lift f n` | core → bir | `⟨m⟩ ↦ ⟨lift m⟩` | `lower_lift` |
| `equivRef f l` | equiv → refEq | `t ≈ u ↦ t ≐ u` | `Equiv Eq ↔` two-sided `Refines Eq` |
| `close f l` | refTrapsUB → refEq | `t ⊑ u ↦ t ⊑ close TrapsUB u` | `refines_close_iff` |

Morphism (projection) edges `Proj` read the `close` and `equivRef` corridors as institution
morphisms `refEq → refTrapsUB` and `refEq → equiv`. The sentence component goes in the opposite
direction: `close` translates a traps-UB atom to refinement against a closed specification, and
`equivRef` translates an equivalence atom to two refinements. Soundness does not turn a
one-sided `Eq` refinement into equivalence of the same two programs.

**Why coarsening is not an identity comorphism.** A comorphism `refEq → refTrapsUB` that is the
identity on sentences would need `Refines Eq ↔ Refines TrapsUB` on all models, which is false.
The inclusion `ExportRefines Eq ⊆ ExportRefines TrapsUB` appears in the logic in two places:
the entailment `{t ⊑ u} ⊨ t ⊑ close R u` in `refEq` for reflexive `R` (`entails_close`), and the
comorphism/morphism pair above. `exportRefines_of_eq` re-derives `ExportRefines.trapsUB_of_eq`
from them.

**Core as a retract of Binaryen IR.** `liftT ≫ lowerT` preserves satisfaction exactly
(`sat_lowerT_liftT_iff`). It is not the identity on sentences, because the generic formula
translation expands `≐` into a conjunction of two refinements.

## Passes

`passEquivValid R hR : Pass (refinesContract R P host hR) ≃ {f // f preserves BModule.Ok ∧ ∀ m,
m.Ok → ⊨ f m ⊑ m in birRef P host R}`. In words, a verified pass is a uniformly valid family of
refinement sentences. `passEquivValidEquiv` gives the same statement for `equivContract` and
`birEquiv Eq`, and `soundPass_iff_valid` gives it for `SoundPass`.

## Graph consequences

* `graph P host Env : LogicGraph.{0,0,1,0,0,0,0}`;
* `pathModelExpansive`: every path is model-expansive;
* `entails_path_iff`: in the Grothendieck institution, entailment is borrowed along any path;
* `valid_bir_trapsUB_iff_core_eq`: validity in the Binaryen IR `TrapsUB` logic is validity, along
  `lower` and then `close`, in the Core `Eq`-refinement logic.

## Phase-2 hooks

`LogicGraph.extend` adds one logic with comorphism edges into it, and `LogicGraph.sum` joins two
graphs with cross comorphisms from the first into the second. `Graph.Hook` packages a new
`ObsSemantics J`, an interface functor `embed : Set String ⥤ J` and translations from chosen
phase-1 nodes. `Hook.pathModelExpansive` keeps borrowing available whenever the hook's semantic
maps are surjective.

* **Games, cross edge from the session logic**: `prog m` maps to the strategy of `m`, and `sem`
  gives the session object observed from a strategy. Here `sem_den` is adequacy. This edge is
  missing; see Phase 2A for why.

Components are covered in Phase 2B, inside their own subgraph. Hooking them to the phase-1
nodes is open (see Phase 2B, gaps).

## Phase 2A: reduction semantics versus game semantics

**Interfaces.** Game signatures `Silmaril.Games.Sig.{0}` live in `Type 1`, while the graph lives
at `Inst.{1,0,0,0,0}`. Interfaces are therefore a small category indexing game signatures
(`GameIfaces`: `sig`, functorial `hom` into `Sig.Hom`, and a top interface). The reduct is
`Strategy.restrict` along `hom f`, which hides operations. For Wasm, `exportIfaces` takes
interfaces `X : Set String`; `sig X` has one operation per invocation `(x, vs)` with `x ∈ X`,
answered by a `Behaviour Val`. For the same reason, reductions and LTSs (also in `Type 1`) enter
through a small type of programs `RProg` with `red : RProg → Reduction E (sig top)`: a language
given by its syntax and its reduction semantics.

**Logics** (all with strategies as semantic objects, `⊑` = strategy refinement, operators
`τ : Strategy E E` plugged below):

| Node | Programs | `p` denotes | Validity of `p ⊑ q` at top |
| --- | --- | --- | --- |
| `game` (`gameSem`) | strategies | itself | `σ ≤ τ` |
| `red` (`redSem`) | `RProg` | `ofReduction (red p)` | every legal trace of `red p` is a play of `ofReduction (red q)` (`valid_red_top_iff_traces`) |
| `lts` (`ltsSem`) | `RProg` | `ofLTS (red p).toLTS` | same, for traces of the LTS |

**Edges** (`GameGraph.gameGraph`): comorphisms `red → lts`, `lts → game` and `red → game`
(`p ↦ ofReduction (red p)`), all model-expansive. Each satisfaction condition is the adequacy
equation `sem_den`: the strategy assigned to the translated program equals the denotation of the
source program. `Silmaril.Games` *defines* `ofReduction` by traces, so this equation holds by
`rfl`. Adequacy has real content as the trace characterization (`Strategy.ofLTS_le_iff`), and
for Wasm as `mem_wasmRed_iff` below. The duals (`Translation.toHom`) are sound institution
morphisms `game → red`, `game → lts` and `lts → red`: projections of the game logic onto the
operational ones.

**Simulation, borrowed.** `valid_of_simulation`: a `Reduction.Simulation (red p) (red q)` makes
`p ⊑ q` valid at every interface of the reduction logic. `valid_game_of_simulation` then shows,
by `Translation.valid_iff` along `redToGame`, that the translated sentence is valid in the game
logic. `valid_game_of_ltsSimulation` does the same for LTSs.

**Grounded in Wasm Core** (`wasmRed P host w`, for an instantiated module `w = (store, module
instance)`):
- *Grounded*: configurations, `Execution.Core.Step P host`, `Binaryen.exportFunc?`, `invoke`
  and results are the library's Core definitions.
- *Not grounded*: host calls are not game moves. The lower signature is `Sig.empty`, and host
  functions run inside `Step` via `host`.
- Each question starts from the same store (single-invocation shape).
- `mem_wasmRed_iff`: for non-divergent `b`, the two-move play "invoke `x` on `vs`, answer `b`" is
  in the strategy iff `b ∈ behaviours P host s a vs` for the export's address `a`.
- `finite_beh_of_le`: game refinement of instantiated modules implies inclusion of their finite
  single-invocation behaviours.
- The converse is stated as a proposition, not proved:

```lean
def Task.wasmRed_le_of_finite_beh : Prop :=
  ∀ w w' : Inst H, (∀ x vs (b : Behaviour Val), b ≠ .diverges →
      b ∈ (instEntry P host).beh w x vs → b ∈ (instEntry P host).beh w' x vs) →
    Silmaril.Games.Strategy.ofReduction (wasmRed P host w) ≤
      Silmaril.Games.Strategy.ofReduction (wasmRed P host w')
```

**The full graph.** `GameGraph.fullGraph P host Env = LogicGraph.sum (Graph.graph P host Env)
(gameGraph exportIfaces Sig.empty (wasmRed P host)) (no cross edges)`. Every path is
model-expansive (`fullGraph_pathModelExpansive`).

**Missing cross edges in `GameGraph.fullGraph` (module logics → ordinary games).**
The following limits concern this graph and its ordinary strategies. The later
`DivGames.entryToRed` uses instantiated modules with `Ok := True`, divergence-observing
strategies and a changed refinement atom; it does not supply either missing edge below.

* *Session logic → games.* A comorphism needs a map from strategies back to session objects, and
  adequacy. Concretely this is a `Graph.Hook` translation from `⟨session, core, n⟩` with:
  - (i) for each module `m`, a strategy whose plays over scripts are `m`'s session observations.
    Because the store persists across questions, this needs an `LTS`, not a `Reduction`.
  - (ii) `sem_den`, i.e. `sem X (res (toTop X) (strat m)) = Session.den P host X m`.

  Two obstacles stand in the way:
  - Session objects carry instantiability (`inst`, the first clause of `ExportRefines`) and the
    instantiation run's outcome, which strategies do not record.
  - Strategies do not observe divergence, which sessions do.

  So with `atom := ⊑`, `atom_holds` fails unless the game side is enriched (an initial
  instantiation move, a divergence observation). The provable shape is an implication, as for
  `finite_beh_of_le`.
* *Entry logic → games.* `moduleEntryPoints` takes a union over instantiations allowed by
  `Env`, whereas `wasmRed` works per instantiated module. A union over `Ready` instantiations of
  `finite_beh_of_le` gives an implication for the finite part of `Equiv.ModuleRefines`. It is not
  a comorphism, for two reasons: entry objects have the `Ok` premise, and games again do not
  observe divergence.

## Phase 2B: modules versus components

**Interfaces.** Components are denoted over the universal signature `sigU` (function index ×
payload). `compIfaces` takes interfaces `X : Set ℕ` (export indices); `compSig X` keeps the
operations of `sigU` with index in `X`, so the reduct hides exports. The lower signature is
`sigU` (the imports). `top σ := σ.restrict ιU` views a `sigU` strategy at the full interface.
`ιU` has inverse `ιU'`, so `top_le_iff` holds: validity at top is exactly refinement over
`sigU`.

**Nodes** (all `GameIfaces.stratSem compIfaces sigU`, for any `C : CoreSem M`). Models assign
strategies to program variables; `⊑` is strategy refinement; operators are environments
`τ : Strategy sigU sigU` linked below.

| Node | Programs | Denotation |
| --- | --- | --- |
| `module` | `m : M` | `modU C m`: `C.sem m` between `narrowH` and `widenH` |
| `comp` | `Comp M` | `Comp.denU C` |
| `linked` | `Linked M` | `Linked.denU C` |
| `program` | `Program M` | `Program.denU C` |
| `game` | strategies | itself |

**Edges and what each satisfaction condition means.**
* `linkedComp`: the flat IR is a sub-IR of the nested one (`Linked.denU_toComponent`).
* `compProgram`: a component is a program observing all its exports (`rfl`).
* `…Game`: "components → games" is the denotation itself (`rfl`).
* `flatten`: flattening preserves meaning (`denU_flatten pairLaws`).
* `wrap`: wrapping preserves meaning, `WrapAdequate C : ∀ m, (wrap m).denU C = modU C m`. This
  is **proved** for every `C` (`wrap_denU`, `wrapAdequate`). The proof goes in three steps:
  - the export handler only calls the new instance (`splitH_comp_implsH_append`);
  - `pair_comp_sumMap` and the right projection `PairInr.pair_restrict_inr` then isolate the
    instance;
  - finally the masks collapse: `maskH_comp_implsN_fwd`, giving `narrowH`, and
    `widenH_comp_maskH`.

  The statement holds with the definitions as given.
  - `wrap m` is the core-level trivial wrapper: one core instance, imports forwarded
    (`Impl.fwd`), exports forwarded.
  - It has no canonical-ABI `lift`/`lower` adapters, and its interface types are placeholders
    `⟨[], []⟩` (the semantics only uses lengths).
  - `valid_wrap_iff` is the borrowing statement: module refinement holds iff wrapper
    refinement holds. `valid_flatten_iff` is the borrowing statement for flattening.
* The dual morphisms project the game logic onto each IR logic.

**What is grounded.** Core modules are an abstract type `M` with `CoreModule M`, and their
semantics is an arbitrary `C : CoreSem M`. `Components.CoreSem.ofReduction` builds `C` from
per-module reduction semantics, through `Strategy.ofReduction`. Nothing in phase 2B is tied to
the library's Wasm Core semantics.

**Passes.**
* `passEquivValid C : Pass (contract C) ≃` size-preserving `f` with every `f c ⊑ c` valid in
  `compSem C`. `programPassEquivValid C` does the same for `(programIR C).contract`.
* `valid_fuse`: adapter fusion gives valid `fuseComponent c ≐ c` at every interface
  (unconditional).
* `valid_deadExports`: dead-export elimination gives valid `deadExports p ≐ p` (unconditional).
* `valid_flatten pairLaws`: flattening gives valid equations.
* `valid_game_fuse`: the fusion equation, borrowed into the component game logic.

**Gaps (phase 2B).**
* There are no cross edges between phase 2B and phases 1/2A, for three reasons:
  - there is no `CoreModule` instance for the library's `Module`/`BModule`;
  - there is no `CoreSem` built from the library's Core semantics (for example from a
    `wasmRed`-like reduction over `sigN` payloads);
  - the component signatures (`sigU`, payloads, `Option Payload` answers) and the export
    signatures of part A (`exportSig`, `Behaviour Val` answers) are related by no interface
    functor.
* The wrapper is core-level only: the ABI-adapter (lift/lower) wrapper is not covered.
* Size equalities of the component contracts are not sentences. They appear as side conditions
  in `passEquivValid`.

## Not covered

* There is no translation between the session and entry families, which would need a semantic
  theorem relating `moduleObs` sessions to `moduleEntryPoints` invocations.
* Interfaces have inclusions only. Renaming exports would need a syntactic export-renaming
  operation on modules together with a semantic lemma; neither is supplied here.
* Function-level `FunRefines` (two addresses in one store) is not a node. Store-level entry
  points (`Execution.Core.entryPoints`) fit the entry construction, but they are not
  instantiated here.
* The pass correspondence covers the Binaryen IR contracts, not `coreIR` contracts.

## Current institution API

`Silmaril.Inst` (module `Silmaril.Logic.Inst`, see [logic-inst.md](logic-inst.md)) supplies the
shared institution types, canonical satisfaction notation (`open scoped Silmaril.Inst`),
comorphism composition and the typed `GraphSpec` builder. `Institution.ofObs`,
`Comorphism.ofObs` and `Morphism.ofObs` expose observational semantics through that facade.
`ExpTranslation` bundles a translation with surjective semantic maps, so its `.comorphism`
supports borrowing without a separate surjectivity argument. Its `.morphism` is available over
the identity interface functor.

`Graph.obsGraph` and `GameGraph.obsGraph` recover the phase-1 and reduction/game graphs.
`ObsGraph.toSpec` presents selected edge lists as a facade `GraphSpec`.
`LogicGraph.AllExpansive` supplies borrowing along every path from edge-level
model-expansiveness. `DivGames.divSpec` is deliberately a `GraphSpec`, rather than an
`ObsGraph`: its `entry → red` map always returns `Ok := True`, so it cannot reach arbitrary
entry objects; only its `red → game` edge has model-expansive borrowing.

The game-reading builder `GInst.Reading` reads strategies as models naturally in signatures.
`GameInst.coHom` and `SpecGInst.specCoHom` use that builder. For `GameInst.coHom G E`,
`modOf_surjective` proves model-expansiveness. `CompGameGraph.graph C` joins the component
graph to `GInstRef → GInst → DGInst` with a model-expansive cross edge into `GInst`;
`GameInstMaps.{compCoHom,moduleCoHom,programCoHom}` are composites along those edges, and every
path is model-expansive.

## Function-level institutions

Institutions for reasoning about functions and code segments *within* a module (holes, typed
contexts, partial models of the other functions, peephole transfer, wasm-merge as
amalgamation), function-body variants over fragment, lambda-SSA and Binaryen IR bodies, and
their link to the entry logic `Entry.entryEquiv` are in
[wasm-fn-institutions.md](wasm-fn-institutions.md).
