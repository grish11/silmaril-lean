# Function-level institutions for Wasm

Institutions for reasoning about Wasm functions and code segments *within* a module: what a
body (or a segment of a body) means relative to the module context it can see and to what is
known about the other functions. They are built with the institution facade `Silmaril.Inst`
(`Plain`, `Comorphism.ofPlain`; see [logic-inst.md](logic-inst.md)) and sit next to the
module-level logics of [wasm-institutions.md](wasm-institutions.md). Code is under
`Silmaril.Wasm.FnInst`; longer proofs are under `Silmaril.Proofs.Wasm.FnInst`.

There are four tracks (core, models, ir, opt) and a grounding layer (`Ground`). The four tracks
are independent constructions: they do not import each other, and no comorphism relates them
yet (see "Known limitations").

An **institution** packages signatures (the names and types code can see), sentences (claims
about code), models (semantic choices) and satisfaction (when a claim is true). A **reduct**
forgets information along a signature map. A **comorphism** translates sentences forward and
models backward while preserving and reflecting satisfaction. **Model-expansive** means every
source model has an expansion; this lets validity be borrowed both ways. A **peephole**
replaces a small code segment; a **hole** records the inputs and context that segment needs.
These constructions are generic: each concrete fragment below has its own stated adequacy
boundary.

## Design summary

**Signatures with a focus.** A signature is a module context (the types of the functions and
other index spaces a body can see) together with a *focus*: what the sentences talk about.
There are four focus variants:

- **one** function index (core `OneSig`/`oneInst`; models `Sig` with one focus function);
- **several**: a set of function indices (core `SetSig`/`setInst`);
- **all** functions of the context (core `allInst`);
- an **abstract hole**: a segment type (params, results, locals, labels) in a context (core
  `HoleSig`/`holeInst`; opt `HSig`/`segInst`, where morphisms are typed contexts `pre`/`post`
  around the hole; ir `Hole` with a pluggable signature `Frame`).

In the core and models tracks, morphisms embed contexts while respecting the focus. In opt they
are typed surrounding code plus a prefix extension of function types; in ir they come from the
chosen signature frame. The core comorphisms one → several → all and hole → all relate the
variants.

**Partial environments as models.** A model says what is known about the functions the focus
can call. Three forms appear and are related:

- (c) *environments / handlers*: abstract answers to every event (core handlers; models
  `semInst`, sets of environments; opt `Env`, environments unspecified outside the visible
  functions, with `div` as an explicit answer);
- (a) *partial bodies*: each other function free, base or given by code, whose meaning is the
  set of its completions (core `PModel`; models `PMod`/`bodyInst`);
- (b) *bodies plus a choice of semantics* (models `kInst`).

Less information means more completions. Validity over partial models equals validity over
handlers/environments, and positive satisfaction is **monotone in information**: what is true
with less information stays true with more (core `HPres.partial_sat_mono`, models `sat_mono`,
opt `holds_mono` for `Form.Positive`, ir `sat_mono`, trivially, since its languages are
call-free).

**Sentences.** Conjunctions of:

- **equivalence** `b ≐ b'` of segments or bodies (same outcomes in every completion; all
  tracks, each with its own semantics);
- **refinement** `b ⊑ b'` (ir, opt);
- **distinction** in some completion (anti-monotone in information: core `distSome_anti`,
  models `distinctSome_anti`, opt `holds_distSome_anti`) and in every completion (monotone;
  opt, and as a predicate in core).

Because a context can hide a difference, plugging into a context is *not* a signature morphism
(core `Frag.plug_no_reduct`), and the opt track keeps the scope in the sentence. The
**peephole theorem** appears in each track: a rewrite valid at the minimal signature (empty
context, least informative model) transfers under the track's hypotheses. Core's arbitrary
plugging needs a **free** segment type (every configuration fits); its typed
`addZero_everywhere` is transfer to a hole of the same type, without a typed-context congruence
theorem. Opt's module theorem needs typed, total import environments and typed rewrite
positions. The results are core `peephole_empty`, models `transfer`, opt
`sat_plug_equiv`/`peephole_module`, and ir `valid_in_every_module`.

| Connection | Track |
| --- | --- |
| focus comorphisms one → several → all, hole → all, model-expansive for handlers (borrowing) | core |
| handler and partial-model versions of each focus institution | core |
| comorphisms environments (c) → partial bodies (a), and bodies + semantics (b) → (a); model readback reverses these arrows | models |
| versions in the signature: conservative `vInst`, context-restricting `AdmValid` (only downward) | models |
| link to the module-level entry logic (`Entry.entryEquiv`, `Equiv.ModuleEquiv`) | models |
| body languages fragment, native fragment, lambda-SSA, decompilable SSA, Binaryen IR, linked by the exact translations of `Silmaril.Wasm.SSA` as comorphisms in a 5-node logic graph; Binaryen-body equations to Core 3.0 behaviours | ir |
| segment institution with typed contexts as morphisms; wasm-merge as amalgamation | opt |

## Track core

**Languages.** `Lang` (`Silmaril.Wasm.FnInst.Core.Defs`) abstracts a body language over module
contexts: code `Code C` with renaming along embeddings, events `Ev C` with renaming, and an
execution `exec h c cfg w : Out W` of code from a configuration `cfg` (operand stack, locals)
in a world `w`, where `h : Ev C → W → Resp × W` answers events. The world type `W` is a
parameter of every institution. The single semantic law is naturality,
`exec h (rename σ c) = exec (h ∘ evMap σ) c`. `Silmaril.Wasm.FnInst.Frag` is an `i32` fragment
with constants, arithmetic, locals, globals, memories, calls, `block`, `br`, `br_if` and `if`,
proved to be a `Lang` by induction on code. Its simplifications (no validation, underflow
traps, no block arities, no loops) are listed in its module doc. In this instance `Fits` checks
operand and local **lengths**, not full Wasm validation or the result/label fields of `SegTy`.

**Why handlers.** A body only acts on its module through events, so the meaning of a body over
a context is a function of the handler. Embedding a context into a bigger one renames events
injectively, and running renamed code under a bigger handler is running the original code
under the reduct handler. That is the satisfaction condition, per model, with no assumption
about the hidden part of the bigger module (the world type absorbs hidden state). Validity over
all handlers is truth with the least information about every other function.

| Institution | Signature | Morphisms | Atoms |
| --- | --- | --- | --- |
| `holeInst L W` | `HoleSig`: a context and a segment type `τ` | embeddings keeping `τ` | `(b, b')`: `SegEq h τ b b'` |
| `oneInst L W` | `OneSig`: a context and one function index | embeddings mapping the index | `seg τ b b'`, `fn () b b'` |
| `setInst L W` | `SetSig`: a context and a set of function indices | embeddings mapping the set into the set | `seg`, `fn i` for members |
| `allInst L W` | a context | embeddings | `seg`, `fn i` for every index |

`SegEq h τ b b'`: same outcome from every configuration that fits `τ`. `FnEq h t b b'`: same
call result from every argument list fitting the function type `t`. Each variant is an `HPres`
(presentation by handlers), turned into a `Plain` institution by `HPres.toPlain`; the partial
versions come from `HPres.partialPlain`, where `M ⊨ φ` means every completion of `M`
satisfies `φ`.

**Partial models.** `PModel L W C` (`Silmaril.Wasm.FnInst.Partial.Defs`): an embedding of `C`
into a module context `C'`, a base handler, and for each function of `C'` `free`, `base` or
`code b`. Its completions are the handlers on `C'` that agree with the base off free and
specified functions and answer calls of specified functions by running their bodies, reduced to
`C`. Completions commute with reducts (`PModel.den_reduct`). A model may have no completion
(recursion makes the body equations a fixpoint condition), and then it satisfies everything
(`HPres.not_sat_of_distAll` needs a completion). `InfoLe M N` is inclusion of completions.

**Results.**

| Statement | Content |
| --- | --- |
| `HPres.toPlain`, `HPres.partialPlain` | satisfaction condition of every handler and partial-model institution |
| `segEq_rename`, `fnEq_rename`, `FnAtom.holds_rename` | atom-level satisfaction condition from `exec_rename` |
| `oneToSet`, `setToAll`, `holeToAll`, `oneToAll` | comorphisms between the focus variants |
| `oneToSet_modelExpansive`, `setToAll_modelExpansive`, `holeToAll_modelExpansive`, `oneToAll_modelExpansive`, `oneToAll_valid_iff`, `holeToAll_valid_iff` | model expansion and borrowing |
| `oneToSetP`, `setToAllP`, `holeToAllP` | the same comorphisms between the partial-model institutions |
| `hole_valid_transfer` | a hole rewrite valid at `(C₀, τ)` holds at every hole of type `τ` of every larger context |
| `peephole`, `peephole_seg`, `peephole_fn`, `peephole_all`, `peephole_empty` | **peephole theorem**: free-typed rewrite valid at the minimal signature ⇒ equivalence inside any context of any function of any module, in every model |
| `congr_entails` | congruence as entailment in `allInst`: `{seg τ b b'} ⊨ fn i K[b] K[b']` for free `τ` |
| `Frag.Hole.congr`, `Frag.fragPlug` | congruence of plugging for the fragment |
| `Frag.plug_not_reflect`, `Frag.plug_no_reduct` | **refuted**: plugging reflects equivalence; no model reduct makes plugging a signature morphism |
| `Frag.constFold_valid`, `constDrop_valid`, `getSet_valid`, `constFold_everywhere` | rules at the minimal signature and their transfer into every function |
| `Frag.addZero_valid`, `addZero_not_free`, `addZero_everywhere` | a typed rule: valid at type `[i32] → [i32]`, refuted at the free type, valid at every hole of its type |
| `HPres.partial_sat_mono` | **monotonicity**: true with less information ⇒ true with more |
| `HPres.distAll_mono`, `HPres.distSome_anti`, `partial_sat_iff_not_distSome` | how distinction behaves |
| `Frag.distSome_not_mono` | **refuted**: distinction in some completion is monotone |
| `PModel.den_exact`, `HPres.sat_exact_iff`, `HPres.valid_partial_iff` | a handler is a partial model with one completion; partial validity is handler validity |

## Track models

Code under `Silmaril.Wasm.FnInst.Models`.

**Design.** `FnSyntax`: function types, bodies `Body n` over `n` callable functions, renaming of
call indices. `FnSem L`: a domain of function behaviours and `eval env b`, the behaviour of
body `b` when the callable functions behave as `env`; the one law `eval_rename` says that a
body sees its context only through calls. `Ctx L` gives the types of all functions of a module;
`Ctx.Hom` is an injective, type-keeping renumbering. `Sig L` is a context and a focus function.
Sentences `Sen L n` are `b ≐ b'` between candidate bodies of the focus, and conjunction.

| Variant | `Mod T` | Institution |
| --- | --- | --- |
| (c) semantic | `Set (Env S T.n)`: possible behaviours of all functions | `semInst` |
| (a) partial bodies | `PMod T`: a bigger context, an embedding of `T` into it, partial bodies | `bodyInst` |
| (b) bodies + semantics | `KMod sems T`: `k : K` and a `PMod T`, read in `sems k` | `kInst` |

The denotation of a partial module is the set of restrictions of the **solutions** `Sol`:
environments in which every function with a known body, other than the focus, behaves as its
body. Unknown bodies are unconstrained. Recursion is handled by taking all solutions of the
body equations, not the least one. Reducts are strictly functorial and `den` commutes with them
(`PMod.den_reduct`). `PMod.Le` is the information order; more information means fewer
environments (`den_anti`).

**Versions.** `Versioned L V` says which bodies a version allows. `vInst` over `VSig` is
conservative along `v ≤ w` (`valid_up_iff`). The context-restricting reading `AdmValid`
quantifies only over behaviours admissible at `v`; it is not an institution along version
inclusions, and validity only transfers downwards (`admValid_anti`).

**Fragment.** `Models.Frag`: `i32` values, one `i32` global, unary functions; `const`, `param`,
`add`, `ext8`, `gget`, `gset` (needs `mutGlobal`), `call`, `seq`, `trap`. A behaviour maps
arguments and state to a set of results. Capabilities follow `Silmaril.Wasm.Models.Cap`, so the
fragment is versioned by the `FeatureSet` lattice.

**Results.**

| Statement | Content |
| --- | --- |
| `semToBody`, `kToBody`; `valid_body_iff`, `valid_sem_iff`, `valid_k_iff` | comorphisms between the variants; validity agrees |
| `PMod.den_anti`, `sat_mono`; `PMod.bot`, `bot_le`, `den_bot` | monotonicity in information; the least informative model |
| `transfer`, `transfer_valid` | a sentence satisfied by the least informative model of the minimal signature holds, translated, in every model of every signature it embeds into |
| `distinctSome_anti` | some-completion distinction is anti-monotone |
| `sol_update_eq`, `sol_replace_of_sat` | replacing a body by one with the same behaviour in every solution keeps the solutions |
| `moduleEquiv_replace`, `entry_valid_replace` | replacement gives `Equiv.ModuleEquiv` for every reflexive behaviour relation at the entry points `entryPoints S obs` of closed modules, for an arbitrary observation function; and validity of `m ⊑ m'` in `Entry.entryEquiv` at every interface |
| `forget`, `valid_up_iff`, `valid_forget_iff` | versions in the signature are a conservative extension |
| `admValid_anti`; `Frag.not_admValid_up` | context-restricting validity transfers down; **refuted** upwards (two bodies equivalent when no callee can write the global, distinguished at Wasm 1.0) |
| `Frag.add_zero_left`, `Frag.addZeroRule_transfer`, `Frag.addZeroRule_moduleEquiv` | `0 + e ≐ e`, its transfer, and module equivalence of the rewrite |
| `Frag.admValid_vg`, `Frag.not_admValid_v10`, `Frag.not_valid_read` | the version counterexample in detail |
| `FragK.addZeroRule_valid_k`, `FragK.dropDouble_not_valid_k` | with a choice of semantics: a rule valid for wrapping and checked `add`; a rewrite valid with wrapping `add` (`dropDouble_valid_wrap`) but not with checked `add` (`dropDouble_not_valid_checked`) |

## Track ir

Code under `Silmaril.Wasm.FnInst.IR`.

**Design.** `Lang.inst F L` is a function-body institution for any body language `L` and any
signature frame `F`, built with `Plain`. A frame is a category of signatures with a focus hole
type, preserved by morphisms, and contexts that reduce contravariantly. Models are a context
plus a runtime environment. Sentences are `≐`, `⊑` and `∧` over candidate bodies of the focus.
An exact translation `Lang.Tr` (bodies forwards, environments backwards, `den_body`) gives a
comorphism `Tr.comorphism`. It is model-expansive when the environment map is surjective
(`Tr.modelExpansive`), so it preserves and reflects equivalence and refinement (`Tr.equiv_iff`,
`Tr.le_iff`) and borrows validity (`Tr.valid_iff`). Composites give the composite comorphism
(`comorphism_comp_sen`, `comorphism_comp_mod`).

| Language | Bodies | Denotation |
| --- | --- | --- |
| `frag E` | `FragFunc` of the hole type | `FragFunc.Run` |
| `fragNative E` | the same with `FragFunc.native` | `FragFunc.Run` |
| `ssa E` | `SFunc` of the hole type | `SFunc.Run` |
| `ssaDec E` | `SFunc` on which `decompileFunc` succeeds | `SFunc.Run` |
| `bir H` | `BFunc` recognised at the hole with a native body | `Binaryen.Eval` in a store and module instance (`nativeOut`) |

| Translation | Body map | Exactness from |
| --- | --- | --- |
| `toSSA : frag → ssa` | `compileFunc` | `compileFunc_iff` |
| `ofSSA : ssaDec → frag` | `decompileFunc` | `decompileFunc_iff` |
| `ofBir : bir → fragNative` | `ofBFunc?` | `native_adequate` |
| `nativeIncl`, `decIncl` | inclusions | `rfl` |

**Results.**

- `graph H F`: the 5-node `GraphSpec`; every path is model-expansive
  (`graph_pathModelExpansive`).
- Equivalence is preserved and reflected where the translations are exact:
  `equiv_compile_iff`, `equiv_decompile_iff`, `equiv_bir_iff` (in any store and module
  instance), `lower_body`, `equiv_lower_iff`; round trips are equivalent to their source
  (`ssa_roundtrip_equiv`, `frag_roundtrip_equiv`, `bir_roundtrip_equiv`).
- Optimiser equations as valid sentences: `optimize_valid` (requires a successful `optimize?`
  result and a nonempty signature context), `optimizeSSA_valid` (with explicit parameter and
  result preservation) and `optimizeFuncNative_valid` (requires a successful
  `optimizeFuncNative?`). The Binaryen case is borrowed along `ofBir` then `nativeIncl` from the
  fragment equation `optimize?_equiv`.
- From a Binaryen-body equation to Core 3.0: `core_behaviours_of_equiv` and
  `core_behaviours_of_sat` cover two functions at the same address of two typed, native,
  arity-checked stores, with `BExpr.structuredList = true` for both bodies, whose bodies satisfy
  `b ≐ b'`. Both stores must admit the invocation (`InvokeOk`); the observation uses
  `closedHost`. Every such typed invocation then has the same Core 3.0 behaviours, at every
  profile, divergence included. This generalises `CoreCert.invoke_replace` from the optimiser's
  output to any equation of the institution.
- For these call-free languages satisfaction ignores the context (`sat_ctx_irrel`), so
  sentences are monotone in information both ways (`sat_mono`, `sat_info_mono` for `modFrame`).
  Validity at the minimal module signature transfers to every module with the same focus type
  (`valid_in_every_module`, an instance of `valid_transfer`).
- The lowering `toBFunc?` is partial: it fails on operators with `¬ op.valid t` and on indices
  of `2³²` or more, so there is no comorphism `fragNative → bir` with that body map. The
  theorems above state the exact correspondence where `toBFunc?` succeeds.

## Track opt

Code under `Silmaril.Wasm.FnInst.Opt.{Seg,Inst,Rules,Merge}`, proofs under
`Silmaril.Proofs.Wasm.FnInst.Opt.{Seg,Inst,Rules}`.

**Fragment** (`Opt.Seg.Defs`). `Val = BitVec 32`; instructions `const`, `add`, `sub`, `mul`,
`and`, `or`, `xor`, `eqz`, `localGet/Set/Tee`, `globalGet/Set`, `drop`, `call f`. Environments
`Env` map a function, arguments and globals to a set of answers (`ret`, `trap` or `div`);
`Env.top` is unspecified. `E.Completion ft M`: `E ≤ M`, `E` respects result counts (`Typed`) and
always answers (`Total`; `div` is an answer). `run ft E c st : Set Out`; `chk ft c h` computes
stack heights. `RunEq ft n E s s'` is equality of outcomes from every state with at least `n`
operands; `SegEquiv` is `RunEq` in every completion. Modules `Mdl` have `fsem M imp k`, the
environment of all functions at call depth `k`; `Mdl.Rewrites` rewrites bodies at typed
positions.

Divergence is an answer so that the empty answer set does not mean both "diverges" and "no
information". Sentences quantify over completions because satisfaction at the partial model
itself is not monotone: two codes that call an unspecified function have equal outcome sets
under `Env.top` and can differ under a narrower environment.

**Institution** (`Opt.Inst.Defs`). Signatures `X : HSig`. Morphisms `σ : X ⟶ Y` (`HSig.Hom`)
are typed contexts: `pre`, `post`, `j` values kept below the hole, and a prefix extension of
function types. `plug σ s = pre ++ s ++ post` is functorial. Models `Model Y` are environments
equal to `Env.top` past `Y.ft`; the reduct is `Env.restrict`. Sentences
`Sen Y = Σ X, (X ⟶ Y) × Form X` are scoped formulas (equivalence, refinement, distinction in
some completion, distinction in every completion, conjunction). The satisfaction condition is
functoriality of the reduct (`segPlain`); `segInst : Institution.{0,0,0,0,0}`. The scope is in
the sentence because plugging both sides preserves satisfaction in one direction only (`drop`
after a hole `0 → 1` makes `i32.const 0` and `i32.const 1` equal). That direction is the
peephole theorem.

**Results** (`Opt.Inst.Thms`, `Opt.Seg.Thms`).

| Theorem | Statement |
| --- | --- |
| `run_restrict`, `Env.restrict_completion` | code typed over `ft` does not see functions past `ft`; completions restrict to completions |
| `runEq_plug`, `runLe_plug` | per environment, equal (included) runs stay equal (included) in every typed context |
| `holds_plug_equiv`, `holds_plug_refine` | the same over a partial model |
| `distSome_of_plug`, `distEvery_of_plug` | a difference of plugged code is a difference of the segments; the every-completion case additionally requires `hX`, lifting every smaller-hole completion to the larger function types |
| `sat_plug_equiv`, `sat_plug_refine` | **peephole theorem**, institution form: `(τ, s ≈ s') ⊨ (𝟙, plug τ s ≈ plug τ s')` |
| `segEquiv_of_holds_top`, `peephole_module` | **peephole theorem**, module form (with `fsem_rewrite`, `den_rewrite`) |
| `holds_mono`, `holds_distSome_anti` | monotonicity of positive formulas; anti-monotonicity of some-completion distinction |
| `distSome_iff_not_equiv`, `distSome_of_distEvery` | how the distinctions relate (the second needs a completion; `Env.trapAll_completion` gives one for `Env.top`) |
| `holds_refine_of_equiv`, `holds_equiv_iff_refine` | equivalence is refinement both ways |

`peephole_module`: a pair equivalent at its minimal hole over the least informative model can be
exchanged at any typed positions of any bodies of any well-typed module whose function types
extend the hole's, with a typed, total import environment; every function keeps its semantics at
every call depth. This is equality of depth-indexed `fsem` (the module's own functions are a
completion by `fsem_typed` and `fsem_total`); `den_rewrite` also gives equality of terminating
denotations. It is not an adequacy theorem for infinite Core executions.

**Peephole family** (`Opt.Rules`). Each rule has one lemma at the minimal hole (`valid_neutral`,
`valid_eqz3`, `valid_dropGet`, `valid_dropGlobal`, `valid_teeForm`, `valid_rseSet`,
`valid_rseTee`, from run equations such as `neutral_runEq`, `eqz3_runEq`, `dropGet_runEq`,
`dropGlobal_runEq`, `teeForm_runEq`, `rseSet_runEq`, `rseTee_runEq`) and one-line corollaries
in every module (`*_module`) and every context (`*_inContext`). The rules are `i32.const k; op`
⟶ ε for six neutral operators; `eqz; eqz; eqz` ⟶ `eqz`; `local.get x; drop` ⟶ ε;
`global.get x; drop` ⟶ ε; `local.set x; local.get x` ⟶ `local.tee x`;
`local.get x; local.set x` ⟶ ε; `local.get x; local.tee x` ⟶ `local.get x`. Refuted at the
smaller hole: `i32.const 0; i32.add` traps on an empty stack (`addZero_distinct_at_empty`). The
one-directional information results are strict: `call 0; drop` against the empty code is
distinguished in some completion of the least informative model, not in every completion, and
equivalent over the more informative model `pureZero` (`callDrop_distSome_top`,
`callDrop_not_distEvery_top`, `callDrop_equiv_pureZero`).

**wasm-merge as amalgamation** (`Opt.Merge`, a sketch with proofs). Signatures are sets of
function names under inclusion. A model of `X` is a name-indexed environment unspecified outside
`X`; `namedInst` is the observational institution of this model functor. `amalgam_reduct_left`,
`amalgam_reduct_right`, `amalgam_unique`: two models agreeing on the **whole intersection**
`X₁ ∩ X₂` have exactly one common extension to `X₁ ∪ X₂`. The analogy with wasm-merge assumes a
syntactic linker has already renamed unrelated clashes; this is not implemented or verified.
`merge_sat`: a sentence satisfied by each side's model holds, translated along the inclusions,
in the amalgam. Tying the amalgam to a syntactic merge of fragment modules (`fsem` of the merged
module) is open.

## Grounding

Code under `Silmaril.Wasm.FnInst.Ground`, proofs under `Silmaril.Proofs.Wasm.FnInst.Ground`.
This layer relates segment rewrites to the library's Core semantics and its code-simulation
closure (`BaseSim`, `CodeSimClosed.exportEquiv_of_baseSim`).

- **Frame-free left sides, proved.** `Ground.Defs` states segments over the library's own
  instructions, frames and values (`GInstr`, interpreter `run`, adequacy `run_steps` and
  inversion `step_inv` against `Execution.Core.Step`). A pair is *good* when it has equal runs
  from every frame and stack where the left side runs (`RunRef`), and its left side is
  stack-only and not all constants, or one `local.get` followed by stack-only code that never
  gets stuck. `gBaseSim` gives `BaseSim` for all good pairs (`GBI`) at every profile, and
  `exportEquiv_of_good` gives export equivalence of modules whose bodies differ by good pairs
  anywhere, under the closed host at every deterministic profile.
- **Refuted in general.** `not_baseSim_twoSets`: `i32.const 1; local.set 0; i32.const 2;
  local.set 0` and `i32.const 2; local.set 0` have equal runs but are a `BaseSim` pair for no
  runtime relation and no rank, because the intermediate frame is never reached on the right.
- **Opt equivalences.** `good_of_runEq`: an opt `RunEq` of typed stack-only segments whose left
  side forces its inputs to be `i32` is a good pair. The opt rule lemmas transfer unchanged
  (`good_neutral_opt`, `good_eqz3_opt`).
- **Writes.** `wDeferredSim` (`Ground.Forced`) gives `DeferredBaseSim` for `GoodW` pairs: local
  code that may write locals and access several, then stack-only code. The `twoSets` pair is an
  equivalence at every profile through this route.
- **Stage proofs restated.** `dropGet_sound_ground` and `rseLine_sound_ground` restate the
  `wasm-opt` stages as one rule lemma plus the generic transfer, at deterministic profiles.
  `rseLine_sound_ground_any` holds at every profile. The full `neutral-ops` and `eqz-pair`
  stages hold at every profile through a stack fragment `NInstr` with both integer types, the
  trapping operators, `select` and `br_if` (`nBaseSim`, `neutralOps_sound_ground_any`,
  `eqzPair_sound_ground_any`). `gTypedSim` gives `TypedBaseSim` for right sides that read
  several locals, and with it `drop-get` at every profile (`dropGet_sound_ground_any`).
- **`wasm-check` statements as sentences.** `Ground.Check.checkInst`: signatures an export
  index, sentences `m ⊑ m'`, `m ≐ m'`, `∧` over candidate modules, models a profile and a
  behaviour relation, satisfaction `ModRefines`/`ModEquiv`. `proved` reports are validity;
  `refuted` reports are non-satisfaction at the reference profile. Under related computed
  instances (`InstRel`), the bridges' simulations give the `checkInst` sentences in every model
  with `Rel.eq` (`Ground.Link`). `instRel_of_bodiesRel` derives `InstRel` from
  `ModuleBodiesRel`, since instantiation never reads function code; so the `checkInst`
  sentences follow from `ExportEquiv`'s hypotheses alone (for example `teeForm_sat`,
  `neutralOps_sat`).
- **Open.** Globals, memory and calls inside grounded pairs (a store-threaded `run` and a forced
  store step); reads of different locals on the untyped left side; VC-stage verdicts as
  institution sentences; identifying `checkInst`/`GBI` with the core and models institutions.

## Known limitations

- **Duplicate notions across tracks.** The abstract hole exists three times: core
  `SegTy`/`HoleSig` (`Core.Defs`), opt `HSig`/`Seg` (`Opt.Seg.Defs`, typed by stack heights,
  morphisms are typed contexts) and ir `Hole`/`Frame` (`IR.Lang.Defs`). Contexts exist twice:
  core `Ctx` (all index spaces) and models `Ctx`/`Sig` (function types only). Code holes exist
  in core `Frag.Hole` and as plugging in opt. Identifying them (for example opt `segInst` as an
  instance of core `holeInst`, models `FnSem` as a reading of a core `Lang`, ir `Frame` hosted
  by the core signature category) is open; nothing relates them by a comorphism yet.
- **opt:** the fragment (`i32`, locals, globals, calls; no blocks, branches, loops, memory,
  tables, other value types or exceptions) has its own big-step semantics over sets. Its
  per-rule proofs are therefore not comparable in size with the `wasm-opt` stage proofs over the
  full Core semantics. Refinement at module level (needs `run` monotone in the environment and
  an inclusion form of `fsem_rewrite`) is open. The grounding layer above covers stack-only and
  local-only pairs, not globals, memory or calls.
- **core:** no comorphism hole → one; no typed congruence (needs stack typing of contexts); no
  module-level equivalence from the all-function institution; refinement and distinction are
  not sentences (distinction is a predicate on partial models). The fragment has no validation,
  no block arities and no loops.
- **models:** models (c) are relations, not game strategies; interfaces are local to the track;
  only distinction in *some* completion is defined (an inconsistent completion satisfies every
  sentence); no comorphism (only a validity transfer) into `Entry.entryEquiv`; the fragment has
  no locals, blocks or memories.
- **ir:** languages are call-free, so contexts carry no observable information; whole-function
  bodies only (a segment variant needs a segment-level simulation of the continuation-passing
  `compileFunc`); no lemma linking `bir` equations to `ExportEquiv` through `CoreCert.LeafFun`
  and `CoreCert.exportEquiv_modRel`; the lowering `toBFunc?` is partial, so there is no
  comorphism `fragNative → bir`.

## Source map

All names are under `Silmaril.Wasm.FnInst`; proof modules are under
`Silmaril.Proofs.Wasm.FnInst`.

| Claim group | Source |
| --- | --- |
| Core index spaces, declaration embeddings, empty context | `Ctx.Defs`: `Kind`, `Decl.Emb`, `Ctx`, `Ctx.Hom`, `Ctx.empty`, `Ctx.ofEmpty` |
| Core handler semantics and four focus variants | `Core.Defs`: `Lang`, `SegEq`, `FnEq`, `HPres`, `FnAtom`, `holePres`, `onePres`, `setPres`, `allPres` |
| Focus translations, model expansion and borrowing | `Comor.Defs`, `Comor.Thms`: `oneToSet`, `setToAll`, `holeToAll`, `oneToAll` and their results |
| Partial bodies, completions, information and distinction | `Partial.Defs`, `Partial.Thms`: `PModel.Completes`, `den`, `InfoLe`, `HPres.partialPlain`, `partial_sat_mono`, `distAll_mono`, `distSome_anti`, `not_sat_of_distAll`, `valid_partial_iff`; `Frag.distSome_not_mono` |
| Generic plugging, free-type premise and typed hole transfer | `Peephole.Defs`, `Peephole.Thms`: `Plug`, `SegTy.Free`, `hole_valid_transfer`, `peephole_empty`, `congr_entails` |
| Core fragment, length-only fitting, rules and refutations | `Frag.Defs`, `Frag.Thms`: `exec`, `Fits`, `frag`, `Hole.congr`, `plug_no_reduct`, `constFold_valid`, `constDrop_valid`, `getSet_valid`, `addZero_valid`, `addZero_not_free`, `addZero_everywhere` |
| Models syntax and semantics, solutions and information | `Models.Base.Defs`, `Models.Base.Thms`: `FnSyntax`, `FnSem`, `Sol`, `PMod`, `PMod.den`, `Le`, `bot`, `den_reduct`, `den_anti`, `sol_update_eq` |
| Three model institutions and transfer | `Models.Inst.Defs`, `Models.Inst.Thms`: `semInst`, `bodyInst`, `kInst`, `semToBody`, `kToBody`, `valid_k_iff`, `sat_mono`, `transfer`, `distinctSome_anti` |
| Replacement into the entry logic | `Models.Entry.Defs`, `Models.Entry.Thms`: `Closed`, `entryPoints`, `Closed.replace`, `moduleEquiv_replace`, `entry_valid_replace` |
| Versions | `Models.Version.Defs`, `Models.Version.Thms`: `Versioned`, `vInst`, `forget`, `AdmValid`, `valid_up_iff`, `admValid_anti` |
| Models fragments and counterexamples | `Models.Frag.{Defs,Thms}`, `Models.FragK.{Defs,Thms}`: `eval`, `adm`, `not_admValid_up`, `add_zero_left`, `addT`, `evalT`, `dropDouble_not_valid_k` |
| IR generic institutions and exact translations | `IR.Lang.Defs`, `IR.Lang.Thms`: `Frame`, `Lang`, `Lang.Tr`, `Tr.comorphism`, `modelExpansive`, `valid_iff` |
| IR languages, optimiser premises and round trips | `IR.Bodies.Defs`, `IR.Bodies.Thms`, `IR.RoundTrip.Thms`: `BirBody`, `ofBir`, `toSSA`, `ofSSA`, `equiv_lower_iff`, `optimize_valid`, `optimizeSSA_valid`, `optimizeFuncNative_valid` |
| IR context irrelevance and the five-node graph | `IR.Frames.Defs`: `modFrame`, `valid_in_every_module`, `sat_info_mono`; `IR.Graph.Defs`: `graph`, `graph_pathModelExpansive` |
| IR bridge to Core 3.0 | `IR.Core.Thms`: `core_behaviours_of_equiv`, `core_behaviours_of_sat` |
| Opt semantics, completions and call-depth modules | `Opt.Seg.Defs`: `Env.Completion`, `run`, `chk`, `RunEq`, `fsem`, `den`, `Mdl.Typed`, `Mdl.Rewrites` |
| Opt typed contexts, scoped sentences, positive formulas | `Opt.Inst.Defs`: `HSig.Hom`, `plug`, `Form`, `holds`, `Form.Positive`, `Model.reduct`, `Sen`, `segPlain` |
| Opt transfer, module and distinction premises | proofs `Opt.Inst.Basic`: `runEq_plug`, `sat_plug_equiv`, `holds_mono`, `distEvery_of_plug`, `peephole_module`; proofs `Opt.Seg.Basic`: `run_rw`, `fsem_typed`, `fsem_total`, `fsem_rewrite`, `den_rewrite` |
| Opt peephole family and information examples | `Opt.Rules.Defs`, `Opt.Rules.Thms`, proofs `Opt.Rules.Basic` and `Opt.Rules.Info`: `Neutral`, `valid_*`, `*_module`, `*_inContext`, `addZero_distinct_at_empty`, `callDrop_*` |
| Named model amalgamation | `Opt.Merge.Defs`, `Opt.Merge.Thms`: `NModel.amalgam`, `Agree`, `amalgam_reduct_left`, `amalgam_reduct_right`, `amalgam_unique`, `merge_sat` |
| Grounding bridges | `Ground.Defs`, `Ground.Thms`, `Ground.Forced.{Defs,Thms}`, `Ground.Num.{Defs,Thms}`, `Ground.Typed.{Defs,Thms}`, `Ground.Opt.{Defs,Thms}`, `Ground.Rules.Thms`: `GInstr`, `RunRef`, `GBI`, `GoodW`, `NInstr`, `exportEquiv_of_good`, `good_of_runEq`, `dropGet_sound_ground`, `rseLine_sound_ground`, `neutralOps_sound_ground_any`, `eqzPair_sound_ground_any`, `dropGet_sound_ground_any`; proofs `Ground.Sim`, `Ground.Refute`, `Ground.Forced`, `Ground.NumSim`, `Ground.Typed`: `gBaseSim`, `not_baseSim_twoSets`, `wDeferredSim`, `nBaseSim`, `gTypedSim` |
| `wasm-check` sentences | `Ground.Check.{Defs,Thms}`, `Ground.Link.{Defs,Thms}`, `Ground.Inst.Thms`, `Ground.Num.Thms`: `checkInst`, `InstRel`, `teeForm_sat`, `neutralOps_sat`; proofs `Ground.Inst`: `instRel_of_bodiesRel` |
