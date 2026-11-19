# Handle-based tree acceptors: design and coverage

This development answers: *what trees does a module accept* when it talks to its environment
through **handles** (`i32` values the environment interprets as trees), rather than through
bytes in memory? It covers writer (constructor) APIs, reader (inspection) APIs, their
combination, parsing sessions, the tree families they produce, abstract acceptors over those
families, and the link to core Wasm modules.

The checklist below maps every item of the original request (1–9) and the additional cautions
to files, theorem names and tests. Status: **done** (in this branch, built with `--wfail`),
**partial** (what exists and what does not), **planned** (nothing yet). Nothing marked planned
is claimed anywhere in the Lean sources.

## Layers

| Layer | Region | Modules |
| --- | --- | --- |
| Host models (generic) | Semantics | `Silmaril.Semantics.Accept.Host.{Defs,Thms}` |
| Handle APIs: writers, readers, combined, node environments | Semantics | `Silmaril.Semantics.Accept.Handle.{Defs,Thms,Examples}` |
| Parsing sessions | Semantics | `Silmaril.Semantics.Accept.Parse.{Defs,Thms,Examples}` |
| Tree families, AST signatures, APIs, patterns | Formats | `Silmaril.Formats.SExp.Family`, `…SExp.Api`, `…SExp.Pattern` |
| Wasm modules, decoders, checkers | Wasm | `Silmaril.Wasm.Game.HandleAccept.{Defs,Thms}`, `…HandleAccept.Checkers.{Defs,Thms}` |

Proofs longer than a few lines are under `Silmaril/Proofs/<Region>/…` and reached only through
the `Thms` headers.

### The common semantics

A module's behaviour is a set of **event traces**; an event is a call with the answer the
module observed (`Host`). A host model says which answers the environment may give and what a
call makes the module accept; `Host.lang h T` is the union over traces. Three kinds of
environment behaviour are kept apart everywhere:

* *nondeterministic answers* (several responses: interning or not, allocation failure,
  arbitrary data for invalid reads);
* *restriction* of the environment (fewer responses; `Sim` gives inclusion of languages; fixed
  environments `fixedLang`, environment sets `Envs`);
* *traps* versus *undefined behaviour* (`chaos`: the event and everything after accepts every
  tree, the top element). A trap is **call-local** by default, as in Wasm: it aborts the current
  export call (phase `aborted`), the instance and its store persist, and the next export call
  (`enter`, decoded from the export-call move of a play) resumes; a session abort (phase `dead`,
  nothing follows) is an optional stricter policy.

Environments are always explicit: writer stores (`WState.store`), fixed environments
(`fix = some ρ`, `fixedLang … Envs`), reader environment sets (`readerLang … Envs`), parse
environments (`parseRel … Envs`).

## Audit against the request

Each requirement of the original request (1–9) and of the follow-ups, with where it is met at
the abstract level (Semantics/Formats) and in Wasm (core modules with proved soundness and a
run showing acceptance), or why not. "Abstract" results quantify over every module trace set;
Wasm examples are concrete modules.

| # | Requirement | Abstract | Wasm | Limits |
| --- | --- | --- | --- | --- |
| 1 | writer `symbol(string)`, `sexp(list<i32>)`, `accept(i32)`; arbitrary fresh handles, interning | `Handle.Writer`, `Fresh`, `Run.store_extends` | memory `hiMod_lang`, `pairMod_lang`; instance-play `twoWords`, `sxPair` | |
| 1 | invalid accept: mandatory trap (call-local), session abort, ignore, UB, fixed-env UB, error return | `callTrap`/`sessionTrap`/`ignore`/`ub`, `fixedLang`, chain + strictness, `writerLang_eraseErr_eq` | `callTrap` is the Wasm-facing policy (export calls decode to `enter`); error-return `accept`: `errAccept_sound` (within words and `nil`), runs `errAccept_accepts_word`, `errAccept_accepts_nil` (error branch) | |
| 1 | sentinel 0/−1, inclusion with exact assumptions, capacity | `writerLang_noRet_subset`, `writerLang_subset_of_oneFailure`, `sentinel_twice`, `writerLang_sentinel_swap`, `successes_length_le` | `twoWordsZ`, `twoWordsM` | raw inclusion is false (counterexample) |
| 1 | constructed set (downward closed), `accept_all` since start, batches | `writerLang_downClosed`, `batch_not_downClosed` | `allAccept_sound` (bound `allL`, `allL_downClosed`), `allAccept_accepts`; `batchAccept_sound`, `batchAccept_accepts`; **exact batch language** `AcceptVariants.Batch`: import-level ghost bridge `strategy_gag` (`GISpec`, `GAG`, `GhostGameSat`; ghost in the host code, as `MemSound.Ghost`), batch bridge `storeLang_subset_of_gag` (ghost = current batch, `batchGSpec`), `consXLang_sound_of_ghostSat`; `batchAccept_lang` (⊆ `keptL` = `nil` and `(w)`, the kept batch), `batchAccept_drops` (no word, the dropped batch, is accepted), `batchAccept_fixed_lang`, `batchAccept_kept` (with the run `run(3)`) | `batchAccept`: upper bound `keptL` with runs at the fixed argument `3` (not every `(w)` is exhibited); the ghost bridge covers store semantics and fixed environments for policies without UB |
| 2 | readers `tag`/`symbol`/`sexp -> list<i32>`; `children`/`child`; fixed env; module-chosen handles, any export sequence | `Reader`, `readerLang`, `Env`/`Env.ofTotal` | cons checkers, n-ary `count`/`child` checkers, memory `items(h, retptr)`, `string_text`, `keyword_text` | |
| 2 | invalid reads: arbitrary, trap, typed error, default, UB; arbitrary ≠ UB | `OnBadRead`, `error_iff_invalid`, `arbitrary_ne_ub`, `arbitrary_uncertified` | checkers use trap; typed error: `errD_disjoint`, `polLang_subset_of_AG` (every policy but UB), `carCheck_sound`; counterexample runs `carNoCheck_unsound_dflt`, `carCheck_unsound_arbitrary`; `carCheck_accepts` | |
| 2 | atoms `blob`, `string`, `word(i64)`, keywords: writers and readers | Family atoms | writers `atomMod` (symbol/string/blob/keyword), `word_lang`; readers string, keyword, symbol (`symTextMod_lang`), blob (`blobMod_lang`: exactly the 2-byte blobs), `word` | |
| 3 | first-class APIs for the ten families incl. Rivest canonical vs hinted | `Family`, one parameterized API per style | **every family × API pair** has a module proved sound with a positive run: `Families.Matrix` (`<family>_<api>_sound`, `<family>_<api>_live`, `api ∈ naryW, consW, naryR, consR, astW, astR`; 60 pairs of theorems for the 10 families × 5 APIs, AST split into writer and reader), instances of generic modules proved once for every atom type: writers over atom tables `MemSound.Tab` (`tab_pair_lang`: `pairAtomMod` writes exactly `(a b)`; `tab_pairAst_lang`: its `sexpSig` tree; `tab_cons_lang`: `consAtomMod` writes exactly `(a)`), readers `MemSound.Probe` (`probeMod`: `next(h, 0)`, then a memory-returning `leaf(c, retptr)`; `nary_sound` ⊆ `firstAtoms`, `cons_sound` ⊆ `carAtoms`, `ast_sound` ⊆ `firstLeaves`, runs `nary_live`, `cons_live`, `ast_live`; payloads `bytesPay` (`list<u8>`), `kindPay` (`{bytes: list<u8>, kind: u32}`), `hintPay` (`{octets: list<u8>, hint: list<u8>}`, null hint pointer = no hint), `u64Pay`); word trees: `word_lang`, `twoWords`, the `u64` probe. **Full signatures**: every table names all atom imports of its family, one decoder per name (`AtomDec.seg`/`.seg2`): symbols `symbol`; bytes, Rivest `blob`; symStr `symbol`+`string`; symBytes `symbol`+`blob`; symStrBytes `symbol`+`string`+`blob`; symStrKw `symbol`+`string`+`keyword`; symStrKwBytes all four; hinted `blob`+`hinted(hptr, hlen, ptr, len)` (`hintedTab_hinted`); readers decode every kind (`kindD`: kind code `c` ↦ `ks[c]`; hinted: `hintPay`). Earlier examples: `Families/Mem`, `bpairMod`/`rivest_bpairMod`, `hinted_lang`, `hintedSep_lang`, `MemSound.ListCheck` | examples are small fixed languages (one two-element list, one cons pair, one-child reader checks); the soundness bounds are for modules that import and call one atom import each, decoded through the full table: a mixed family's writer run uses one kind, the hinted writer runs are hint-free (`hinted` is decoded but not called; a module calling it: `MemSound.Hinted`, n-ary only); reader runs read one kind (hinted: with a hint); the word cons writer's run is at the specification profiles; no looped any-length checker |
| 4 | generic branch + leaf tags with WIT payloads; variadic, fixed, mixed arity; SExp correspondence | `AstSig`, `WitSig`, `sexpW_hom`, `SExp.equivAST`, `leaf_children_not_wellArity`; owned handles: `Own.ownHost` (resource table in the host state, moves consume), `resolveOp_congr`, `run_congr`, `ownLang_congr` (dependence on the table only at moved handles), `no_second_move`, `unresolved_step`, `ownLang_eq_of_linear`, `linear_of_ob` (`obProto`), `borrow_rejected` | `astMod`, `calcMod`, `appMod`, `binMod`, `glyphMod`, `addCheck`; owned handles: `ownMod` (`ownMod_sound`, `ownMod_dead`, `ownMod_live`, `ownMod_lang`: exactly `{res(rep)}` for the table's live `own<0>` handle `1`), `twiceMod` (`twice_traces`, `twice_accepts`: the double move accepts nothing; `twice_via`: the stateless reading would accept); canonical-ABI layout for the whole domain (`layout_toWit`, `valsLayout_toWit`); decoding equal to the pure reference loaders for scalar vectors of all nine scalars (`loadVals_loadRecord`), single scalars, floats and chars (`loadVal_scalar`, `loadVal_f32`, `loadVal_f64`, `loadVal_char`) and UTF-8 strings below `maxStringByteLength` (`readVal_string_loadStringFromRange`) | payload domain: every WIT value type with a memory representation and no async semantics (`bool`, the eight integers, `f32`/`f64` (NaNs canonicalised), `char`, `string`, `list<t>`, `list<t, n>`, `record`, `tuple`, `variant`, `enum`, `option`, `result`, `flags`, nested) and the handles `own<r>`/`borrow<r>`: a **top-level** `own` field moves its handle into the tree under the resource-table semantics (`MemSound.WitAst.Own`: the tree holds the representation from an explicit table, consumed once; an `own` nested in a list/option/record is no value), `borrow` is rejected (no value in a stored tree, `borrow_rejected`); not `future`, `stream`, `error-context` (pending async semantics), `map` (use `list<tuple<k, v>>`); lists, fixed lists and composite types are not compared with any reference loader (none is pure); not compared with the monadic `Canon.load`; no length limits; no flattening |
| 5 | cons API with/without nil; SExp vs SExp2; properness; roundtrips | `consW`, `pairW`, `SExp2.toSExp?`, `Pat.toSExp2_image_lang` | cons checkers, `combCheck` (Tree2), `consMod`, `consMix` | |
| 6 | union/intersection, images/preimages, list combinators, patterns, AST→sexp encodings | `Pattern`, `tuple_inter`, `AST.encode_injective`, `enc_collides` | — | abstract by nature |
| 7 | executable checkers: proper lists (SExp2), word lists n-ary and binary, sorted with subset | — | `properCheck` (spine), `recProperCheck`, `recFullCheck` (recursive, total), `wordsCheck`, `sortedCheck`, `wordsNCheck`, `sortedNCheck`, `combCheck`; replays | signed `i64` order; handles are opaque `i32` |
| 8 | combined writer+reader, consistent future reads, persistent meanings | `combined_write_read`, `Reader.Mono.persist`, `write_persists` | `readBack` writes `(x)` and reads it back (`combLang_subset_of_AG`, `crun_facts_init`): `readBack_sound`, `readBack_accepts_0/_5` | upper bound plus runs at fixed arguments |
| 9 | parse(data), append/done, chunks with `used`, cursor, failure advancing, projections | `Parse`, `parseRel_slice(_eff)`, `parseRel_done`, projection laws and counterexample | `nzParse`, `listParse`, `stackParse`, `chunkStack`, `chunkTake`, `chunkRingN`, pull `echoMod`, exact `drainEcho` | `stackParse`/`chunkStack` return newest-first lists |
| F | call-local trap, pre-trap effects persist | `callTrap`, `write_persists`, `persist_seven` | export calls → `enter` | |
| F | combined writer+parser relation with a real parser | `Mixed`, `mixedRel_subset_of_AG` | `listParse`, `stackParse`, `drainEcho` | |
| F | memory-observing soundness; list children, chunk inputs, items reader | `MemSound`, ghost bridge `tagTraces_gpre` | `pairMod`, `itemsMod`, `echoMod`, `drainEcho` | export-argument chunks in memory are not expressible in the traced-session model (pull-style `read` is) |
| F | recursive vs spine properness | `SpineProperList`, `recProperL_ssubset_properL` | `properCheck` vs `recFullCheck` | |

## Coverage checklist

### 1. Writer acceptor API

| Item | Status | Where |
| --- | --- | --- |
| `symbol(string)->i32`, `sexp(list<i32>)->i32`, `accept(i32)` | done (abstract), see 7 for Wasm | `Handle.Writer`, `WEv.write/accept`; S-expression instance `Formats.SExp.Api` |
| successful handles arbitrary, never reused; interning allowed | done | `Fresh`, `Policy.intern`; persistence `Run.store_extends`, `write_persists` |
| invalid accept: mandatory trap (Wasm-facing, call-local) | done | `OnInvalid.callTrap` (the default), `WStep.acceptCallTrap` (`aborted` phase until the next export call `WEv.enter`, `WStep.resume`; `WStep.aborted_inv`: only `enter` follows, store and batch unchanged). Effects before the trap persist: `write_persists`, `Examples.persist_seven` (write `7` at `1`, invalid accept, `enter`, `accept 1` accepts `7`) |
| invalid accept: session abort (optional, stricter) | done | `OnInvalid.sessionTrap`, `WStep.acceptSessionTrap` (`dead` phase: nothing follows, not even an export call, `WStep.not_dead`); within one export call it agrees with `callTrap` (`writerLang_callTrap_eq_sessionTrap`, traces with no `enter` after their first event) |
| invalid accept: ignored, traps permitted as a foreign call | done | `OnInvalid.ignore` (a trace may end anywhere) |
| invalid accept: UB = all behaviour | done | `OnInvalid.ub`, `WStep.acceptChaos`/`chaos` |
| UB restricted to fixed `i32 → tree` environments agreeing with allocations | done | `fix = some ρ`, `Agrees`, `WStep.writeFixed/acceptFixed`, `fixedLang` |
| error-return accept variant | done | `WEv.acceptErr`, `writerLang_subset_eraseErr`, `writerLang_eraseErr_eq` (`ResultOblivious`) |
| relationships under explicit observations | done | `writerLang_mono` (`Policy.Le`, ranks `sessionTrap ≤ callTrap ≤ ignore ≤ ub`), `writerLang_onAccept_mono`, chain `writerLang_sessionTrap_subset_callTrap`, `writerLang_callTrap_subset_ignore`, `writerLang_ignore_subset_ub`; fixed environments `writerLang_subset_fixedLang`, `fixedLang_subset`; strictness `Examples.callTrap_ne_sessionTrap` (invalid accept in call 1, valid in call 2: `[accept 0, enter, write (lit 7) → 1, accept 1]`), `Examples.callTrap_ne_ignore` and `sessionTrap_ne_ignore` (invalid then valid in the same call), `fixed_lt_ub`, `fixed_trace_lt_ub` |
| failure sentinel `0` or `-1` | done | `Policy.sentinel`, `writerLang_sentinel_swap` (the two correspond by the handle swap `0 ↔ -1`, not by numeric identity) |
| acceptance with sentinel ≤ without, exact assumptions | done | The anticipated raw inclusion `writerLang (sentinel s) T ⊆ writerLang (no sentinel) T` is **false** (`Examples.sentinel_twice`: two failures at handle `0` for different trees cannot be read as allocations, since a sentinel-free environment never returns one handle for two trees). What holds: (1) restriction: traces that never receive the sentinel (`writerLang_noRet`, `writerLang_noRet_subset`); (2) reinterpretation: with trapping invalid writes, a trace with at most one failure whose result is never used again (`OneUnusedFailure`) accepts no more than without a sentinel, reading the failure as a successful allocation of `s` (`accepts_subset_of_oneFailure`, `writerLang_subset_of_oneFailure`, `Examples.ten_one_failure`); (3) `0` vs `-1` correspond by the handle swap (`writerLang_sentinel_swap`) |
| finite `i32` capacity, freshness vs aliases/interning | done | `successes_nodup`, `successes_length_le` (no interning: at most `\|{h ≠ sentinel}\|` successes) |
| consistent environments | done | stores only grow (`Run.store_extends`); fixed `ρ` must agree with every allocation |
| constructed set as accepted, downward closed | done | `WEv.acceptAll`, `writerLang_downClosed` (`Writer.ChildRel`) |
| `accept_all()` since start; `accept_all(bool)` batches since previous call | done | `WEv.acceptAll`, `WEv.acceptBatch`; batches are not downward closed: `Examples.batch_not_downClosed` |

### 2. Reader APIs

| Item | Status | Where |
| --- | --- | --- |
| `accept(i32)`, `tag`, `symbol`, `sexp(i32)->list<i32>`; `children` count, `child(i32,i32)` | done (abstract signature), S-expression queries in `Formats.SExp.Api` | `Reader`, `REv` |
| fixed environment `i32 → tree` or `option tree` | done | `Env` (partial), `Env.ofTotal` |
| handles chosen by the module, arbitrary export sequences | done | traces are arbitrary event lists with export-call boundaries `REv.enter`, not a single `check(h)` |
| invalid accept | done | `OnInvalid` as for writers: `RStep.acceptCallTrap` (`aborted` until `enter`), `acceptSessionTrap` (`dead`), `acceptIgnore`, `acceptChaos`; chain `readerLang_sessionTrap_subset_callTrap`, `readerLang_callTrap_subset_ignore`, `readerLang_ignore_subset_ub`; `readerLang_callTrap_eq_sessionTrap` within one export call |
| invalid reads: arbitrary data, trap, typed error, default, UB | done | `OnBadRead.{arbitrary,trap,dflt,ub}`, typed error = `dflt` + `ErrorDisjoint` (`error_iff_invalid`) |
| arbitrary data ≠ UB | done | `Examples.arbitrary_ne_ub`, `Examples.arbitrary_uncertified` |
| relations | done | `readerLang_mono` (`OnBadRead.Le`, accept ranks), `trap_reads_correct`, `readerLang_trap_subset` (certified acceptance, every accept policy but `ub`; `readerLang_trap_subset_callTrap` for the call-local trap, reads stay correct across export calls) |
| more atoms: `blob(bytes)`, `string`, `word(i64)`, keywords | see 3 | `Formats.SExp.Family` |

### 3. First-class family APIs

| Item | Status | Where |
| --- | --- | --- |
| symbols, byte trees, word trees, symbols+strings, symbols+bytes, symbols+strings+bytes, symbols+strings+keywords, symbols+strings+keywords+bytes | done (tree types and writer/reader signatures) | `Formats.SExp.Family.Defs`: `SymbolSExp`, `ByteSExp`, `WordSExp`, `SymStrSExp`, …, `Atom ks`, `AtomKind`; one parameterized writer `Api.sexpW α` and reader `Api.sexpR α H` instantiated per family (no per-family code duplication) |
| Rivest canonical vs display hints | done | `RivestSExp` (hint-free, existing), `HintedSExp` with `HintedSExp.toSpki` into RFC 9804 `Spki.Sexp`, `HintedSExp.toSpki_injective`; the docstring explains that canonical encodings carry hints |
| Wasm import decoders for string/byte-carrying imports (`symbol(string)`, `blob`, `sexp(list<i32>)`) | done (decoders, structural bound) | `Wasm.Game.HandleAccept.Memory`: `memWrite`/`memAccept` roles over memory-observing traced sessions (`memTraces` on `tagTraces`), `memWriterLang` over `SymStrBytesSExp`; `inp_of_tsession`, `memWriterLang_subset_atoms`; 12 kernel-checked decodings in `Memory.Examples`. An assume/guarantee bridge for memory-carrying traces is **not done** |
| memory-observing soundness | done (upper bounds) | `HandleAccept.MemSound`: `MemContract` (call guarantee `pre` sees the callout and memory at the call; `ans` assumption on decoded answers; `reply` host class), `MemSat` (Hoare-logic obligation), bridge `tagTraces_pre` by induction over `TSession`; `memWriterLang_subset`, `memFixedLang_subset`, `memReaderLang_subset` with a canonical-ABI `items(h, retptr)` reader. Examples: `hiMod_sound` (accepts only the symbol `hi`), `pairMod_sound`/`pairMod_fixed_sound` (only `(a b)` of its symbols), `itemsMod_sound`/`itemsMod_sound_callTrap` (only 2-element lists). Host class: answers keep the store's functions and memory count, may rewrite memory, return the import's result shape. Export-argument chunks in memory are not expressible in `TSession` (the embedder never writes memory between export calls); pull-style `read` imports are. Non-vacuity: `MemSound.Live` builds concrete traced sessions (`countEnv` handle host, `itemsEnv` retptr host): `hiMod_lang` (exactly `{hi}`), `pairMod_lang` (exactly `{(a b)}`, no sentinel), `itemsMod_lang_univ` (exactly the 2-element lists over all fixed environments). String/blob/keyword atoms: generic `atomMod` with `str_lang`, `blob_lang`, `kw_lang` (new `keyword(ptr,len)` decoder); `Families/Mem` lists the memory instantiations per family. Pull-style chunks: `read(buf,cap)` answers decode to `PEv.feed` (memory after the answer), `finish(used,h)`; `echo_short` (relates at most 16 bytes), `echo_live` (relates `[68,69]`); the echo tree handle is a constant. Byte/Rivest trees through memory: `bpairMod_lang` (exactly the list of byte strings `61`, `62`), `rivest_bpairMod`, `bytes_bpairMod`. String reader `string_text(h, retptr)`: `textMod_sound` (only 2-byte strings), `textMod_live`. Writer + pull-chunk host `memMixedRel`: `blobEcho_len` (**length only**: the returned atom has as many bytes as were consumed), `blobEcho_live`; exact content is **false** against the admitted hosts (`blobEcho_not_exact`: if `blob` traps after `read`, the next `finish` consumes the stale chunk). **Ghost bridge** `MemSound.Ghost`: `GContract` (call guarantee `pre g o` in a ghost state `g` moved by `upd` over the decoded inputs), `GMemSat` (Hoare obligation in a specification world whose host codes carry the ghost, `gConfig g c = Config.mapH (·, g) c`; host-free steps commute by `Component.Reference.Step.mapH`, re-exported by `Component.Reference.HostMap.Thms`), bridge `tagTraces_gpre` (a call-decoded input meets `pre` in the ghost of the decoded prefix; admitted hosts are `ReplyEnvs reply`, unchanged), `gConfig_erase`. **One-point case**: `MemContract.toG` (ghost `Unit`), `memSat_iff_gMemSat` (`MemSat … K Inv ↔ GMemSat … K.toG (fun _ => Inv) ()`, by transferring step-indexed safety along the host relabelling `gConfig ()` in both directions) and `tagTraces_pre_of_gpre` (the conclusion of `tagTraces_pre` derived from `tagTraces_gpre`). **Exact content** `MemSound.Exact`: `drainEcho z` drains stale bytes with `finish(16|8|4|2|1, z)` before the `blobEcho` body; `drainEcho_exact` (`memMixedRel … ⊆ exactRel` against `blobReply`, **every** sentinel `z`, no UB; the instantiation shape `deOk_all` and the spec instance `deSpec_all` are kernel evaluations with `z` free, by `kernel_rfl`), `drainEcho_finish_bound` (≤ 16 bytes buffered at every `finish`), `drainEcho_no_stale` (the `blobEcho` stale pair is not related), non-vacuity `drainEcho_live`, `drainEcho_repeat` (two invocations), `drainEcho_after_trap` (the stale-chunk host: the drain consumes the stale bytes); liveness needs `onOverrun` `callTrap` or `ignore` (under `sessionTrap` the first drain overrun ends the session). **Keyword reader** `MemSound.KwText`: `keyword_text(h, retptr)` (`kwTextRoles`, `kwTextReaderLang_subset`), `kwTextMod_sound` (only keywords of two UTF-8 bytes), `kwTextMod_live_of` (every two-byte UTF-8 text `b₀ b₁`: the live session is parameterized by the bytes, against the host `itemsEnv (kwWord b₀ b₁) 0` writing them as the text), `kwTextMod_live` (`:hi`), `kwTextMod_bounds`, and **exact language** `kwTextMod_lang` (`= twoByteKws` over every set of fixed environments naming each two-byte keyword), `kwTextMod_lang_univ` (over all fixed environments). **Word trees** `MemSound.WordAtom`: `word(ptr)` reads the little-endian `i64` at `[ptr, ptr + 8)` (`wordWrite`, also `sexp(ptr, len)` nodes, `wordWriterLang` over `WordSExp`); `wordMod` (`i64.store 42`, `accept(word(0))`): `word_sound`, `word_live`, `word_lang` (exactly `{42}`). **Hinted Rivest atoms** `MemSound.Hinted`: `hinted(hptr, hlen, ptr, len)` (display hint and octets from memory; `blob` gives hint-free atoms; `hintedWriterLang` over `HintedSExp`); `hintedMod` (`accept(hinted(0, 2, 0, 2))`): `hinted_sound`, `hinted_live`, `hinted_lang` (exactly `{[hi]hi}`; hint and octets read from the same segment); separate segments: `hintedSepMod` (`i32.store 0x62616968` at `0`, `accept(hinted(0, 2, 2, 2))`: hint at `[0, 2)`, octets at `[2, 4)`): `hintedSep_sound`, `hintedSep_live`, `hintedSep_lang` (exactly `{[hi]ab}`), with the slice lemma `segment_sub` |

### 4. Generic branch/leaves and tagged ASTs

`Wit.Fragments.Thms` provides named `ScalarType` and `CompoundType` families, with
injective embeddings and partial inverses for `PTy` and WIT types. Scalars include
`char` and floats but not `string`. Compound constructors use existing payload types
for their members, and do not certify well-formedness or resource support.
`MemSound.WitAst.Fragments.Thms` relates their memory32 layouts and transports
existing decoder results without changing success or failure. The scalar `calcSig`
and compound `glyphSig` examples recover the existing signatures, so they use the
same ASTs, Core modules and accepted languages after embedding.

| Item | Status | Where |
| --- | --- | --- |
| generic `branch(children)` + designated leaves `tag(args)` | done | `AstSig`, `AST S := TExpr1 (Σ t, S.Arg t)` (reuses `TExpr`), `AST.WellArity`, `Api.astW` |
| typed heterogeneous WIT payloads | done | `PTy` (`bool`, `s8`…`u64`, `f32`, `f64`, `char`, `string`, `list t` (`bytes = list u8`), `fixedList t n`, `record`, `tuple`, `variant`, `enum`, `option`, `result`, `flags`; nested inductive, `DecidableEq` via `PTy.beq_iff`), `PTy.Val` (the Lean interpretation: floats as IEEE bits, `char` as `Char`, products, sums, `Fin n`, `BitVec n`), `PTy.Vals`, `WitSig.toAstSig`; `Wasm.Game.HandleAccept.Wit`: `toWit : PTy → WIT.ValType`, its left inverse `ofWit` (`ofWit_toWit`, defined exactly off names, `map`, handles and async types), `toWit_simple`, `toWit_injective`, `valEquiv E t : PTy.Val t ≃ (toWit t).Interp E` (with `valsEquiv`, `fieldsEquiv`, `casesEquiv`, `optEquiv`) |
| variadic `tag(args…, children: list<i32>)`, fixed arity `tag(args…, c₁…cₙ)`, mixed arities | done | one writer `astW`; Wasm fixed-arity decoders `Wasm.Game.HandleAccept.Ast` (`moduleAstWLang`, `moduleAstWLang_wellArity` for every module, `astWLang_sound_of_gameSat`); AST reader `moduleAstLang`, `astLang_sound_of_gameSat`; variadic imports carry a memory list (see `Memory`). **Through memory** `MemSound.Ast`: `tag(tagptr, taglen, children, n) -> i32` decodes the UTF-8 tag name at `[tagptr, tagptr + taglen)` and `n` little-endian `i32` child handles at `[children, children + 4n)` of the memory at the call (`Callout.tagNode`, `astWrite`, `astRoles`, `astWriterLang` over `astW strSig`; `strSig`: string tags, no payload, `Arity.star`); bridges `astFixedLang_subset`, `astWriterLang_subset` (instances of `rolesFixedLang_subset`/`rolesWriterLang_subset`); example `astMod` (`tag(16, 1, 0, 0)` for the leaf `a`, the returned handle stored at `[0, 4)`, then `accept(tag(16, 1, 0, 1))`): `astMod_fixed_sound`, `astMod_sound` (Hoare proof `ast_sat` in every fixed environment), `astMod_live` (traced session against the counting host), `astMod_lang` (exactly `{f(a)}`, no sentinel, no UB). **Typed payloads, fixed arities through memory** `MemSound.WitAst`, for every `S : WitSig` with tags numbered by `tagOf`: `node(tag, payload, children, n) -> i32` reads the payload vector of `S.params t` at `payload` **in the canonical ABI layout** (memory32): `PTy.layout`/`PTy.width`/`PTy.align` (`bool` 1/1, `s32`/`u32` 4/4, `s64`/`u64` 8/8, `string`/`bytes`/`list t` the `(ptr, len)` pair 8/4), the vector as the WIT tuple of its types (`valsLayout = ABI.recordLayout`, fields at aligned offsets, tail padding, padding never read; `readFields`, `readVals`), agreeing with the repository's ABI layout `ABI.layout .i32` through `Wit.toWit` (`layout_toWit`, `width_toWit`, `align_toWit`, `valsLayout_toWit`, `valsWidth_toWit`, `valsAlign_toWit`; sizes `ex_width_*`); `payload` must be aligned to `valsAlign` and `children` to four (REF `trap_if(ptr != align_to(ptr, alignment))`); `string`: UTF-8 of `[ptr, ptr + len)`, `bytes`: the octets, `list t`: `len` elements at `ptr + i * t.width` with `ptr` aligned to `t`, recursively (`list<string>`, `list<list<t>>`); payload lemmas `readPtrLen_encode`, `readVal_rest`, `readVal_string`, `readVal_bytes`, `readVal_list`, `readVal_list_misaligned`, `readVals_single`; kernel-checked examples over `exMem` (`ex_string`, `ex_string_utf8`, `ex_bytes`, `ex_bytes_not_utf8`, `ex_list_u32`, `ex_list_string`, `ex_list_list`, `ex_vals`, `ex_vals_padded`, `ex_vals_padded64`); **malformed inputs** decode to no value (`ex_bad_utf8`, `ex_out_of_bounds`, `ex_list_oob`, `ex_list_misaligned`, `ex_list_string_bad_utf8`, `ex_list_string_oob`, `ex_list_list_misaligned`, `ex_short`) and malformed calls to no event (`ex_node_misaligned_payload`, `ex_node_payload_oob`, `ex_node_one_child`, `ex_node_three_children`, `ex_node_leaf_child`, `ex_node_misaligned_children`, `ex_node_children_oob`, `ex_node_unknown_tag`, `ex_node_bad_utf8`, `ex_node_string_oob`, `ex_node_misaligned_pair`, with controls `ex_node_num`, `ex_node_add`, `ex_node_var`); `witWrite_none`: a rejected call has no write event, so under the bridges it makes no handle denote a tree. The supported domain (WitAst docstring): payloads are all of `PTy`, i.e. the WIT value types with a canonical-ABI memory representation and no resource or asynchronous semantics: `bool`, `s8`, `u8`, `s16`, `u16`, `s32`, `u32`, `s64`, `u64`, `f32`, `f64`, `char`, `string`, `list<t>` (`bytes = list<u8>`), `list<t, n>`, `record`, `tuple`, `variant`, `enum`, `option`, `result`, `flags`, nested to any depth; layouts `PTy.layout` (narrow integers 1/1 and 2/2, `f32`/`char` 4/4, `f64` 8/8, records/tuples `ABI.recordLayout`, variants/`option`/`result` `ABI.variantLayout` with the smallest discriminant (`discBytes`) and the payload at `caseOffset`, `enum` its discriminant, `flags` 1/2/4 bytes, `list<t, n>` in place), agreeing with `ABI.layout .i32` mutually over fields, cases and options (`layout_toWit`); decoding with the canonical trap conditions: floats with NaNs canonicalised (`ex_f32_nan`, `ex_f64_nan`), `char` only a Unicode scalar value (`ex_char_surrogate`, `ex_char_too_big`, `ex_record_bad_char`), discriminants in range (`ex_option_bad_disc`, `ex_record_bad_disc`, `ex_variant_bad_disc`, `ex_enum_bad_disc`, `ex_result_bad_disc`), `bool` any nonzero byte (`ex_bool_two`, REF `convert_int_to_bool`), flag bits above the label count ignored (`ex_flags_high`, REF `unpack_flags_from_int`); controls `ex_s8`, `ex_u16`, `ex_s16`, `ex_f32`, `ex_f64`, `ex_char`, `ex_char_astral`, `ex_fixed`, `ex_tuple`, `ex_record`, `ex_option_none`, `ex_option_string`, `ex_variant`, `ex_variant_a`, `ex_enum`, `ex_result_ok`, `ex_result_err`, `ex_flags`, `ex_list_tuple`, `ex_vals_glyph`, sizes `ex_width_glyph`, `ex_width_option_u64`, `ex_width_result`, `ex_width_variant`, `ex_width_enum257`, `ex_width_flags`, `ex_width_fixed`; `readVal_rest` (every value consumes exactly its width) for the whole domain; resource handles (`MemSound.WitAst.Own`, resource-table semantics): an `own<r>` payload field is read as its `u32` table index (`rawSig`, `ownRaw`), resolved in an **explicit resource table** `RT` (index ↦ resource type, representation, live) to the resource's representation (`resolveOp`; dead, missing or foreign-type handles and a double move inside one payload do not resolve) and **consumed**: the resource host `ownHost` keeps the table in its state, a second move of a handle is an invalid write under `onWrite` (`no_second_move`, `unresolved_step`), acceptance depends on the initial table only at the moved handles (`resolveOp_congr`, `run_congr`, `ownLang_congr`), and on traces moving no handle twice (in particular those the ownership protocol `obProto` accepts, `linear_of_ob`, `ownLang_eq_of_ob`) it is the stateless reading `viaRT` (`ownLang_eq_of_linear`); `ownMod` (the module owns handle `1` in the table; `ownMod_sound`, `ownMod_dead`, `ownMod_live`, `ownMod_lang`: exactly `{res(rep)}`) and `twiceMod` (`twice_accepts`: moving `1` twice accepts nothing; `twice_via`); only **top-level** `own` fields are resolved (nested ones are no value); `borrow<r>` is rejected in stored trees (`PTy.Val (.borrow r) = Empty`, `readVal_borrow`, `borrow_rejected`); not payloads: futures, streams, error contexts (pending async semantics) and `map` (despecialised to `list<tuple<k, v>>`). Arity: `Callout.witNode`, `witWrite`, `witRoles`, `witWriterLang` over `astW S.toAstSig`; `witNode_admits`, `witWrite_admits` (every decoded write has `(S.arity t).Admits` children); bridges `witFixedLang_subset`, `witWriterLang_subset`; example `calcSig` (`num`: one `s64`, arity `fixed 0`; `add`: no payload, arity `fixed 2`) and `calcMod` (`i64.store` of `1`, then `2`, at `[16, 24)` right before each `node(0, 16, 0, 0)`, the two handles at `[0, 8)`, `accept(node(1, 0, 0, 2))`): `calcMod_fixed_sound`, `calcMod_sound` (Hoare proof `calc_sat`), `calcMod_live` (traced session against the counting host), `calcMod_lang` (exactly `{add(num 1, num 2)}`, no sentinel, no UB). **String payloads**: `appSig` (`var`: one `string`, arity `fixed 0`; `app`: no payload, arity `fixed 2`) and `appMod` (`i32.store8` of the byte of `"f"` at `24`, then the pair `(24, 1)` as one `i64.store` at `[16, 24)`, right before each `node(0, 16, 0, 0)`, the same with `"x"`, the two handles at `[0, 8)`, `accept(node(1, 0, 0, 2))`): `appMod_fixed_sound`, `appMod_sound` (Hoare proof `app_sat`, decoding `var_node`), `appMod_live` (traced session against the counting host), `appMod_lang` (exactly `{app(var "f", var "x")}`, no sentinel, no UB). **Byte-string and list payloads**: `binSig` (`blob`: one `bytes`; `seq`: one `list<u32>`; both arity `fixed 0`; `pair`: no payload, arity `fixed 2`) and `binMod` (the byte `FF` at `24` and the pair `(24, 1)` before `node(0, 16, 0, 0)`; the `u32`s `7`, `9` as one `i64.store` at `[24, 32)` and the pair `(24, 2)` before `node(1, 16, 0, 0)`; the two handles at `[0, 8)`, `accept(node(2, 0, 0, 2))`): `binMod_fixed_sound`, `binMod_sound` (Hoare proof `bin_sat`, decoding `blob_node`, `seq_node`), `binMod_live` (traced session), `binMod_lang` (exactly `{pair(blob [0xFF], seq [7, 9])}`, no sentinel, no UB). **Against the pure canonical ABI reference loaders** `MemSound.WitAst.Canon` (memory32): `loadVals mem ps ptr` is the payload step of `node` at the call's memory (`witNode_loadVals`: every decoded node's payload is `loadVals` at its payload pointer); for scalar vectors (`SPTy`: `bool`, `s32`, `u32`, `s64`, `u64`) `loadVals_loadRecord` proves `(loadVals mem ps ptr).map toScalarValues = ABI.loadRecord ts mem ptr` (`Reference/ABI/Memory`), an equation of options, so values and failures (misalignment, out of bounds) coincide, with an injective value translation (`toScalarValues_injective`); `readPtrLen_load`: a `(ptr, len)` pair is the two reference `ABI.Scalar.load .u32` loads; `readVal_string_loadStringFromRange`: given its pair, a `string` payload is `ABI.loadStringFromRange? .utf8 .i32` (`Reference/ABI/String`) for `len ≤ ABI.maxStringByteLength` (same text or same failure: bounds, invalid UTF-8), while above the limit the reference traps and the decoder does not check. `SPTy` now covers all nine canonical scalars (`bool`, `s8`…`u64`); single values `loadVal mem t a`: `loadVal_scalar` (`ABI.Scalar.load`), `loadVal_f32`, `loadVal_f64` (`ABI.loadFloat`: NaNs canonicalised), `loadVal_char` (`ABI.loadChar`: surrogates and values `≥ 0x110000` fail in both), equations of options. There is no pure reference list, record-with-non-scalar-fields, variant or flags loader under `Reference/ABI/` (REF `load_list*`, `load_record`, `load_variant`, `load_flags` exist only as the monadic `Canon.Load` programs), so `bytes`, `list t`, fixed lists and the composite types are not compared with a reference loader. **Records, options and chars end to end**: `glyphSig` (`glyph`: one `record { ch: char, size: option<u8> }` (`glyphTy`, eight bytes), arity `fixed 0`; `pair`: no payload, arity `fixed 2`) and `glyphMod` (the record `{ 'a', some(7) }` as one `i64.store` at `[16, 24)` before `node(0, 16, 0, 0)`, the same with `{ 'λ', none }`, the two handles at `[0, 8)`, `accept(node(1, 0, 0, 2))`): `glyphMod_fixed_sound`, `glyphMod_sound` (Hoare proof `glyph_sat`, payloads `readVals_glyphA`, `readVals_glyphB`), `glyphMod_live` (traced session), `glyphMod_lang` (exactly `{pair(glyph { 'a', some(7) }, glyph { 'λ', none })}`, no sentinel, no UB) |
| simple APIs are special cases | done | `Api.sexpW_hom` (writer homomorphism), `sexpLang_eq_astLang`, generic `writerLang_hom`/`writerLang_hom_subset` |
| SExpr ≅ single payload-free variadic branch tag + atom leaves | done | `sexpSig`, `SExp.equivAST : SExp α ≃ {x // WellArity x}`; atoms are not unlabelled internal nodes: `leaf_children_not_wellArity` |

### 5. Cons API and n-ary vs dotted

| Item | Status | Where |
| --- | --- | --- |
| `nil()`, `symbol`/atoms, `cons(i32,i32)`; cons without `nil` | done | `Api.consW` (`SExp2`), `Api.pairW` (`Tree2`), `consW_childRel`. Through memory: `MemSound.Cons` (`consWrite`: `symbol`/`string`/`blob(ptr, len)` atoms from memory, `nil()`, `cons(a, b)`; `consWriterLang` over `SExp2 MemAtom`; generic bridges `rolesFixedLang_subset`, `rolesWriterLang_subset` for any roles and writer); `consMod` (`accept(cons(symbol(0, 2), nil()))`): `consMod_fixed_sound`, `consMod_sound`, `consMod_live`, `consMod_lang` (exactly `{(hi)}`, no sentinel, no UB); mixed atom kinds: `consMix` (`symbol(0, 2)` and `string(0, 2)` over `68 69`, re-stored before each call since hosts may rewrite memory, `nil()`, two `cons`): `consMix_fixed_sound`, `consMix_sound`, `consMix_live`, `consMix_lang` (exactly `{(hi "hi")}`, a symbol and a string atom) |
| n-ary vs `SExp2` (improper lists), properness, roundtrips | done | existing `SExp.toSExp2`, `toSExp2_injective`, `proper_iff_exists`; new `SExp2.toSExp?` with `toSExp?_toSExp2`, `toSExp2_of_toSExp?`, `isProper_iff_toSExp?` |
| tagged AST embeddings | done | existing `TExpr.equivSExp`, `TExpr1.equivTree2`, `TExpr1.equivSExp2`; new `SExp.equivAST` |

### 6. Abstract acceptors

| Item | Status | Where |
| --- | --- | --- |
| union/intersection, images/preimages (incl. `SExp → SExp2`) | done | languages are `Set`s; `Set.image SExp.toSExp2` etc.; homomorphism images `writerLang_hom` |
| combinators `(a₁ a₂)`, `(a₁ … aₙ)`, `star` | done | `pair`, `tuple`, `star`; `mem_pair`, `tuple_inter`, `pair_inter_left`, `pair_union_left`, `tuple_subset_star` |
| patterns over SExpr/SExpr2/AST with acceptors as an extra atom | done | `Pat`, `Pat2`, `PatAST` and their `lang`; `Pat.lang_ground`, `Pat.lang_mono`, `Pat2.lang_ground`, `Pat2.lang_mono`, `Pat2.lang_ofList`, `PatAST.lang_ground`, `PatAST.lang_mono`; `Pat.toPat2` with `Pat.toSExp2_image_lang` (image of a proper pattern's language along `SExp → SExp2`) |
| AST→sexp `(tag arg₁…argₙ child₁…childₙ)`, per-tag layouts, soundness assumptions | done | `AST.encode`, `AST.encodeWith`, `AST.encode_injective` (`ArgLenFixed`), `encode_image_injective`; counterexample `Formats.Examples.enc_collides` |

### 7. Executable Wasm checkers

| Item | Status | Where |
| --- | --- | --- |
| module languages grounded in core Wasm | done (definitions) | `Wasm.Game.HandleAccept`: `playEvents enter decAsk decAns`, `handleTraces` over `(instOf m).strategy P s` plays (every profile, every environment, any export sequence); export-call moves `.inr (.ask _)` decode to `enter` (`some .enter` in every module language: `moduleConsLang`, `moduleSExpLang`, `moduleAstLang`, `moduleTree2Lang`, `Writers.moduleTraces`; `Memory.memTraces` reads `Tag.enter` likewise), so module languages see call boundaries and a trapped call is followed by further export calls on the same store |
| link from Hoare-logic specifications to language soundness | done | `readerLang_subset_of_AG` (generic, every `oa ≠ .ub`), `consLang_sound_of_gameSat`, `consLang_sound_callTrap`, `consLang_sound_of_forall` via `GameLink.strategy_sound`; writers `fixedLang_subset_of_AG`, `writerLang_subset_of_AG` |
| proper lists in `SExp2`, `[i64]` word lists, sorted word lists, subset theorem | done (soundness) | modules `properCheck`, `wordsCheck`, `sortedCheck` (validated by `decide +kernel`); `properCheck_sat`, `wordsCheck_sat`, `sortedCheck_sat` (`GameSat` with store invariant `consInv`, every profile, every environment `ρ`); unconditional `properCheck_sound`, `wordsCheck_sound`, `sortedCheck_sound` (`moduleConsLang P m consIx .trap oa Envs ⊆ L` for every `Envs` and every accept policy `oa ≠ .ub`, in particular the Wasm-facing `callTrap`). `properL` is **spine** properness (`SpineProperList`: nil-terminated `cdr` spine, any elements), which is what `properCheck` checks; recursive properness `recProperL` is strictly smaller (`recProperL_ssubset_properL`, with `dottedElem_mem_properL`/`dottedElem_not_mem_recProperL`); `sortedL_subset_wordsL`, `wordsL_subset_properL` |
| deeper properness | done | depth two: `recProperCheck` (`recProperCheck_sound` ⊆ `nestL`, `wordsL_ssubset_nestL`, `nestL_ssubset_recProperL`); full depth: `recFullCheck` (Wasm recursion; recursive calls proved by a size-indexed specification, `X.callSpec`): `recFullCheck_sat`, `recFullCheck_sound` (⊆ `recProperL`), `recFullCheck_accepts_deep1` (`(((1)))`), `recFullCheck_accepts_nested`, `recFullCheck_separates_deep1` (accepted by `recFullCheck`, rejected by `recProperCheck`). Non-proper inputs make the export trap. **Termination**: `recFullCheck_tsat` (`TGameSat` against `consISpec consIx ρ recProperL`, every profile and every `ρ`: every export call returns or traps; the variant is the number of cons cells of the tree the cursor denotes, finite since `ρ` maps handles to finite trees and correct `car`/`cdr` answers name subtrees; total rules `T.*`, `RT.*`, recursion `RT.self` in `Proofs/…/RecFull/Total.lean`), `recFullCheck_dsound` (the divergence-observing strategy refines `dagStrat`, via `dstrategy_sound`) |
| non-vacuity of the checkers | done | `Checkers.Examples`: replayed instance plays (`Silmaril.Wasm.Resource.Replay`, `replayExport_play`) decoded into reader runs (`mem_consLang_of_replay`; a replay starts with its export call, decoded as `enter`, which the Boolean checks pass), under the call-local trap: `properCheck_accepts_12`, `wordsCheck_accepts_12`, `sortedCheck_accepts_12` (`ofAtoms [1, 2]`), `wordsCheck_accepts_21`, `properCheck_accepts_dottedElem`, for every profile admitting the deterministic interpreter's steps (`hP`) and every specification profile (`_spec`); negative: `sortedCheck_rejects_21`, `wordsCheck_rejects_dottedElem`, `properCheck_rejects_atom`. So `sortedL ⊊ wordsL ⊊ properL` is witnessed by the modules |
| signed `i32` handles vs `i64` payloads, sorting | done (stated) | `Checkers.Defs` docstring; `sortedL` uses signed `BitVec.sle` (`i64.le_s`) |
| other styles in Wasm (proved examples) | done | shared rules `Proofs/Wasm/Game/HandleAccept/Checkers/Generic.lean`. N-ary reader (`count`/`child`): `pairCheck_sound`, `wordsNCheck_sound` (`SExp.ofAtoms ws`), `sortedNCheck_sound`, `sortedNL_subset_wordsNL`. AST reader: `addCheck_sound` (`add(num a, num b)`). Parsing export: `nzParse_sound`/`nzParse_input` (one-shot inputs are single nonzero words; the tree is unconstrained because the export spec cannot constrain its imports). Binary trees (`Tree2`, cons without nil): writer/reader decoders, `combCheck_sound` (right combs of words). Writer: `twoWords_sound`, `twoWords_fixed_sound` (accepts only `(x x+1)`), for policies without a sentinel (the module does not test for failures). Structural bounds for every module: `moduleConsWLang_subset_atoms2`, `moduleSxWLang_subset_arities`, `moduleAstWLang_wellArity`, `moduleParseRel_input_oneShot`, `memWriterLang_subset_atoms` |
| sentinel writers `0` and `-1` | done | `twoWordsZ`, `twoWordsM` test each write result against the sentinel: `twoWordsZ_sat`/`twoWordsM_sat`, `twoWordsZ_sound`/`twoWordsM_sound` (store semantics, `pol.sentinel = some 0` resp. `some (-1)`), fixed-environment versions, `twoWordsZ_accepts_0/_5`, `twoWordsM_accepts_0/_5` (handle `0` valid under sentinel `-1`), failure replays `twoWordsZ_fail_accepts_nothing`, `twoWordsM_fail_accepts_nothing`, `twoWordsZ_lateFail_accepts_nothing` |
| family × API audit | done | `HandleAccept.Families`: 10 families × 5 APIs as named instantiations (table in `Families/Defs.lean`, every row names its Wasm theorems). `Families.Matrix`: for every pair a core Wasm module over the family's own atom type with a Hoare-logic language bound (`_sound`) and a traced session accepting a tree (`_live`): n-ary writer `pairAtomMod` (exactly `(a b)`; words `wordMod`, exactly `42`), cons writer `consAtomMod` (exactly `(a)`; words `twoWords`), AST writer the n-ary module read at `sexpSig` (`tabAstWriterLang_eq`), n-ary/cons/AST readers `probeMod` (`firstAtoms`, `carAtoms`, `firstLeaves`). No pair is left without a module |
| non-vacuity of the other styles | done | generic replay decoding `Proofs/Wasm/Game/HandleAccept/Replay.lean` (`mem_readerLang_of_replay`, `mem_writerLang_of_replay`); `pairCheck_accepts_12`, `wordsNCheck_accepts_12`, `sortedNCheck_accepts_12`, `wordsNCheck_accepts_21`, `sortedNCheck_rejects_21`; `addCheck_accepts_12`; `combCheck_accepts_123`; `twoWords_accepts_0`, `twoWords_accepts_5` (fresh-handle host); `nzParse_relates_7` (needs `replayExportR`, which also records the export's answer). All for profiles admitting the deterministic interpreter's steps (`hP`) and every specification profile (`_spec`) |

### 8. Combined writer + reader

| Item | Status | Where |
| --- | --- | --- |
| successful writes agree with any future read; persistent immutable meanings; interning | done | `CEv`, `combined`, `combined_cut`, `combined_write`, `combined_read`, `combined_write_read`, `Reader.Mono.persist`; monotone readers `sexpR_mono`, `consR_mono`, `astR_mono` |
| all reader invalidity and writer failure policies | done | `CStep` reuses `WStep` and `answers` (every `OnBadRead`) |

### 9. Parsing variants

| Item | Status | Where |
| --- | --- | --- |
| a. `parse(data) -> i32`, sentinel failure | done | `PEv.parse`, `resolve`, `oneShotRel` |
| b. `append(data)`, `done() -> i32` | done | `PEv.append/done`, `parseRel_done`, `pending`, `doneClears` |
| c. chunks, `done() -> (used, tree)`, cursor, failure advances, unconsumed suffix, bounds | done | `PEv.feed/finish`, `Returns`, `run_cursor`, `parseRel_slice` (for the session-abort overrun policy `onOverrun = .sessionTrap`), `onOverrun`, `usedOfI32`/`usedOfI32_lt`, `Examples.chunk_example`, and for every overrun policy without UB (incl. call-local) `run_cursor_eff`, `parseRel_slice_eff` (`effConsumed` counts only answered `finish` calls; `effConsumed_eq_consumed` under session abort) |
| invalid returned handle, overrun: traps | done | every parsing event is itself an export call ending with its returned handle, so a call-local trap (`callTrap`, the default) is that call relating nothing while the session continues; it coincides with `ignore` (`PStep.retBadIgnore`, `PStep.overrunIgnore`). `sessionTrap` aborts the session (`PStep.retBadSessionTrap`, `dead`; an overrun has no answer) |
| repeated `done`, sessions, `reset` | done | `doneClears`, `PEv.reset`, `Examples.done_twice` |
| projections, membership, monotonicity, unions, non-preservation of intersections | done | `inputLang`, `treeLang`, `inputLang_union`, `inputLang_inter_subset`, `parseRel_mono`, `parseRel_union`, `Examples.projection_inter_strict` |
| trees resolved in consistent environments; mixed APIs with parsing; Wasm tie-ins | done (one-shot `parse` in Wasm) | `Semantics.Accept.Mixed`: `mixedRel` resolves returned handles in the **current writer store** (`run_resolve_stable`, `mixedRel_constructed`), `mixedFixedRel` over fixed environments, `mixedRel_subset_parseRel`, `mixedRel_subset_of_AG`; Wasm `HandleAccept.Mixed`: `moduleMixedRel`, `moduleMixedRel_sound_of_gameSat` (writer import answers agree with ρ, export spec constrains the returned tree); example `listParse`: `listParse_sound`/`listParse_rel` (every related pair is `([x], (x))`, `x ≠ 0`), non-vacuous `listParse_relates_7`, `listParse_rel_eq_7`. Streaming: ghost-state export specifications (`SSpec`, `SGameSat`, `strategy_sag`, `moduleMixedRel_sound_of_streamSat`, semantic `mixedRel_subset_of_streamAG`); example `stackParse` (`append(x)`/`done()`): `stackParse_sound`, `stackParse_rel` (every pair is `(vs, ofAtoms vs.reverse)`), `stackParse_relates_78`, `stackParse_rel_eq_78` (replayed session of three export calls). Requires no writer sentinel and `doneClears`. Chunk exports (`feed`/`finish -> (used, tree)`): `Mixed.Chunk`, `chunkSSpec` (ghost = chunk buffer), `moduleMixedRel_sound_of_chunkSat` (with the semantic `Semantics.Accept.Mixed.Chunk`: `chunkStep`, `chunkFold`, `pstep_buf`, `mixedRel_subset_of_chunkAG`, `mixedFixedRel_subset_of_chunkAG`, assume/guarantee along the chunk buffer), over fixed environments `moduleMixedFixedRel_sound_of_chunkSat` (every writer policy), `chunkStack_fixed_sound`; example `chunkStack` (`feed(x : i64)`, `finish(n) -> (used, tree)`, all-or-nothing consumption): `chunkStack_sat`, `chunkStack_sound`, `chunkStack_relates_78`, `chunkStack_relates_nil`, `chunkStack_rel_eq_78` (replayed `feed(7) feed(8) finish(1) finish(5)`: the values stay buffered across a `finish` that consumes none). Partial consumption: `Mixed.Chunk.Take`, `chunkTake` (two `i64` slots and a count in globals; `finish(n)` consumes exactly the oldest `n` when `0 < n ≤` count and returns their list, otherwise `(0, ())`): `chunkTake_sat`, `chunkTake_sound`, `chunkTake_fixed_sound`, `chunkTake_rel` (every pair is `(vs, ofAtoms vs)`), replayed `feed(7) feed(8) finish(1) finish(1)`: `chunkTake_relates_7` (`used = 1` of `2` buffered), `chunkTake_relates_8` (the value left buffered), `chunkTake_rel_eq_8`. Memory buffer: `Mixed.Chunk.Ring`, `chunkRingN cap` (a ring buffer of up to `cap` `i64`s in linear memory, start slot and count in globals, slots `8 * ((st + i) mod cap)`; `feed` diverges when the buffer is full; `finish(n)` builds the list of the oldest `n` values in a loop and advances the start slot, consuming exactly `n` when `0 < n ≤` count, otherwise `(0, ())`; `chunkRing = chunkRingN 8`), with **one proof generic in the capacity** for every `RingCap cap` (`0 < cap ≤ 8192`, the buffer within the one page): `chunkRingN_sat` (invariant `ringInv cap`: the memory loads at `slot cap st i` are the chunk buffer; the instance shape, code, globals and memory are kernel evaluations with `cap` free, `kernel_rfl`, `MShape.of_okNB`; slot arithmetic with `cap` symbolic, `slot_addr`, `slot_ne`), `chunkRingN_sound`, `chunkRingN_fixed_sound`, `chunkRingN_rel` (every pair is `(vs, ofAtoms vs)`), restated for eight slots as `chunkRing_sat`, `chunkRing_sound`, `chunkRing_fixed_sound`, `chunkRing_rel`; non-vacuity for every `2 ≤ cap ≤ 8192` at once: `chunkRingN_relates_7`, `chunkRingN_relates_8`, `chunkRingN_rel_eq_8` (`feed(7) feed(8) finish(1) finish(1)`: the second `finish` consumes the value left in memory), instances `chunkRing_relates_7`, `chunkRing_relates_8`, `chunkRing_rel_eq_8` (eight slots) and `chunkRing8192_relates_8`, `chunkRing8192_rel_eq_8` (the whole page); one value for every `1 ≤ cap ≤ 8192`: `chunkRingN_relates_7_one` (`feed(7) finish(1)`, `RingLive.ring_session1`), with the one-slot buffer `chunkRing1_relates_7`, `chunkRing1_rel_eq_7`; for **every profile**, by a play built forwards (`RingLive.ring_session`): the kernel replay used for `chunkTake` does not scale to a 64 KiB page, so the runs between callouts are composed from Core `Step` rules with the store symbolic (straight-line code by `exec_sound`, memory by `load_store_same`/`load_store_disjoint`, slot addresses from `cap` by `mod_small`), and only the decoded moves are checked by kernel evaluation (`mem_moduleMixedRel_of_path`) |

### Cautions

| Caution | Where |
| --- | --- |
| explicitly quantified environments | `Envs` parameters, `fix`, `langOver` |
| restriction vs nondeterminism vs trap vs UB top | `Sim`, `Phase.dead`, `Phase.chaos` |
| well-founded fixed environments, no silent cycles | `NodeEnv`, `UnfoldN`/`Unfold`, `not_unfold_of_cycle`, `realize_realizes`, `Examples.cycle_unfolds_to_nothing` |
| sentinel inclusion via observations/renamings, allocation failure | `writerLang_rename`, `writerLang_sentinel_swap`, `writerLang_noRet_subset`, `sentinel_twice` |
| intersection is not preserved by projection or trace languages | `Host.lang_inter_subset`, `inputLang_inter_subset`, `Examples.inter_strict`, `projection_inter_strict` |

## Modelling choices to review

* **Traps are call-local.** The Wasm-facing mandatory trap on an invalid `accept` is
  `OnInvalid.callTrap` (the default): as in Wasm, a trap aborts only the current export
  invocation, while the instance and its store persist (the game strategy
  `ScalarInstance.strategy` keeps the store across export calls) and the environment may make
  arbitrary further export calls. The environment moves to `aborted`; only the next export call
  (`enter`) may follow and resumes `live` with the store unchanged (`WStep.aborted_inv`).
  Effects before the trap are not rolled back: successful writes stay allocated
  (`write_persists`, `Run.store_extends`, `Examples.persist_seven`).
* Aborting the whole session (`OnInvalid.sessionTrap`, phase `dead`) is an optional stricter
  policy. Ranks `sessionTrap ≤ callTrap ≤ ignore ≤ ub` order the languages
  (`writerLang_sessionTrap_subset_callTrap`, `writerLang_callTrap_subset_ignore`,
  `writerLang_ignore_subset_ub` and the reader analogues), both inclusions around `callTrap` are
  strict (`Examples.callTrap_ne_sessionTrap`, `Examples.callTrap_ne_ignore`), and within one
  export call the two traps agree (`writerLang_callTrap_eq_sessionTrap`,
  `readerLang_callTrap_eq_sessionTrap`). Reader soundness (`readerLang_trap_subset`, the
  checker theorems `*_sound`) holds for every accept policy but `ub`.
* Parsing exports are themselves the export calls: a trapped `parse`/`done` relates nothing and
  the session continues (`callTrap` coincides with `ignore` there); the cursor theorems assume
  the session-abort overrun policy.
* Allocation failure with a sentinel is always allowed (capacity is the environment's); without
  a sentinel a failing allocation traps.
* `SExp2.toSExp?` is defined by classical choice (the unique preimage); a computable decoder is
  not provided.
* The Wasm reading uses instance plays (`Verify.instOf`, every profile), which carry argument
  values and results but not memory.

## Remaining obligations

* Memory ASTs: `MemSound.WitAst` has the canonical ABI layout (`layout_toWit`,
  `valsLayout_toWit`), and its decoding is proved equal to the **pure** reference loaders only
  for scalar payload vectors
  (`loadVals_loadRecord` against `ABI.loadRecord`) and for UTF-8 strings of at most
  `MAX_STRING_BYTE_LENGTH` bytes (`readPtrLen_load`, `readVal_string_loadStringFromRange` against
  `ABI.loadStringFromRange?`), failures included. Not proved: `bytes` and `list t` against any
  reference (the repository has no pure list loader; REF `load_list*` exist only as monadic
  `Canon.Load` programs), mixed vectors as one record equation (`loadRecord` has only scalar
  fields), and any equation with the monadic `Canon.load` programs over a component store. The
  legacy memory decoder checks bounds but not `MAX_STRING_BYTE_LENGTH`/`MAX_LIST_BYTE_LENGTH`.
  The checked host boundary (`MemSound.WitAst.Checked.Thms`) applies both limits to payload
  indirections and the list limit to child handles. It explicitly rejects flat arguments,
  non-UTF-8 encodings, memory64, and asynchronous calls. This is not a proof of interoperability
  with canonical component-ABI lifting. Floats, `char` and single scalars agree with the pure
  reference loaders (`loadVal_f32`, `loadVal_f64`, `loadVal_char`, `loadVal_scalar`); lists,
  fixed lists, records with non-scalar fields, tuples, variants, enums, options, results and
  flags follow the reference layout (`layout_toWit`) and trap conditions (discriminant range,
  Unicode scalar values, NaN canonicalisation, ignored high flag bits) but are compared with no
  reference loader (none is pure). The end-to-end modules cover `s64`, `string`, `bytes`,
  `list<u32>` and a `record { char, option<u8> }`; nested lists, variants, enums, results,
  flags, fixed lists and floats are covered by kernel-checked decoding examples only.
  **Resource handles** (`MemSound.WitAst.Own`): `own<r>` payloads follow the resource-table
  semantics (the tree holds the representation from an explicit table; the move consumes the
  handle; trace- and table-dependence proved), but only **top-level** `own` fields of a payload
  vector are resolved. The checked boundary rejects the entire selected schema for nested
  `own`, stored `borrow` and unsupported WIT kinds, even in inactive cases and empty lists.
  Its typed diagnostics also distinguish unknown, dead, wrong-type and repeated handles.
  Rejection leaves the caller's resource table and Core store in place, including earlier
  effects; it traps this call, not the whole session. The legacy trace projection omits failed
  decodes, and is not itself a checked host contract. The checked boundary does not yet have
  the legacy trace language's whole-module bridge. Handle **creation** is not modelled (the table
  is the initial environment `rt₀`, e.g.
  handles received earlier; no `resource.new`/`new_res` import), nor `resource.drop` or `rep` of
  the module's own resources, and the stateful host is not compared with the reference machine's
  `Table` (`Silmaril.Wasm.Resource.Table`); the end-to-end examples move one handle (`ownMod`) and
  one handle twice (`twiceMod`, a trace-level negative: its whole language is not computed).
  `borrow` is rejected in stored trees by design. **Not payloads**: `future`, `stream`,
  `error-context` (pending async semantics); `map` is not a separate payload type (WIT
  despecialises it to `list<tuple<k, v>>`). The flat (core-argument) decoder `Ast.ofVal?` still reads only `bool`,
  `s32`, `u32`, `s64`, `u64`.
* Wasm writer variants: `batchAccept_lang` bounds `batchAccept` by its kept batch `keptL` (the
  dropped word is never accepted, `batchAccept_drops`), but the lower bound is the run at the
  fixed argument `3` (`batchAccept_kept`), not every `(w)`; the batch bridge assumes policies
  without undefined behaviour. `errAccept`, `allAccept`, `readBack` are upper bounds with runs at
  fixed arguments, not exact languages.
* Families through memory: `MemSound.ListCheck` checks lists of exactly two symbols
  (`symListMod`) or two blobs (`blobListMod`); there is no looped checker for any length (a loop
  computing `ptr + 4i` with `i32` arithmetic wraps modulo `2^32` while the decoder reads at the
  natural-number offset, so it needs an overflow guard), and the live sessions exhibit lists of
  two copies of one symbol (blob) only.
* Parsing: `chunkRingN` is proved for capacities up to 8192 (one page), with non-vacuity for
  every `1 ≤ cap ≤ 8192` (one value: `chunkRingN_relates_7_one`; the one-slot buffer:
  `chunkRing1_relates_7`, `chunkRing1_rel_eq_7`) and for `2 ≤ cap` with two values; capacities
  beyond one page and memory growth (`memory.grow`) are not done.

## Checking

```
lake build --wfail Silmaril.Semantics.Accept.Handle.Examples Silmaril.Semantics.Accept.Parse.Examples \
  Silmaril.Formats.SExp.Api.Thms Silmaril.Formats.SExp.Pattern.Examples \
  Silmaril.Formats.SExp.Family.Thms Silmaril.Wasm.Game.HandleAccept.Checkers.Thms \
  Silmaril.Semantics.Accept.Mixed.Chunk.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.Thms \
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take.Examples Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Examples \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Canon Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Exact.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.KwText.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms \
  Silmaril.Wasm.Game.HandleAccept.Checkers.RecFull.Thms \
  Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch.Examples Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Probe.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.Tab.Thms \
  Silmaril.Wasm.Game.HandleAccept.Families.Matrix
scripts/check-layout.sh
```

`make check` builds everything; a library-only build does not run the executable tests.
