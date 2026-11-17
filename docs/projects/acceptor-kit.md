# The acceptor kit

A certificate-checking acceptor is a Wasm component whose exports take a problem and a
certificate as canonical-ABI lists and answer `bool`. The SAT, LRAT and Farkas acceptors
(`Silmaril.Wasm.Examples.{SatAccept,LratAccept,FarkasAccept}`) are verified end to end against
the reference Component Model: an accepting call means that the problem is in the checker's
language. Everything that does not depend on the checking algorithm is in one shared topic,
`Silmaril.Wasm.Acceptor` (headers `Silmaril/Wasm/Acceptor/*/{Defs,Thms}.lean`, proofs in
`Silmaril/Proofs/Wasm/Acceptor/`), and the generic byte linkage is in
`Silmaril.Project.WasmComponents.Acceptor`. This page describes the layers, what is generic and
what each checker supplies, and how to add the next checker.

## The layers

| Layer | Header | What it gives |
|---|---|---|
| Allocator | `Silmaril.Wasm.Acceptor.Alloc` | `reallocFunc ty g N`: `cabi_realloc` as a Lean Wasm AST function, its heap pointer global `g`, its memory size `N`; `realloc_sound` (every returning run answers one value and only sets the heap pointer, `ReallocOk N`); `BumpSpec` and `BumpSpec.bumpAlloc` (a bump allocator on a global gives `ListLift.BumpAlloc` for any memory index) |
| Code and instance facts | `Silmaril.Wasm.Acceptor.Code` | `fnOk`, `fn_of_fnOk` (one kernel check gives, per function, its code, module instance and type); `ibeq`/`ibeqs` with `ibeqs_sound`; `callf`; the call rules `w_call`, `w_callVoid`, `w_callI32` of the every-run logic |
| ABI read contracts | `Silmaril.Wasm.Acceptor.Abi` | readers `listAt`, `pairAt`, `read2`, bounds `ListIn`, `PairIn`; the contract `Reads t enc rd inn` (`Holds` implies the reader returns the value and the bounds hold) with `reads_s32`, `reads_u32`, `reads_s64`, `Reads.list`, `Reads.tuple2`, `Reads.record2`, `Reads.map`, `Reads.mono`, `reads_words`; `holdsL_listAt`, `flatHolds_two`, `flatHolds_read2`; the shared `list<list<s32>>` reader `nestedAt`, `NestedIn`; `checkList_map` for typing |
| Bridge | `Silmaril.Wasm.Acceptor.Bridge` | `Kit c` (instance, `Good`, `Inst`, bump allocator, invariant, initial heap pointer), `CheckerExport c α β` (export, encoding of problem and certificate, typing, `Goal`), the Core obligation `CheckerExport.CoreSound`; `CheckerExport.sound`, `sound_accepts`, `sound_lang`; rejection: `CheckerExport.rejects`, `rejects_none` |
| Emission and bytes | `Silmaril.Wasm.Acceptor.Emit` | `coreBytesOf m`, `compBytes c core`; `decode_coreBytesOf`, `parse_compBytes` from the kernel evaluations of the encoders and the decoder |
| Byte linkage | `Silmaril.Project.WasmComponents.Acceptor` | `toRef_toAst`: for **every** `ListComp`, `toRef? (c.toAst core) = some c.toRef` when `decode? core = some c.mod` (proved once, not by evaluation); `toRef_of_parse`; `CheckerExport.sound_of_bytes` |

The layers rest on the list-lifting fragment of the reference Component Model,
`Silmaril.Wasm.Component.Reference.ListLift` (`ListComp`, `LTy`, `acceptSound`) and its bump
allocator results `ListLift.Bump` (`BumpAlloc`, `params_holds`, `Holds`, `FlatHolds`).

### The generic statements

* `Acceptor.realloc_sound`: for a function instance at address `a` with code
  `reallocFunc ty g N`, `N < 2³²`, module instance mapping global `g` to the address `ga` that
  holds the `i32` heap pointer `top ≤ N`, every returning `$invoke` run on
  `(old, osz, al, nsz)` answers `[i32 r]`, leaves `s.setGlobal ga (i32 t')` and satisfies
  `ReallocOk N top al nsz r t'` (bump, never lower, within `N`, or failure at `N`).
* `BumpSpec.bumpAlloc : BumpSpec P ra ga N Inv → (size of memory ma is N under Inv) →
  (writes to ma keep Inv) → BumpAlloc P ra ma N Inv`.
* `Reads t enc rd inn := ∀ B lo hi a p, Holds B lo hi t (enc a) p → rd B p = a ∧ inn B p`, and
  `flatHolds_read2 : Reads t₁ e₁ r₁ i₁ → Reads t₂ e₂ r₂ i₂ → FlatHolds B lo hi [.list t₁, .list t₂]
  [.list (xs.map e₁), .list (ys.map e₂)] fl → ∃ q₁ q₂, fl = [q₁, |xs|, q₂, |ys|] ∧ … ∧
  ListIn t₁.size i₁ B q₁ |xs| ∧ listAt t₁.size r₁ B q₁ |xs| = xs ∧ (the same for ys)`.
* `CheckerExport.CoreSound K e := ∀ P p q s t fl s' f' r, K.Inv s t → FlatHolds (memBytesOf s
  c.memIdx) K.base t (e.x.params.map (·.2)) (e.enc p q) fl → Steps P noHost (invoke s
  (c.coreAddr K.I e.x.core) fl) ⟨s', f', vals [i32 r]⟩ → r ≠ 0 → e.Goal p q`.
* `CheckerExport.sound K e (hc : e.CoreSound K) P prof p q : returns (some [bool true]) ∈
  exportBehaviours prof (refHost P) () c.toRef [] e.x.name ((e.enc p q).map LVal.toRef) →
  e.Goal p q`; with `hg : Goal p q → chk p q = true` and `hL : Accepts chk ⊆ L`,
  `sound_lang` gives `p ∈ L`.
* `CheckerExport.rejects K e hc (hg : ∀ p q, Goal p q → R p q) P prof (hn : ¬ R p q) :
  returns (some [bool true]) ∉ exportBehaviours prof (refHost P) () c.toRef [] e.x.name …`;
  `rejects_none` is the case `R p q := D (f p q) ≠ none` for a decoder `D` of the problem or the
  certificate. "Rejected" means only this: no reference behaviour returns `true`; that the call
  returns `false` (rather than trapping or diverging) is not claimed.
* `Acceptor.toRef_toAst c (h : decode? core = some c.mod) : toRef? (c.toAst core) = some c.toRef`.

## Generic versus checker-specific

Generic (proved once, in the kit): the allocator code and its proof; the bump-allocator
instance from the allocator's run; the read-back of canonical-ABI values for every type the
fragment lowers (scalars, lists, nested lists, two-field tuples and records, through any
bijection with a Lean type); the composition `acceptSound` + `params_holds` + Core obligation;
the call rules and the instance-fact reading; the byte encoders' round trip and the reference
reading of every emitted `ListComp`.

Checker-specific (in each example):

* the Lean carrier and checker (`Silmaril.Logic.SAT.Carrier`, `Silmaril.Logic.LinArith.Carrier`):
  problem and certificate types, `chk`, its soundness `Accepts chk ⊆ L`;
* the core module: the verified checker (`LRAT.lratModule`, `Farkas.farkasMod`, the SAT checks)
  and the driver that reads the arguments from the ABI memory and feeds the checker, with its
  Core soundness theorem (`check_sound`, `checkStream_sound`, `stream_returns`, …). This is the
  algorithmic proof: the LRAT and Farkas drivers are proved with fixtures of their checkers
  (`LRAT.Fix`, `Farkas.Fix`), the SAT checks with the verification-condition generator;
* the store invariant of the acceptor (`AccStore`, `SInv`), with the heap pointer, and the facts
  that make the allocator a `BumpSpec` on it (the global layout, `set`);
* the kernel facts of the instance (`acc_fnOk`, `t_coreAddrs`, `t_exports`, …) and the three
  byte evaluations;
* the readers in the shape the core theorems use (`systemAt`, `wordsAt64`, `nestedAt`) as
  instances of the kit's (`rfl`), and the Core obligation of each export.

What is deliberately not generic: memory layouts and sizes (each module chooses its memory
index, size, heap base and global index; the kit's proofs take them as parameters), the Core
drivers themselves (their loops differ per checker) and the readers' composite shapes beyond
two fields (add a combinator when a checker needs one).

## Adding a checker

1. **Carrier.** A Lean problem type, certificate type and checker `chk : α → β → Bool` in a
   `Logic` carrier, with `Accepts chk ⊆ L` for its language. Give decoders from the WIT values
   if the problem is not a list of scalars.
2. **Core module.** Extend the verified checker module with a memory for the ABI, a heap pointer
   global and `Silmaril.Wasm.Acceptor.reallocFunc ty g N` (no hand-written allocator), and a
   driver export that reads the arguments (`(ptr, len)` pairs) and calls the checker. Prove the
   driver's Core soundness: from a store of the acceptor with the arguments in bounds, a nonzero
   answer implies the goal (`chk p c = true`, or `p ∈ L` when the Wasm checker is stricter than
   `chk`). Use `fnOk`/`fn_of_fnOk` for the instance facts and `w_callVoid`/`w_callI32` for the
   calls into the checker.
3. **The `ListComp` value.** `mod`, `memName`, `memIdx`, `reallocName`, the exports with their
   `LTy` parameters (records need a type name). `bytes := compBytes c (coreBytesOf prog)`.
4. **Instance facts.** `c.Good`, `c.Inst I` and `coreAddr` by kernel evaluation (`decide +kernel`),
   as in `Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.Inst`.
5. **Bump allocator.** A store invariant `Inv s t`, `BumpSpec P ra ga N Inv` from
   `Acceptor.realloc_sound` (plus `set`), and `BumpSpec.bumpAlloc` with the memory's size and
   write facts.
6. **Readers.** Compose `Reads` for the parameter types (`Reads.list`, `Reads.tuple2`,
   `Reads.record2`, `Reads.map`); state the checker's readers as instances (`rfl`).
7. **Kit and exports.** A `Kit c` and one `CheckerExport` per export; prove `CoreSound` from
   `flatHolds_read2` and the Core theorem; the headline theorem is
   `CheckerExport.sound` (or `sound_lang`).
8. **Bytes.** Three kernel evaluations (`encodeModule?`, `decode?`, component `encode`), then
   `decode_coreBytesOf`, `parse_compBytes`; in `Project/WasmComponents/<Name>/Thms.lean`,
   `toRef_toAst := Acceptor.toRef_toAst c decode_coreBytes` and the `*_sound_of_bytes`
   theorems (or `CheckerExport.sound_of_bytes`).
9. **Artifacts.** Write the bytes to `examples/wasm-acceptors/<name>.wasm` by regeneration,
   register the file in `silmaril/artifacts.toml` (`sil project artifacts add`, then `sil project
   lock`; `examples/project/registry-check.sh` must pass), add a Wasmtime suite
   `tools/wasm-acceptor-harness/suites/<name>.json` with the file's SHA-256 pinned, regenerate the
   report (`make acceptor-report`) and add the artifact to the explorer's acceptor table
   (`tools/silmaril-project/src/project/explore/views/acceptors.js`). See
   [accepted inputs](accepted-inputs.md) for the harness and the explorer.

## Where the three checkers stand

| Checker | Exports | Goal of an accepting call | Core theorem used |
|---|---|---|---|
| SAT | `check-stream`, `check-nested` | `satStream xs ms = true`, `satNested p ms = true` (agrees with the Lean checker) | `stream_returns`, `nested_returns` |
| LRAT | `check-stream`, `check-nested` | `xs ∈ UnsatStream ∧ (LratStream.decode cs).isSome`, `p ∈ UnsatNested ∧ (LratStream.decode cs).isSome` | `checkStream_sound`, `checkNested_sound` |
| Farkas | `check` | `S ∈ Infeasible ∧ y.length = S.length` | `check_sound` |

The LRAT and Farkas Wasm checkers do not agree with the Lean reference checkers (`lratStream`,
`lratNested`, `farkasCheck`) on every input: the Farkas checker rejects valid certificates
outside its bounds, and the LRAT checker needs no empty-clause step on a problem with an empty
input clause. Their `Goal` is therefore language membership, from their own Core proofs, together
with what the driver checks of the certificate: for LRAT that the certificate words decode
under the flat LRAT stream format v1 (the driver's certificate loop runs the parser automaton
`LratAccept.certRun`, and answers nonzero only in its state `0`; `decode_of_certRun`), for Farkas
that there is one multiplier per inequality.

**Rejection.** With `CheckerExport.rejects`, each `Goal` gives rejection theorems (no reference
behaviour returns `true`): malformed problems for SAT and LRAT (`decodeStream`/`decodeNested`
`= none`), malformed LRAT certificates (`LratStream.decode cs = none`), Farkas multiplier lists
of the wrong length, and SAT models that are not consistent sets of literal words or miss a
clause. See [accepted inputs](accepted-inputs.md#acceptor-components-runtime-observations-and-theorems)
for the list and for what is not proved (well-formed inputs beyond a checker's bounds, and
termination).

The current status of the SAT, LRAT and Farkas exports, proved and tested, is in the
[acceptance checklist](acceptor-checklist.md).
