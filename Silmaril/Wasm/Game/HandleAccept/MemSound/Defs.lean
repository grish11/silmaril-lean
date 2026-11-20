module

public import Silmaril.Wasm.Game.HandleAccept.Memory.Defs
public import Silmaril.Wasm.Logic.GameLink.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs

/-!
# Memory-observing soundness: program-logic contracts for traced sessions

`Silmaril.Wasm.Game.HandleAccept.Memory` decodes memory-carrying writer imports
(`symbol(ptr, len)`, `sexp(ptr, len)`, …) from the **traced sessions** of
`Silmaril.Wasm.Game.IOAccept` (`TSession`): a callout carries the bytes of the instance's
memory at the call, a host answer the raw result and the bytes of the memory after it. This
topic connects those sessions to the every-run program logic (`Silmaril.Wasm.Logic.Hoare`), so
that memory facts proved by Hoare logic about a module's code become facts about the decoded
events.

## Contracts

A `MemContract I` over decoded input events `I` has three parts:

* `pre o`: the **guarantee** of the module at every call of an import, a predicate on the
  callout `o` (`Callout`: the import's name, the raw arguments and the bytes of the memory at
  the call). For example "a call of `symbol` passes a segment holding the UTF-8 text `hi`".
* `ans x`: the **assumption** on every event `x` decoded at a host answer
  (`Roles.answerIn`), for example "a write returns a handle denoting the tree it built in the
  fixed environment `ρ`".
* `reply e a`: what a host reply may be, on the raw call `e : UCall Nat` (host code, caller's
  store, arguments) and the raw reply `a : UReply` (new store, result): typically a store frame
  ("the code is unchanged; memory contents may be rewritten") and the shape of the returned
  values (the import's result type). The admitted environments are `ReplyEnvs reply`.

`memCtx m memAddr R K` turns a contract into a specification context of the program logic
(`Silmaril.Wasm.Logic.Hoare.Ctx`), indexed by host code (`.host k` is import `k` of the
instance, as in `IsSpecInstance`): import `k` (named `(i.moduleName, i.name)`) is called in the
store `s` with `args` when `K.pre` holds of the callout `⟨name, args, memOf memAddr s⟩` read in
that store; it returns, in a store `s'`, an outcome `resultOutcome r` with
`K.reply ⟨k, s, args⟩ ⟨s', r⟩`, such that every event `x` that `R.answerIn` decodes from the
reply `⟨r, memOf memAddr s'⟩` meets `K.ans`. `memHost` is the most general environment meeting
it (`Open.specHost`).

## The Hoare-logic obligation

`MemSat P m memIdx R K Inv`: for the (unique) specification instance of `m` (`IsSpecInstance`),
with `memAddr` the address of its memory `memIdx`,

* the instantiation configuration `c₀` is safe under `memHost` and, if it returns, returns in a
  store meeting the invariant `Inv` (`instPost`);
* every export address `a` meets `exportSpec Inv a` under `memHost`: from a store meeting `Inv`
  and arguments `$invoke` accepts (`InvokeOk`), every outcome ends in a store meeting `Inv`.

This is partial correctness in the every-run logic (`FSpecValid`); `Safe` forbids getting
stuck, and a host call whose precondition fails has no outcome under `memHost`, so a proof of
`MemSat` proves `K.pre` at every reachable call.

## Writer and reader instances

* `writerContract ix sent ρ L reply`: the memory-carrying writer API of `Memory.memRoles` in
  the fixed environment `ρ`: `accept(h)` names a handle whose meaning in `ρ`, if any, is in
  `L`; every decoded write returns the sentinel `sent` or a handle denoting in `ρ` the tree it
  builds in `ρ` (as `Writers.writerISpec`).
* `closedContract ix S reply`: a write-only guarantee: every write the call decodes to (for
  every reply) is closed in `S` (`Writers.WriteClosed`).
* **A memory-returning reader** (`ReadImports`, `memReadRoles`): `items(h, retptr)` returns a
  `list<i32>` through a return pointer, canonical-ABI style: the host writes `(ptr, len)` at
  `retptr` (two little-endian `i32`s) and the `len` child handles at `ptr` (little-endian),
  read off the memory **after** the answer (`HostReply.mem`). The decoded event is
  `read (items h) (items hs)`; a reply the decoder cannot read (out of bounds, no memory) is the
  ill-typed answer `handle 0`, never a correct answer of `items` (`sexpR`), so under the
  trapping read policy such a session is discarded. `accept(h)` is decoded at the call.
  `memReaderLang` is the reader language (`Silmaril.Accept.Handle.readerLang`, reader `sexpR`)
  of those traces, export invocations read as `REv.enter`; `readerContract ρ L reply` asks
  correct reads in `ρ` and accepts of members of `L`.

## Scope

* **Admitted hosts.** The examples admit `ReplyEnvs (ShapedReply shape)`: any environment
  (stateful, nondeterministic, possibly diverging) whose answers keep the store's functions and
  number of memories (`KeepsCode`), may rewrite every memory's contents, and return values of
  the import's result shape (or trap, or throw). This is not `UEnvOk`: it does not ask for typed
  stores, and it excludes answers that add functions to the store, which `Extend` allows.
* **No memory input at export calls.** `TSession.invoke` runs `$invoke` in the store the last
  run ended in, and `Roles.entry` observes only the export address and the raw arguments: the
  environment does not write the module's memory between export calls. An export
  `feed(ptr, len)` whose bytes the embedder writes into the module's memory before calling it
  (the canonical-ABI lowering of `list<u8>` arguments: `cabi_realloc`, then a host write) has no
  counterpart: the bytes at `[ptr, ptr + len)` at entry are the module's own (its code, or an
  earlier host answer). Input chunks enter memory only through host answers, observed by
  `answerIn` on the memory after the answer, as `items` does (a pull-style `read(buf, cap)`
  import would be decoded the same way).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec FSpecValid Safe)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Strategy (resultOutcome)

/-! ## Contracts -/

/-- **A contract of a module's imports**, over decoded input events `I`: the module's guarantee
at each call, the assumption on each event decoded at a host answer, and the admitted host
replies. -/
structure MemContract (I : Type) where
  /-- The guarantee at a call: a predicate on the callout (memory at the call). -/
  pre : Callout → Prop
  /-- The assumption on an event decoded at a host answer. -/
  ans : I → Prop := fun _ => True
  /-- What a host answer may be: a predicate on the raw call (host code, caller's store,
  arguments) and the raw reply (new store, result). -/
  reply : UCall Nat → UReply → Prop

/-- The callout of import `i` called in the store `s` with `args`. -/
def calloutIn (i : Import) (memAddr : Option Nat) (s : Store Nat) (args : List Val) : Callout :=
  ⟨(i.moduleName, i.name), args, memOf memAddr s⟩

variable {X I O C : Type}

/-- **The specification of import `i`** (host code `k`) under a contract. -/
def importSpec (k : Nat) (i : Import) (memAddr : Option Nat) (R : Roles X I O C)
    (K : MemContract I) : FSpec Nat where
  pre s args := K.pre (calloutIn i memAddr s args)
  post s args s' o := ∃ r, resultOutcome r = o ∧ K.reply ⟨k, s, args⟩ ⟨s', r⟩ ∧ ∀ x,
    R.answerIn (calloutIn i memAddr s args) ⟨r, memOf memAddr s'⟩ = some x → K.ans x

/-- **The specification context of a contract**, by host code: `.host k` is import `k`. -/
def memCtx (m : Module) (memAddr : Option Nat) (R : Roles X I O C) (K : MemContract I) :
    Ctx Nat := fun k => (m.imports[k]?).map fun i => importSpec k i memAddr R K

/-- **The most general environment meeting a contract**, as a host relation. -/
def memHost (m : Module) (memAddr : Option Nat) (R : Roles X I O C) (K : MemContract I) :
    HostSemantics Nat :=
  Silmaril.Wasm.Logic.Open.specHost id (memCtx m memAddr R K)

/-- The specification of an export address for the store invariant `Inv`. -/
def exportSpec (Inv : Store Nat → Prop) (a : Nat) : FSpec Nat where
  pre s args := Inv s ∧ InvokeOk s a args
  post _ _ s' _ := Inv s'

/-- The postcondition of the instantiation run: if it returns, the invariant holds. -/
def instPost (Inv : Store Nat → Prop) : Post Nat := fun s _ o => ∀ vs, o = .normal vs → Inv s

/-- **The Hoare-logic obligation of a module under a contract**: instantiation and every export
are safe under `memHost` and keep the store invariant `Inv`. -/
def MemSat (P : Profile) (m : Module) (memIdx : Nat) (R : Roles X I O C) (K : MemContract I)
    (Inv : Store Nat → Prop) : Prop :=
  ∀ (mt : CModuleType) (Is : ScalarInstance) (c₀ : Config Nat), IsSpecInstance m mt Is c₀ →
    (∀ n, Safe P (memHost m c₀.frame.module.mems[memIdx]? R K) (instPost Inv) n c₀) ∧
    ∀ a ∈ Is.addrs, FSpecValid P (memHost m c₀.frame.module.mems[memIdx]? R K) a
      (exportSpec Inv a)

/-- **Environments whose replies meet `reply`**: every answer `a` to a call `e` has
`reply e a`. -/
def ReplyEnvs (reply : UCall Nat → UReply → Prop) : Store Nat → SEnv UImp → Prop :=
  fun _ L => ∀ q e a q', L.Ans q e a q' → reply e a

/-- The store frame of the examples: a host answer keeps the functions and the number of
memories, and may rewrite every memory's contents (and anything else in the store). -/
def KeepsCode (s s' : Store Nat) : Prop := s'.funcs = s.funcs ∧ s'.mems.length = s.mems.length

/-- The replies of the examples: they keep the code (`KeepsCode`), and the values returned by a
call of host code `k` have the shape `shape k` (the import's result type: one `i32`, or
nothing). Traps and exceptions are allowed. -/
def ShapedReply (shape : Nat → List Val → Prop) (e : UCall Nat) (a : UReply) : Prop :=
  KeepsCode e.store a.store ∧ ∀ vs, a.result = .values vs → shape e.target vs

/-! ## Writer contracts -/

/-- **The writer contract** in the fixed environment `ρ`, sentinel `sent`: accepts name members
of `L`; decoded writes are correct in `ρ`. -/
def writerContract (ix : MemImports) (sent : Option (BitVec 32))
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp) (L : Set SymStrBytesSExp)
    (reply : UCall Nat → UReply → Prop) : MemContract MemWEv where
  pre o := ∀ h, memAccept ix o = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  ans x := ∀ op args r, x = .write op args r →
    sent = some r ∨ ∃ t, (sexpW MemAtom).built ρ op args = some t ∧ ρ r = some t
  reply := reply

/-- **A closed-writes contract**: every write a call decodes to, for every reply, is closed in
`S`. -/
def closedContract (ix : MemImports) (S : Set SymStrBytesSExp)
    (reply : UCall Nat → UReply → Prop) : MemContract MemWEv where
  pre o := ∀ w op args r, memWrite ix o w = some (.write op args r) →
    Writers.WriteClosed (sexpW MemAtom) S op args
  reply := reply

/-! ## A memory-returning reader -/

/-- The named imports of the memory-returning reader. -/
structure ReadImports where
  items : String × String := ("sexp", "items")
  accept : String × String := ("sexp", "accept")

/-- Reader events over memory-carrying atoms and `i32` handles. -/
abbrev MemREv := REv (SxQ (BitVec 32)) (SxA MemAtom (BitVec 32)) (BitVec 32)

/-- The bytes at `[p, p + n)` of a memory, if in bounds. -/
def segOf (mem : ByteArray) (p n : Nat) : Option (List UInt8) :=
  (Execution.Memory.readBytes mem p n).map (·.data.toList)

/-- Exactly two words. -/
def pair32 : List (BitVec 32) → Option (BitVec 32 × BitVec 32)
  | [a, b] => some (a, b)
  | _ => none

/-- The `list<i32>` returned through `retptr`: `(ptr, len)` at `retptr`, then `len` handles at
`ptr`, all little-endian. -/
def itemsList (mem : ByteArray) (retptr : Nat) : Option (List (BitVec 32)) := do
  let (p, n) ← pair32 (← le32s (← segOf mem retptr 8))
  le32s (← segOf mem p.toNat (4 * n.toNat))

/-- The answer of `items` read off the reply: the handles, or the ill-typed `handle 0` when the
reply cannot be read. -/
def itemsAns (w : HostReply) (retptr : BitVec 32) : SxA MemAtom (BitVec 32) :=
  match w.mem.bind fun mem => itemsList mem retptr.toNat with
  | some hs => .items hs
  | none => .handle 0

/-- **A read of `items(h, retptr)`**, decoded at its answer (returning no values). -/
def itemsRead (ix : ReadImports) (o : Callout) (w : HostReply) : Option MemREv :=
  if o.imp = ix.items then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, rp⟩], .values [] =>
        some (.read (.items h) (itemsAns w rp))
    | _, _ => none
  else none

/-- A call of `accept(h)`. -/
def readAccept (ix : ReadImports) (o : Callout) : Option MemREv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the memory-returning reader: accepts at calls, reads at answers. -/
def memReadRoles (ix : ReadImports) : Roles Unit MemREv Unit Unit where
  callIn := readAccept ix
  answerIn := itemsRead ix

/-- **The reader traces of a module** through the memory-returning reader. -/
def memReadTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : ReadImports) : Set (List MemREv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (memReadRoles ix)

/-- **The reader language of a module** through the memory-returning reader. -/
def memReaderLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : ReadImports) (pol : OnBadRead (SxQ (BitVec 32)) (SxA MemAtom (BitVec 32)))
    (oa : OnInvalid) (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    Set SymStrBytesSExp :=
  readerLang (sexpR MemAtom (BitVec 32)) pol oa Rhos (memReadTraces P Envs memIdx m ix)

/-- **The reader contract** in the fixed environment `ρ`: reads are correct in `ρ`; accepts
name members of `L`. -/
def readerContract (ix : ReadImports) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)
    (L : Set SymStrBytesSExp) (reply : UCall Nat → UReply → Prop) : MemContract MemREv where
  pre o := ∀ h, readAccept ix o = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  ans x := ∀ q a, x = .read q a →
    (sexpR MemAtom (BitVec 32)).valid ρ q ∧ (sexpR MemAtom (BitVec 32)).ok ρ q a
  reply := reply

end Silmaril.Wasm.Game.HandleAccept.MemSound
