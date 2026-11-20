module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Defs
public import Silmaril.Semantics.Accept.Handle.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Langs

/-!
# Memory-observing soundness: the bridge

For a module `m` meeting a contract `K` in the program logic (`MemSat P m memIdx R K Inv`: its
instantiation and every export are safe under the most general host of `K` and keep the store
invariant `Inv`), and every class of environments whose replies are admitted by `K`
(`Envs s L → ReplyEnvs K.reply s L`):

* `tagTraces_pre` (**the bridge**): in every traced session (every instantiation, every
  admitted environment, every sequence of export invocations, every profile `P` for which
  `MemSat` is proved), every decoded input `x` whose earlier inputs all meet `K.ans` is decoded
  from a callout `o` with `K.pre o`, either at the call (`R.callIn o = some x`) or at its answer
  (`R.answerIn o w = some x`). The callout `o` carries the bytes of the instance's memory at the
  call, so `K.pre` is a fact about memory established by Hoare logic.

Writer and reader languages (`Silmaril.Wasm.Game.HandleAccept.Memory.memWriterLang`,
`memReaderLang`):

* `memWriterLang_subset_of_closed`: with a closed-writes contract (every write decoded at a
  call's answer is closed in `S`), the writer language is included in `S`, for every policy
  without undefined behaviour;
* `memFixedLang_subset`: with the writer contract in the fixed environment `ρ`, the
  fixed-environment writer language in `ρ` is included in `L`, for every policy;
  `memWriterLang_subset`: from the obligation in every fixed environment, the writer language
  (store semantics, no undefined behaviour) is included in `L`;
* `memReaderLang_subset`: with the reader contract in every fixed environment, the reader
  language of the memory-returning reader (`items(h, retptr)`) under the trapping read policy is
  included in `L`, for every accept policy without undefined behaviour and every set of fixed
  environments.

**What is observed.** A write event `write op args r` is read off the callout of the call
(its arguments and the memory at the call) and the raw reply (`r`); an `items` read off the
memory **after** the answer; an `accept(h)` off the call. Export invocations are `enter`
events. The admitted environments are those of `ReplyEnvs K.reply` (any state machine whose
answers meet `K.reply`, for instance "keeps the code, may rewrite memory, returns one `i32`");
host divergence and traps are allowed.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory

variable {X I O C : Type} {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}
  {m : Module} {Inv : Store Nat → Prop}

/-- **The bridge**: inputs preceded by admitted answers are decoded from callouts meeting the
contract's precondition. -/
theorem tagTraces_pre {R : Roles X I O C} {K : MemContract I}
    (hsat : MemSat P m memIdx R K Inv) (hE : ∀ s L, Envs s L → ReplyEnvs K.reply s L)
    {ts : List (Tag X I O C)} (hts : ts ∈ tagTraces P Envs memIdx m R)
    {u v : List (Tag X I O C)} {x : I} (hd : ts = u ++ .inp x :: v)
    (hu : ∀ y, Tag.inp y ∈ u → K.ans y) :
    ∃ o, K.pre o ∧ (R.callIn o = some x ∨ ∃ w, R.answerIn o w = some x) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.tagTraces_pre hsat hE hts hd hu

/-- **Closed writes bound the writer language.** -/
theorem memWriterLang_subset_of_closed {ix : MemImports} {pol : Policy (BitVec 32)}
    {S : Set SymStrBytesSExp} {reply : UCall Nat → UReply → Prop}
    (hsat : MemSat P m memIdx (memRoles ix) (closedContract ix S reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : memWriterLang P Envs memIdx m ix pol ⊆ S :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.memWriterLang_subset_of_closed hsat hE ha hw

/-- **The memory writer bridge in a fixed environment**, for every policy. -/
theorem memFixedLang_subset {ix : MemImports} {pol : Policy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop}
    (hsat : MemSat P m memIdx (memRoles ix) (writerContract ix pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang (sexpW MemAtom) pol {ρ} (memTraces P Envs memIdx m ix) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.memFixedLang_subset hsat hE

/-- **The memory writer bridge** (store semantics, no undefined behaviour). -/
theorem memWriterLang_subset {ix : MemImports} {pol : Policy (BitVec 32)}
    {L : Set SymStrBytesSExp} {reply : UCall Nat → UReply → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (memRoles ix) (writerContract ix pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : memWriterLang P Envs memIdx m ix pol ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.memWriterLang_subset hsat hE hw ha

/-- **The memory reader bridge** (trapping read policy, no accept UB). -/
theorem memReaderLang_subset {ix : ReadImports} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (memReadRoles ix) (readerContract ix ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    memReaderLang P Envs memIdx m ix .trap oa Rhos ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.memReaderLang_subset hsat hE hoa Rhos

end Silmaril.Wasm.Game.HandleAccept.MemSound
