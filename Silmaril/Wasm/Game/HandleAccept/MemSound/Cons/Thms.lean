module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Defs
public import Silmaril.Semantics.Accept.Handle.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ConsLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ConsMixLive

/-!
# The cons API through linear memory: bridges, soundness and non-vacuity

**Bridges for any roles** (`rolesFixedLang_subset`, `rolesWriterLang_subset`): for roles decoding
accepts at calls and writes at answers, and any writer `W`, a module meeting
`roleWriterContract R W pol.sentinel ρ L reply` in the program logic (`MemSat`) has its
fixed-environment writer language in `ρ` included in `L` (every policy), resp. its writer language
(store semantics, no undefined behaviour) when the obligation holds in every `ρ`. Instances:
`consFixedLang_subset`, `consWriterLang_subset` for the cons roles `consRoles`.

**The example `consMod`** (`symbol(0, 2)` over `68 69`, `nil()`, `cons`, `accept`), for every
profile, against every environment admitted by `consReply`:

* `consMod_fixed_sound`: in every fixed environment and for every policy without a sentinel, it
  accepts only `(hi)`;
* `consMod_sound`: the same for the writer language (no sentinel, no undefined behaviour);
* `consMod_live`: it accepts `(hi)`, for every policy (traced session against the counting host);
* `consMod_lang`: **its writer language is exactly `{(hi)}`** (no sentinel, no undefined
  behaviour).

**Mixed atom kinds: `consMix`** (`symbol(0, 2)` and `string(0, 2)` over `68 69`, `nil()`, two
`cons`, `accept`), against every environment admitted by `consMixReply`: `consMix_fixed_sound`,
`consMix_sound`, `consMix_live`, and `consMix_lang`: **its writer language is exactly
`{(hi "hi")}`** (a symbol and a string atom; no sentinel, no undefined behaviour).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Cons

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api

variable {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module}

/-- **The writer bridge in a fixed environment**, for any roles and writer. -/
theorem rolesFixedLang_subset {Op Y : Type} {W : Writer Op Y}
    {R : Roles Unit (WEv Op (BitVec 32)) Unit Unit}
    (hcall : ∀ o e, R.callIn o = some e → ∃ h, e = .accept h)
    (hans : ∀ o w e, R.answerIn o w = some e → ∃ op args r, e = .write op args r)
    {pol : Policy (BitVec 32)} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) Y} {L : Set Y}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx R (roleWriterContract R W pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang W pol {ρ} (inputsOf (some .enter) '' tagTraces P Envs memIdx m R) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.rolesFixedLang_subset hcall hans hsat hE

/-- **The writer bridge** (store semantics, no undefined behaviour), for any roles and writer. -/
theorem rolesWriterLang_subset {Op Y : Type} {W : Writer Op Y}
    {R : Roles Unit (WEv Op (BitVec 32)) Unit Unit}
    (hcall : ∀ o e, R.callIn o = some e → ∃ h, e = .accept h)
    (hans : ∀ o w e, R.answerIn o w = some e → ∃ op args r, e = .write op args r)
    {pol : Policy (BitVec 32)} {L : Set Y} {reply : UCall Nat → UReply → Prop}
    {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx R (roleWriterContract R W pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (inputsOf (some .enter) '' tagTraces P Envs memIdx m R) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.rolesWriterLang_subset hcall hans hsat hE
    hw ha

/-- **The cons writer bridge in a fixed environment**, for every policy. -/
theorem consFixedLang_subset {ix : ConsImports} {pol : Policy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 MemAtom)} {L : Set (SExp2 MemAtom)}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx (consRoles ix)
      (roleWriterContract (consRoles ix) (consW MemAtom) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang (consW MemAtom) pol {ρ} (consTraces P Envs memIdx m ix) ⊆ L :=
  rolesFixedLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consWrite_isWrite h)
    hsat hE

/-- **The cons writer bridge** (store semantics, no undefined behaviour). -/
theorem consWriterLang_subset {ix : ConsImports} {pol : Policy (BitVec 32)}
    {L : Set (SExp2 MemAtom)} {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (consRoles ix)
      (roleWriterContract (consRoles ix) (consW MemAtom) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : consWriterLang P Envs memIdx m ix pol ⊆ L :=
  rolesWriterLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consWrite_isWrite h)
    hsat hE hw ha

/-- **In a fixed environment, `consMod` accepts only `(hi)`.** -/
theorem consMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 MemAtom)) :
    fixedLang (consW MemAtom) pol {ρ} (consTraces P (ReplyEnvs consReply) 0 consMod {}) ⊆
      {hiList} :=
  consFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.cons_sat P ρ)
    (fun _ _ h => h)

/-- **`consMod` accepts only `(hi)`.** -/
theorem consMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    consWriterLang P (ReplyEnvs consReply) 0 consMod {} pol ⊆ {hiList} :=
  consWriterLang_subset
    (fun ρ => by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.cons_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`consMod` accepts `(hi)`**, for every policy. -/
theorem consMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    hiList ∈ consWriterLang P (ReplyEnvs consReply) 0 consMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consMod_live P pol

/-- **The writer language of `consMod` is exactly `{(hi)}`.** -/
theorem consMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    consWriterLang P (ReplyEnvs consReply) 0 consMod {} pol = {hiList} :=
  Set.Subset.antisymm (consMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (consMod_live P pol))

/-! ## Mixed atom kinds -/

/-- **In a fixed environment, `consMix` accepts only `(hi "hi")`.** -/
theorem consMix_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 MemAtom)) :
    fixedLang (consW MemAtom) pol {ρ} (consTraces P (ReplyEnvs consMixReply) 0 consMix {}) ⊆
      {mixList} :=
  consFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consMix_sat P ρ)
    (fun _ _ h => h)

/-- **`consMix` accepts only `(hi "hi")`.** -/
theorem consMix_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    consWriterLang P (ReplyEnvs consMixReply) 0 consMix {} pol ⊆ {mixList} :=
  consWriterLang_subset
    (fun ρ => by
      rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consMix_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`consMix` accepts `(hi "hi")`**, for every policy. -/
theorem consMix_live (P : Profile) (pol : Policy (BitVec 32)) :
    mixList ∈ consWriterLang P (ReplyEnvs consMixReply) 0 consMix {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.consMix_live P pol

/-- **The writer language of `consMix` is exactly `{(hi "hi")}`**: a symbol and a string atom. -/
theorem consMix_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    consWriterLang P (ReplyEnvs consMixReply) 0 consMix {} pol = {mixList} :=
  Set.Subset.antisymm (consMix_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (consMix_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
