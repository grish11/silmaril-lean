module

public import Silmaril.Wasm.Game.HandleAccept.Tree2.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2.Decode

/-!
# Binary-tree APIs of core Wasm modules: laws

* Writer: `pairWDecAns_isWrite`, `pairWDecAsk_isAccept` (the decoders produce writes and
  accepts), and the bridges `tree2WLang_sound_of_gameSat` (store semantics, no UB, no
  `accept_all`) and `tree2WFixedLang_sound_of_gameSat` (fixed environments, every policy), from
  the Hoare-logic obligation for `writerISpec (pairW _)`.
* Reader: `t2DecAns_ne_accept`, and the bridges `tree2Lang_sound_of_gameSat` /
  `tree2Lang_sound_of_forall` (`readerLang_subset_of_AG` and
  `Silmaril.Wasm.Logic.GameLink.strategy_sound`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Tree2

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
open Silmaril.Wasm.Logic.GameLink (GameSat)

variable {ts : List FnType}

/-! ## Writer -/

theorem pairWDecAns_isWrite (ix : PairWImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e)
    (ev : PairWEv) (h : pairWDecAns ix e v = some ev) : ∃ op args r, ev = .write op args r := by
  obtain ⟨r, ⟨-, w, rfl⟩ | ⟨-, args, rfl⟩⟩ :=
    Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2.pairWDecAns_cases h <;> exact ⟨_, _, _, rfl⟩

theorem pairWDecAsk_isAccept {ix : PairWImports} (hall : ix.acceptAll = none)
    (e : (ifaceSig ts).Op) (ev : PairWEv) (h : pairWDecAsk ix e = some ev) :
    ∃ h, ev = .accept h := by
  rcases Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2.pairWDecAsk_cases h with h | ⟨h, -⟩
  · exact h
  · simp [hall] at h

/-- **Soundness of a binary-tree writer module** from its Hoare-logic obligation in every
fixed environment (store semantics, no UB, no `accept_all`). -/
theorem tree2WLang_sound_of_gameSat {P : Profile} {m : Module} {ix : PairWImports}
    {pol : Policy (BitVec 32)} {L : Set (Tree2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ, GameSat P (Verify.instOf m) Inv
      (writerISpec (pairW (BitVec 64)) pol.sentinel (pairWDecAsk ix) (pairWDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hall : ix.acceptAll = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    moduleTree2WLang P m ix pol ⊆ L :=
  writerLang_subset_of_AG
    (fun ρ _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ) hs hp).2)
    (pairWDecAsk_isAccept hall) (pairWDecAns_isWrite ix) hw ha

/-- Soundness of a binary-tree writer module over fixed environments, for every policy. -/
theorem tree2WFixedLang_sound_of_gameSat {P : Profile} {m : Module} {ix : PairWImports}
    {pol : Policy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64)))}
    {L : Set (Tree2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv
      (writerISpec (pairW (BitVec 64)) pol.sentinel (pairWDecAsk ix) (pairWDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hall : ix.acceptAll = none) :
    moduleTree2WFixedLang P m ix pol Envs ⊆ L :=
  fixedLang_subset_of_forall fun ρ hρ => fixedLang_subset_of_AG
    (fun _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ hρ) hs hp).2)
    (pairWDecAsk_isAccept hall) (pairWDecAns_isWrite ix)

/-! ## Reader -/

theorem t2DecAns_ne_accept (ix : T2RImports) (e : (ifaceSig ts).Op)
    (v : (ifaceSig ts).Ar e) (h : BitVec 32) : t2DecAns ix e v ≠ some (.accept h) := by
  unfold t2DecAns
  cases t2DecRead ix e v <;> simp

/-- **Soundness of a binary-tree reader checker from its Hoare-logic obligation.** -/
theorem tree2Lang_sound_of_gameSat {P : Profile} {m : Module} {ix : T2RImports}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64))} {L : Set (Tree2 (BitVec 64))}
    {Inv : Store Nat → Prop}
    (hm : GameSat P (Verify.instOf m) Inv (tree2ISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleTree2Lang P m ix .trap oa {ρ} ⊆ L :=
  readerLang_subset_of_AG
    (fun _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hp).2)
    (fun _ _ h => h) (fun _ h hd hpre => hpre h hd)
    (t2DecAns_ne_accept ix) hoa

/-- For every environment of a set. -/
theorem tree2Lang_sound_of_forall {P : Profile} {m : Module} {ix : T2RImports}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64)))}
    {L : Set (Tree2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv (tree2ISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleTree2Lang P m ix .trap oa Envs ⊆ L := fun _ hx => by
  obtain ⟨⟨ρ, hρ⟩, hx⟩ := Silmaril.Accept.mem_langOver.1 hx
  exact tree2Lang_sound_of_gameSat (hm ρ hρ) hs hoa (Silmaril.Accept.mem_langOver.2 ⟨⟨ρ, rfl⟩, hx⟩)

end Silmaril.Wasm.Game.HandleAccept.Tree2
