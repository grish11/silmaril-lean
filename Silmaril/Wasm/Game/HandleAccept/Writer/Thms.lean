module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs
public import Silmaril.Wasm.Game.HandleAccept.Thms
public import Silmaril.Semantics.Accept.Handle.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Decode
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Bounds

/-!
# Writer APIs of core Wasm modules: laws

**Generic** (any writer signature, any decoded strategy):

* `writerLang_subset_of_closed`: without undefined behaviour (`onAccept ≠ ub`,
  `onWrite ≠ ub`), if every write of every trace is closed in `S` (`WriteClosed`: arguments
  denoting trees of `S` build a tree of `S`), the writer language is included in `S`;
* `fixedLang_subset_of_AG`, the **writer bridge** in a fixed environment `ρ`: plays that are
  assume/guarantee correct for `writerISpec W pol.sentinel dAsk dAns ρ L` (asks decoding only to
  `accept`, answers only to writes) have their writer language in `ρ` included in `L`, for every
  policy; `writerLang_subset_of_AG` for the store semantics (no UB), from the obligation in
  every fixed environment, through `writerLang_subset_fixedLang`.

**Wasm** (the cons and n-ary APIs of `Defs`):

* `consWLang_sound_of_gameSat` / `sxWLang_sound_of_gameSat`: the Hoare-logic obligation
  `GameSat` for `writerISpec` in every environment gives `moduleConsWLang … ⊆ L` (no
  `accept_all` import, no UB); `consWFixedLang_sound_of_gameSat` /
  `sxWFixedLang_sound_of_gameSat` for the fixed-environment languages over a set `Envs`, for
  every policy;
* **structural bounds**, for every module and profile, with no obligation:
  `moduleConsWLang_subset_atoms2` (a module without `nil` and `cons` imports accepts only
  words), `moduleSxWLang_subset_arities` (every list node a module builds has the arity of one
  of its list-constructor imports: a module importing only `list2` accepts only binary lists),
  `moduleSxWLang_subset_atoms` (no list-constructor import: only words).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Writers

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Strategy (ISpec AG)
open Silmaril.Wasm.Logic.GameLink (GameSat)

/-! ## Generic -/

theorem writerLang_subset_of_closed {Op X H : Type} [DecidableEq H] {W : Writer Op X}
    {pol : Policy H} (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) {S : Set X}
    {T : Set (List (WEv Op H))}
    (hT : ∀ t ∈ T, ∀ op args r, WEv.write op args r ∈ t → WriteClosed W S op args) :
    writerLang W pol T ⊆ S :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.writerLang_subset_of_closed ha hw hT

variable {E F : Sig.{0}}

theorem fixedLang_subset_of_AG {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) X} {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))}
    (hAG : ∀ p ∈ σ, AG (writerISpec W pol.sentinel dAsk dAns ρ L) (topISpec F) p)
    (hask : ∀ e ev, dAsk e = some ev → ∃ h, ev = .accept h)
    (hans : ∀ e v ev, dAns e v = some ev → ∃ op args r, ev = .write op args r) :
    fixedLang W pol {ρ} (handleTraces σ (some .enter) dAsk dAns) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.fixedLang_subset_of_AG hAG hask hans

theorem writerLang_subset_of_AG {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))}
    (hAG : ∀ ρ, ∀ p ∈ σ, AG (writerISpec W pol.sentinel dAsk dAns ρ L) (topISpec F) p)
    (hask : ∀ e ev, dAsk e = some ev → ∃ h, ev = .accept h)
    (hans : ∀ e v ev, dAns e v = some ev → ∃ op args r, ev = .write op args r)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (handleTraces σ (some .enter) dAsk dAns) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.writerLang_subset_of_AG hAG hask hans hw ha

/-- Over a set of fixed environments. -/
theorem fixedLang_subset_of_forall {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)} {L : Set X}
    {T : Set (List (WEv Op (BitVec 32)))}
    (h : ∀ ρ ∈ Envs, fixedLang W pol {ρ} T ⊆ L) : fixedLang W pol Envs T ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.fixedLang_subset_of_forall h

/-! ## Decoders -/

variable {ts : List FnType}

theorem consWDecAns_isWrite (ix : ConsWImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e)
    (ev : ConsWEv) (h : consWDecAns ix e v = some ev) : ∃ op args r, ev = .write op args r := by
  obtain ⟨r, ⟨-, w, rfl⟩ | ⟨-, rfl⟩ | ⟨-, args, -, rfl⟩⟩ :=
    Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.consWDecAns_cases h <;> exact ⟨_, _, _, rfl⟩

theorem consWDecAsk_isAccept {ix : ConsWImports} (hall : ix.acceptAll = none)
    (e : (ifaceSig ts).Op) (ev : ConsWEv) (h : consWDecAsk ix e = some ev) :
    ∃ h, ev = .accept h := by
  rcases Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.consWDecAsk_cases h with h | ⟨h, -⟩
  · exact h
  · simp [hall] at h

theorem sxWDecAns_isWrite (ix : SxWImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e)
    (ev : SxWEv) (h : sxWDecAns ix e v = some ev) : ∃ op args r, ev = .write op args r := by
  obtain ⟨r, ⟨-, w, rfl⟩ | ⟨-, args, -, rfl⟩⟩ :=
    Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.sxWDecAns_cases h <;> exact ⟨_, _, _, rfl⟩

theorem sxWDecAsk_isAccept {ix : SxWImports} (hall : ix.acceptAll = none)
    (e : (ifaceSig ts).Op) (ev : SxWEv) (h : sxWDecAsk ix e = some ev) :
    ∃ h, ev = .accept h := by
  rcases Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.sxWDecAsk_cases h with h | ⟨h, -⟩
  · exact h
  · simp [hall] at h

/-! ## Soundness from Hoare-logic obligations -/

/-- **Soundness of a cons writer module** from its Hoare-logic obligation in every fixed
environment (store semantics, no UB, no `accept_all`). -/
theorem consWLang_sound_of_gameSat {P : Profile} {m : Module} {ix : ConsWImports}
    {pol : Policy (BitVec 32)} {L : Set (SExp2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ, GameSat P (Verify.instOf m) Inv
      (writerISpec (consW (BitVec 64)) pol.sentinel (consWDecAsk ix) (consWDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hall : ix.acceptAll = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    moduleConsWLang P m ix pol ⊆ L :=
  writerLang_subset_of_AG
    (fun ρ _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ) hs hp).2)
    (consWDecAsk_isAccept hall) (consWDecAns_isWrite ix) hw ha

/-- Soundness of a cons writer module over fixed environments, for every policy. -/
theorem consWFixedLang_sound_of_gameSat {P : Profile} {m : Module} {ix : ConsWImports}
    {pol : Policy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))}
    {L : Set (SExp2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv
      (writerISpec (consW (BitVec 64)) pol.sentinel (consWDecAsk ix) (consWDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hall : ix.acceptAll = none) :
    moduleConsWFixedLang P m ix pol Envs ⊆ L :=
  fixedLang_subset_of_forall fun ρ hρ => fixedLang_subset_of_AG
    (fun _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ hρ) hs hp).2)
    (consWDecAsk_isAccept hall) (consWDecAns_isWrite ix)

/-- **Soundness of an n-ary writer module** from its Hoare-logic obligation in every fixed
environment (store semantics, no UB, no `accept_all`). -/
theorem sxWLang_sound_of_gameSat {P : Profile} {m : Module} {ix : SxWImports}
    {pol : Policy (BitVec 32)} {L : Set (SExp (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ, GameSat P (Verify.instOf m) Inv
      (writerISpec (sexpW (BitVec 64)) pol.sentinel (sxWDecAsk ix) (sxWDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hall : ix.acceptAll = none) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    moduleSxWLang P m ix pol ⊆ L :=
  writerLang_subset_of_AG
    (fun ρ _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ) hs hp).2)
    (sxWDecAsk_isAccept hall) (sxWDecAns_isWrite ix) hw ha

/-- Soundness of an n-ary writer module over fixed environments, for every policy. -/
theorem sxWFixedLang_sound_of_gameSat {P : Profile} {m : Module} {ix : SxWImports}
    {pol : Policy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))}
    {L : Set (SExp (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv
      (writerISpec (sexpW (BitVec 64)) pol.sentinel (sxWDecAsk ix) (sxWDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hall : ix.acceptAll = none) :
    moduleSxWFixedLang P m ix pol Envs ⊆ L :=
  fixedLang_subset_of_forall fun ρ hρ => fixedLang_subset_of_AG
    (fun _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ hρ) hs hp).2)
    (sxWDecAsk_isAccept hall) (sxWDecAns_isWrite ix)

/-! ## Structural bounds -/

theorem atom_writeClosed2 (w : BitVec 64) (args : List (BitVec 32)) :
    WriteClosed (consW (BitVec 64)) atoms2 (.atom w) args :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.atom_writeClosed2 w args

/-- **A module without `nil` and `cons` imports accepts only words** (every module, profile and
policy without UB). -/
theorem moduleConsWLang_subset_atoms2 {P : Profile} {m : Module} {ix : ConsWImports}
    {pol : Policy (BitVec 32)} (hn : (Verify.instOf m).imports.length ≤ ix.nil)
    (hc : (Verify.instOf m).imports.length ≤ ix.cons) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : moduleConsWLang P m ix pol ⊆ atoms2 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.moduleConsWLang_subset_atoms2 hn hc ha hw

theorem atom_writeClosed (K : Set Nat) (w : BitVec 64) (args : List (BitVec 32)) :
    WriteClosed (sexpW (BitVec 64)) {x | ListArities K x} (.atom w) args :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.atom_writeClosed K w args

theorem list_writeClosed {K : Set Nat} {args : List (BitVec 32)} (hK : args.length ∈ K) :
    WriteClosed (sexpW (BitVec 64)) {x | ListArities K x} .list args :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.list_writeClosed hK

/-- **List arities are bounded by the imports**: every list node of every tree a module
accepts through the n-ary API has the arity of one of its list-constructor imports (every
module, profile and policy without UB). -/
theorem moduleSxWLang_subset_arities {P : Profile} {m : Module} {ix : SxWImports}
    {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    moduleSxWLang P m ix pol ⊆ {x | ListArities (sxArities ix (Verify.instOf m).imports) x} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.moduleSxWLang_subset_arities ha hw

theorem listArities_empty {x : SExp (BitVec 64)} (h : ListArities ∅ x) : x ∈ atoms :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.listArities_empty h

/-- **A module without list-constructor imports accepts only words.** -/
theorem moduleSxWLang_subset_atoms {P : Profile} {m : Module} {ix : SxWImports}
    {pol : Policy (BitVec 32)} (hl : ∀ j ∈ ix.lists, (Verify.instOf m).imports.length ≤ j)
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) : moduleSxWLang P m ix pol ⊆ atoms :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.moduleSxWLang_subset_atoms hl ha hw

end Silmaril.Wasm.Game.HandleAccept.Writers
