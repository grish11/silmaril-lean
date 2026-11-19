module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Defs
public import Silmaril.Wasm.Game.HandleAccept.Thms
public import Silmaril.Semantics.Accept.Handle.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Module

/-!
# Accept variants of the cons writer API: laws

* `ask_of_ans`: in every play of an instance strategy, an answered import call was asked
  before, so a precondition at the question covers its answer.
* `storeLang_subset_of_AG`, **the store bridge for accept variants**: for an instance strategy
  whose questions decode to `accept`, `acceptAll`, `acceptBatch` and whose answers decode to
  writes and `acceptErr`, assume/guarantee correctness for `storeISpec … ρ L C` in every
  environment `ρ` leaving the sentinel undefined bounds the writer language (store semantics,
  no UB) by `L`. The environment used is the final store of each run
  (`Silmaril.Wasm.Game.HandleAccept.Combined.crun_facts_init`); bulk accepts are bounded by the
  constructed-set bound `C`, which the module guarantees is in `L` when it calls them.
* `consXLang_sound_of_gameSat`: the same from a module's Hoare-logic obligation.

**Examples** (the modules of `Defs`; every profile, every writer policy without UB, **any
sentinel**):

* `errAccept_sound`: `errAccept` accepts only words and `nil` (`errL`), under the error-return
  semantics of `accept_err` (a failed `word` returns the sentinel, which no environment run
  defines, and `accept_err` of it answers an error).
* `allAccept_sound`: `allAccept` accepts only `allL` (words, `nil`, `(w)`), which is downward
  closed (`allL_downClosed`), as the constructed set must be.
* `batchAccept_sound`: `batchAccept` accepts only `allL`. This bound is the constructed set: the
  per-move store specification cannot see which batch a tree belongs to, so it does not show
  that the dropped word is never accepted (`Examples` shows the kept trees are accepted, and the
  abstract `Silmaril.Accept.Handle.Examples.t4_lang` computes the exact language of a batch
  trace).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Accept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Strategy (ISpec AG)
open Silmaril.Wasm.Logic.GameLink (GameSat)

theorem ask_of_ans {I : ScalarInstance} {P : Profile} {s : Store Nat}
    {p : List (Move I.E I.F)} (hp : p ∈ I.strategy P s) {e : I.E.Op} {v : I.E.Ar e}
    (hm : (.inl (.ans e v) : Move I.E I.F) ∈ p) : (.inl (.ask e) : Move I.E I.F) ∈ p :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.ask_of_ans hp hm

theorem storeLang_subset_of_AG {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {L C : Set X} {I : ScalarInstance} {P : Profile} {s : Store Nat}
    {dAsk : I.E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : I.E.Op) → I.E.Ar e → Option (WEv Op (BitVec 32))}
    (hAG : ∀ ρ : Silmaril.Accept.Handle.Env (BitVec 32) X,
      (∀ r, pol.sentinel = some r → ρ r = none) →
      ∀ p ∈ I.strategy P s, AG (storeISpec W pol.sentinel dAsk dAns ρ L C) (topISpec _) p)
    (hask : ∀ e ev, dAsk e = some ev →
      (∃ h, ev = .accept h) ∨ ev = .acceptAll ∨ ∃ k, ev = .acceptBatch k)
    (hans : ∀ e v ev, dAns e v = some ev →
      (∃ op args r, ev = .write op args r) ∨ ∃ h b, ev = .acceptErr h b)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (handleTraces (I.strategy P s) (some .enter) dAsk dAns) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.storeLang_subset_of_AG
    (fun _ hp _ _ hm => ask_of_ans hp hm) hAG hask hans hw ha

variable {ts : List FnType}

theorem consXDecAsk_isAsk (ix : ConsXImports) (e : (ifaceSig ts).Op) (ev : ConsWEv)
    (h : consXDecAsk ix e = some ev) :
    (∃ h, ev = .accept h) ∨ ev = .acceptAll ∨ ∃ k, ev = .acceptBatch k := by
  rcases Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.consXDecAsk_cases ix e ev h with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  exacts [.inl h, .inr (.inl h), .inr (.inr h)]

/-- **Soundness of a module with accept variants** from its Hoare-logic obligation in every
environment leaving the sentinel undefined. -/
theorem consXLang_sound_of_gameSat {P : Profile} {m : Module} {ix : ConsXImports}
    {pol : Policy (BitVec 32)} {L C : Set (SExp2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)),
      (∀ r, pol.sentinel = some r → ρ r = none) →
      GameSat P (Verify.instOf m) Inv
        (storeISpec (consW (BitVec 64)) pol.sentinel (consXDecAsk ix) (consXDecAns ix) ρ L C)
        (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleConsXLang P m ix pol ⊆ L :=
  storeLang_subset_of_AG
    (fun ρ hρ _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ hρ) hs hp).2)
    (consXDecAsk_isAsk ix)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.consXDecAns_cases ix) hw ha

/-! ## Examples -/

theorem errAccept_instance : (Verify.instance? errAccept).isSome = true := by decide +kernel
theorem allAccept_instance : (Verify.instance? allAccept).isSome = true := by decide +kernel
theorem batchAccept_instance : (Verify.instance? batchAccept).isSome = true := by decide +kernel

/-- **`errAccept` accepts only words and `nil`**, under the error-return semantics, for every
profile, every policy without UB and every sentinel. -/
theorem errAccept_sound (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : moduleConsXLang P errAccept variantsIx pol ⊆ errL :=
  consXLang_sound_of_gameSat (C := Set.univ)
    (fun ρ hρ => Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.errAccept_sat P
      pol.sentinel ρ hρ) rfl hw ha

/-- **`allAccept` accepts only its constructed set `allL`.** -/
theorem allAccept_sound (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : moduleConsXLang P allAccept variantsIx pol ⊆ allL :=
  consXLang_sound_of_gameSat (C := allL)
    (fun ρ hρ => Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.allAccept_sat P
      pol.sentinel ρ hρ) rfl hw ha

/-- **`batchAccept` accepts only trees of its constructed set `allL`.** -/
theorem batchAccept_sound (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : moduleConsXLang P batchAccept variantsIx pol ⊆ allL :=
  consXLang_sound_of_gameSat (C := allL)
    (fun ρ hρ => Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.batchAccept_sat P
      pol.sentinel ρ hρ) rfl hw ha

/-- The constructed set of `allAccept` is downward closed under the car/cdr child relation. -/
theorem allL_downClosed : DownClosed SExp2.Child allL := by
  rintro t (⟨w, rfl⟩ | rfl | ⟨w, rfl⟩) c ⟨x, y, hxy, hc⟩
  · cases hxy
  · cases hxy
  · obtain ⟨rfl, rfl⟩ := SExp2.cons.inj hxy
    rcases hc with rfl | rfl
    · exact .inl ⟨w, rfl⟩
    · exact .inr (.inl rfl)

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants
