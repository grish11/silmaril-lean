module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Defs
public import Silmaril.Wasm.Game.HandleAccept.Combined.Thms
public import Silmaril.Wasm.Game.Strategy.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic

/-! # Proofs: the store bridge for writers with accept variants

* `ask_of_ans`: in a play of an instance strategy every answer `.inl (.ans e v)` follows its
  question `.inl (.ask e)`, so a precondition on `e` is available for every answered call.
* `wrun_combined`: a writer run is a combined run (with the reader `noR`, which has no valid
  query), so `crun_facts_init` describes the final store of writer runs.
* `storeLang_subset_of_AG`: the store bridge for writers whose answers decode to writes and
  error-return accepts and whose questions decode to `accept`, `acceptAll` and `acceptBatch`.
* What the decoders `consXDecAsk`, `consXDecAns` produce.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
  Silmaril.Wasm.Game.HandleAccept.AcceptVariants Silmaril.Wasm.Game.HandleAccept.Combined
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host Silmaril.Proofs.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Answers follow their questions -/

theorem path_ans_ask {I : ScalarInstance} {P : Profile} :
    ∀ {q q' : I.HState} {p : List (Move I.E I.F)}, I.Path P q p q' →
      ∀ e v, (.inl (.ans e v) : Move I.E I.F) ∈ p →
        (.inl (.ask e) : Move I.E I.F) ∈ p ∨ ∃ f s t, q = .waiting f s t e := by
  intro q q' p hp
  induction hp with
  | nil => intro _ _ h; simp at h
  | @cons q₀ q₁ q₂ m p htr _ ih =>
    intro e v hm
    rcases List.mem_cons.1 hm with rfl | hm
    · cases htr with
      | uret => exact .inr ⟨_, _, _, rfl⟩
    · rcases ih e v hm with h | ⟨f, s, t, rfl⟩
      · exact .inl (List.mem_cons_of_mem _ h)
      · cases htr with
        | ucall => exact .inl List.mem_cons_self

/-- **Every answer of a play of an instance follows its question.** -/
theorem ask_of_ans {I : ScalarInstance} {P : Profile} {s : Store Nat}
    {p : List (Move I.E I.F)} (hp : p ∈ I.strategy P s) {e : I.E.Op} {v : I.E.Ar e}
    (hm : (.inl (.ans e v) : Move I.E I.F) ∈ p) : (.inl (.ask e) : Move I.E I.F) ∈ p := by
  obtain ⟨q, hq⟩ := ScalarInstance.mem_strategy_iff.1 hp
  rcases path_ans_ask hq e v hm with h | ⟨_, _, _, h⟩
  · exact h
  · cases h

/-! ## Writer runs as combined runs -/

/-- The reader with no valid query. -/
def noR (H X : Type) : Reader PEmpty PEmpty H X := ⟨fun _ _ => False, fun _ _ _ => False⟩

theorem noR_mono {H X : Type} : (noR H X).Mono :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ _ h _ => h⟩

variable {Op X H : Type} [DecidableEq H] {W : Writer Op X} {pol : Policy H}

theorem wrun_combined {s s' : WState H X} {t : List (WEv Op H)} {S : Set X}
    (hr : (writer W pol).Run s t s' S) :
    (combined W (noR H X) pol .trap).Run s (t.map CEv.w) s' S := by
  induction hr with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (CStep.w hs) ih

omit [DecidableEq H] in
theorem mem_map_w {Q A : Type} {e : WEv Op H} {t : List (WEv Op H)} :
    (CEv.w e : CEv Op H Q A) ∈ t.map CEv.w ↔ e ∈ t := by
  simp

/-! ## The bridge -/

variable {E F : Sig.{0}}

/-- **The store bridge for writers with accept variants.** -/
theorem storeLang_subset_of_AG {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {L C : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))}
    (hσ : ∀ p ∈ σ, ∀ e v, (.inl (.ans e v) : Move E F) ∈ p → (.inl (.ask e) : Move E F) ∈ p)
    (hAG : ∀ ρ : Env (BitVec 32) X, (∀ r, pol.sentinel = some r → ρ r = none) →
      ∀ p ∈ σ, AG (storeISpec W pol.sentinel dAsk dAns ρ L C) (topISpec F) p)
    (hask : ∀ e ev, dAsk e = some ev →
      (∃ h, ev = .accept h) ∨ ev = .acceptAll ∨ ∃ k, ev = .acceptBatch k)
    (hans : ∀ e v ev, dAns e v = some ev →
      (∃ op args r, ev = .write op args r) ∨ ∃ h b, ev = .acceptErr h b)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (handleTraces σ (some .enter) dAsk dAns) ⊆ L := by
  intro x hx
  obtain ⟨t, ⟨p, hp, rfl⟩, s', S, hr, hxS⟩ := mem_lang.1 hx
  obtain ⟨hsn, hwr, -, hacc⟩ := crun_facts_init noR_mono hw ha (wrun_combined hr)
  set ρ := s'.store
  have hgood : ∀ o ∈ p, Move.IsO o →
      MoveGood (storeISpec W pol.sentinel dAsk dAns ρ L C) (topISpec F) o := by
    intro o ho hO
    rcases o with (e | ⟨e, v⟩) | (q | ⟨q, r⟩)
    · simp [Move.IsO] at hO
    · exact fun op args r hd => hwr op args r (mem_map_w.2
        (ans_mem_playEvents (enter := some .enter) (decAsk := dAsk) ho hd))
    · trivial
    · simp [Move.IsO] at hO
  have hP := ag_allP (hAG ρ hsn p hp) hgood
  have hpre : ∀ e, (.inl (.ask e) : Move E F) ∈ p →
      (storeISpec W pol.sentinel dAsk dAns ρ L C).pre e := fun e he => hP _ he trivial
  rcases hacc x hxS with ⟨h, hm, hh⟩ | ⟨hm, op, args, r, hwm, hb⟩
  · rcases hm with hm | hm
    · rcases mem_playEvents (mem_map_w.1 hm) with ⟨e, he, hd⟩ | ⟨e, v, _, hd⟩ | hd
      · exact (hpre e he).1 h hd x hh
      · rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
      · cases hd
    · rcases mem_playEvents (mem_map_w.1 hm) with ⟨e, _, hd⟩ | ⟨e, v, hev, hd⟩ | hd
      · rcases hask e _ hd with ⟨_, h'⟩ | h' | ⟨_, h'⟩ <;> cases h'
      · exact (hpre e (hσ p hp e v hev)).2.1 v h true hd x hh
      · cases hd
  · have hCL : C ⊆ L := by
      rcases hm with hm | hm <;>
      rcases mem_playEvents (mem_map_w.1 hm) with ⟨e, he, hd⟩ | ⟨e, v, _, hd⟩ | hd
      · exact (hpre e he).2.2.2 (.inl hd)
      · rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
      · cases hd
      · exact (hpre e he).2.2.2 (.inr hd)
      · rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
      · cases hd
    refine hCL ?_
    rcases mem_playEvents (mem_map_w.1 hwm) with ⟨e, _, hd⟩ | ⟨e, v, hev, hd⟩ | hd
    · rcases hask e _ hd with ⟨_, h'⟩ | h' | ⟨_, h'⟩ <;> cases h'
    · exact (hpre e (hσ p hp e v hev)).2.2.1 v op args r hd x hb
    · cases hd

/-! ## The decoders -/

variable {ts : List FnType}

theorem consXDecAsk_cases (ix : ConsXImports) (e : (ifaceSig ts).Op) (ev : ConsWEv)
    (h : consXDecAsk ix e = some ev) :
    ((∃ h, ev = .accept h) ∧ ix.accept = some e.1.val) ∨
      (ev = .acceptAll ∧ ix.acceptAll = some e.1.val) ∨
      ((∃ k, ev = .acceptBatch k) ∧ ix.acceptBatch = some e.1.val) := by
  unfold consXDecAsk at h
  split_ifs at h with h1 h2 h3 h4
  · obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .inl ⟨⟨a, rfl⟩, h1⟩
  · cases h
    exact .inr (.inl ⟨rfl, h2⟩)
  · obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .inr (.inr ⟨⟨_, rfl⟩, h4⟩)

theorem consXDecAns_cases (ix : ConsXImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e)
    (ev : ConsWEv) (h : consXDecAns ix e v = some ev) :
    (∃ op args r, ev = .write op args r) ∨ ∃ h b, ev = .acceptErr h b := by
  unfold consXDecAns at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨r, -, h⟩ := h
  split_ifs at h <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    obtain ⟨_, -, rfl⟩ := h <;> first | exact .inl ⟨_, _, _, rfl⟩ | exact .inr ⟨_, _, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants
