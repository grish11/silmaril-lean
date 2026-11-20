module

public import Silmaril.Wasm.Game.HandleAccept.Combined.Defs
public import Silmaril.Semantics.Accept.Handle.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic

/-! # Proofs: the store bridge for combined sessions

The final store of a run of the combined host (no undefined behaviour, trapping reads, a
monotone reader) is a fixed environment in which every answered write and read of the run is
correct and every accepted tree is the meaning of an accepted handle, or (for `acceptAll` and
kept batches) a tree built by a write of the run (`crun_facts`). Instantiating the
assume/guarantee obligation at that environment gives the bridge `combLang_subset_of_AG`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Combined

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Combined Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Host Silmaril.Proofs.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood)

/-! ## Environments -/

section Env

variable {H X : Type}

theorem extends_trans {a b c : Env H X} (h₁ : a.Extends b) (h₂ : b.Extends c) : a.Extends c :=
  fun _ _ h => h₂ (h₁ h)

theorem lookupAll_extends {σ ρ : Env H X} (he : σ.Extends ρ) :
    ∀ {hs : List H} {ts : List X}, σ.lookupAll hs = some ts → ρ.lookupAll hs = some ts
  | [], ts, h => h
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      exact ⟨x, he hx, xs, lookupAll_extends he (hs := hs) hxs, rfl⟩

theorem built_extends {Op : Type} {W : Writer Op X} {σ ρ : Env H X} (he : σ.Extends ρ)
    {op : Op} {args : List H} {t : X} (h : W.built σ op args = some t) :
    W.built ρ op args = some t := by
  unfold Writer.built at h ⊢
  rcases hl : σ.lookupAll args with _ | ts
  · simp [hl] at h
  · rw [hl] at h
    rw [lookupAll_extends he hl]
    exact h

end Env

/-! ## One step -/

variable {Op Q A X : Type} {H : Type} [DecidableEq H]
  {W : Writer Op X} {R : Reader Q A H X} {pol : Policy H}

/-- What one step of the combined host (no UB, trapping reads) says. -/
structure StepFacts (W : Writer Op X) (R : Reader Q A H X) (pol : Policy H) (s : WState H X)
    (e : CEv Op H Q A) (s₁ : WState H X) (S : Set X) : Prop where
  phase : s₁.phase ≠ .chaos
  ext : s.store.Extends s₁.store
  sent : (∀ r, pol.sentinel = some r → s.store r = none) →
    ∀ r, pol.sentinel = some r → s₁.store r = none
  write : ∀ op args r, e = .w (.write op args r) →
    pol.sentinel = some r ∨ ∃ y, W.built s.store op args = some y ∧ s₁.store r = some y
  read : ∀ q a, e = .r q a → R.valid s.store q ∧ R.ok s.store q a
  store : ∀ h y, s₁.store h = some y →
    s.store h = some y ∨ ∃ op args r, e = .w (.write op args r) ∧ W.built s.store op args = some y
  batch : ∀ y ∈ s₁.batch,
    y ∈ s.batch ∨ ∃ op args r, e = .w (.write op args r) ∧ W.built s.store op args = some y
  acc : ∀ x ∈ S, (∃ h, (e = .w (.accept h) ∨ e = .w (.acceptErr h true)) ∧ s.store h = some x) ∨
    ((e = .w .acceptAll ∨ e = .w (.acceptBatch true)) ∧ ((∃ h, s.store h = some x) ∨ x ∈ s.batch))

theorem wstep_facts (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {s s₁ : WState H X}
    {e : WEv Op H} {S : Set X} (hs : WStep W pol none s e s₁ S) (hp : s.phase ≠ .chaos) :
    StepFacts W R pol s (.w e) s₁ S := by
  cases hs with
  | @writeOk σ B op args r t hbt hfr _ =>
      refine ⟨by simp, fun h y hy => ?_, fun hsn r' hr' => ?_, ?_, by simp, fun h y hy => ?_,
        fun y hy => ?_, by simp⟩
      · dsimp only at hy ⊢
        by_cases hh : h = r
        · subst hh
          rcases hfr.2 with hn | ⟨-, ht⟩
          · simp [hn] at hy
          · rw [ht] at hy; cases hy; simp
        · simp [Function.update_of_ne hh, hy]
      · dsimp only at hsn ⊢
        have hne : r' ≠ r := fun h => hfr.1 (h ▸ hr')
        simp [Function.update_of_ne hne, hsn r' hr']
      · rintro op' args' r'' he
        cases he
        exact .inr ⟨t, hbt, by simp⟩
      · by_cases hh : h = r
        · subst hh
          simp only [Function.update_self, Option.some.injEq] at hy
          subst hy
          exact .inr ⟨op, args, h, rfl, hbt⟩
        · simp only [ne_eq, hh, not_false_eq_true, Function.update_of_ne] at hy
          exact .inl hy
      · rcases Set.mem_insert_iff.1 hy with rfl | hy
        · exact .inr ⟨op, args, r, rfl, hbt⟩
        · exact .inl hy
  | @writeFail σ B op args r hsn _ =>
      refine ⟨hp, fun _ _ h => h, fun h => h, ?_, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
      rintro op' args' r' he
      cases he
      exact .inl hsn
  | writeChaos _ hu _ => exact absurd hu hw
  | writeFixed _ _ hfix => cases hfix
  | @acceptOk σ B h t hh =>
      refine ⟨hp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, fun x hx => ?_⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact .inl ⟨h, .inl rfl, hh⟩
  | acceptCallTrap =>
      exact ⟨by simp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
  | acceptSessionTrap =>
      exact ⟨by simp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
  | acceptIgnore =>
      exact ⟨hp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
  | acceptChaos _ hu _ => exact absurd hu ha
  | acceptFixed _ _ hfix => cases hfix
  | @acceptErrOk σ B h t hh =>
      refine ⟨hp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, fun x hx => ?_⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact .inl ⟨h, .inr rfl, hh⟩
  | acceptErrBad =>
      exact ⟨hp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
  | acceptAll =>
      exact ⟨hp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, fun x hx => .inr ⟨.inl rfl, .inl hx⟩⟩
  | acceptBatch k =>
      refine ⟨hp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => by simp at hy, fun x hx => ?_⟩
      cases k
      · simp at hx
      · exact .inr ⟨.inr rfl, .inr hx⟩
  | enter =>
      exact ⟨hp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
  | resume =>
      exact ⟨by simp, fun _ _ h => h, fun h => h, by simp, by simp, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
  | chaos => exact absurd rfl hp

theorem cstep_facts (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {s s₁ : WState H X}
    {e : CEv Op H Q A} {S : Set X} (hs : CStep W R pol .trap s e s₁ S)
    (hp : s.phase ≠ .chaos) : StepFacts W R pol s e s₁ S := by
  cases hs with
  | w hs => exact wstep_facts hw ha hs hp
  | @read σ B q a S' hS haS =>
      refine ⟨by simp, fun _ _ h => h, fun h => h, by simp, ?_, fun h y hy => .inl hy,
        fun y hy => .inl hy, by simp⟩
      rintro q' a' he
      cases he
      unfold answers at hS
      split at hS
      · rename_i hv
        cases hS
        exact ⟨hv, haS⟩
      · simp [badAnswers] at hS
        subst hS
        simp at haS
  | @readChaos σ B q a hS =>
      unfold answers at hS
      split at hS <;> simp [badAnswers] at hS
  | readInChaos => exact absurd rfl hp

/-! ## Runs -/

/-- **What a run of the combined host says about its final store** (no UB, trapping reads,
monotone reader). `Pre` bounds the trees of the initial store and batch. -/
theorem crun_facts (hM : R.Mono) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    ∀ {s s' : WState H X} {t : List (CEv Op H Q A)} {S : Set X},
      (combined W R pol .trap).Run s t s' S → s.phase ≠ .chaos →
      (∀ r, pol.sentinel = some r → s.store r = none) →
      ∀ (Pre : Set X), (∀ h y, s.store h = some y → y ∈ Pre) → s.batch ⊆ Pre →
      s.store.Extends s'.store ∧ (∀ r, pol.sentinel = some r → s'.store r = none) ∧
      (∀ op args r, CEv.w (.write op args r) ∈ t →
        pol.sentinel = some r ∨ ∃ y, W.built s'.store op args = some y ∧ s'.store r = some y) ∧
      (∀ q a, CEv.r q a ∈ t → R.valid s'.store q ∧ R.ok s'.store q a) ∧
      (∀ x ∈ S, (∃ h, (CEv.w (.accept h) ∈ t ∨ CEv.w (.acceptErr h true) ∈ t) ∧
          s'.store h = some x) ∨
        ((CEv.w .acceptAll ∈ t ∨ CEv.w (.acceptBatch true) ∈ t) ∧
          (x ∈ Pre ∨ ∃ op args r, CEv.w (.write op args r) ∈ t ∧
            W.built s'.store op args = some x))) := by
  intro s s' t S hr
  induction hr with
  | nil s =>
      intro _ hsn _ _ _
      exact ⟨fun _ _ h => h, hsn, by simp, by simp, by simp⟩
  | @cons s s₁ s₂ e es S₁ S₂ hs _ ih =>
      intro hp hsn Pre hPre hB
      have F := cstep_facts (R := R) hw ha hs hp
      let Pre' : Set X := Pre ∪ {y | ∃ op args r, e = .w (.write op args r) ∧
        W.built s.store op args = some y}
      have hPre' : ∀ h y, s₁.store h = some y → y ∈ Pre' := fun h y hy => by
        rcases F.store h y hy with hy | hy
        · exact .inl (hPre h y hy)
        · exact .inr hy
      have hB' : s₁.batch ⊆ Pre' := fun y hy => by
        rcases F.batch y hy with hy | hy
        · exact .inl (hB hy)
        · exact .inr hy
      obtain ⟨hext, hsn', hwr, hrd, hacc⟩ := ih F.phase (F.sent hsn) Pre' hPre' hB'
      have hext0 : s.store.Extends s₂.store := extends_trans F.ext hext
      refine ⟨hext0, hsn', fun op args r hm => ?_, fun q a hm => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.1 hm with he | hm
        · rcases F.write op args r he.symm with h | ⟨y, hy, hr⟩
          · exact .inl h
          · exact .inr ⟨y, built_extends hext0 hy, hext hr⟩
        · exact hwr op args r hm
      · rcases List.mem_cons.1 hm with he | hm
        · obtain ⟨hv, hok⟩ := F.read q a he.symm
          exact hM.persist hext0 hv hok
        · exact hrd q a hm
      · rcases hx with hx | hx
        · rcases F.acc x hx with ⟨h, he, hh⟩ | ⟨he, hx'⟩
          · refine .inl ⟨h, ?_, hext0 hh⟩
            rcases he with he | he <;> simp [he]
          · refine .inr ⟨by rcases he with he | he <;> simp [he], ?_⟩
            rcases hx' with ⟨h, hh⟩ | hx'
            · exact .inl (hPre h x hh)
            · exact .inl (hB hx')
        · rcases hacc x hx with ⟨h, hm, hh⟩ | ⟨hm, hx'⟩
          · exact .inl ⟨h, by rcases hm with hm | hm <;> simp [hm], hh⟩
          · refine .inr ⟨by rcases hm with hm | hm <;> simp [hm], ?_⟩
            rcases hx' with (hx' | ⟨op, args, r, he, hy⟩) | ⟨op, args, r, hm, hy⟩
            · exact .inl hx'
            · exact .inr ⟨op, args, r, by simp [he], built_extends hext0 hy⟩
            · exact .inr ⟨op, args, r, List.mem_cons_of_mem _ hm, hy⟩

/-- From the initial state. -/
theorem crun_facts_init (hM : R.Mono) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    {s' : WState H X} {t : List (CEv Op H Q A)} {S : Set X}
    (hr : (combined W R pol .trap).Run WState.init t s' S) :
    (∀ r, pol.sentinel = some r → s'.store r = none) ∧
      (∀ op args r, CEv.w (.write op args r) ∈ t →
        pol.sentinel = some r ∨ ∃ y, W.built s'.store op args = some y ∧ s'.store r = some y) ∧
      (∀ q a, CEv.r q a ∈ t → R.valid s'.store q ∧ R.ok s'.store q a) ∧
      (∀ x ∈ S, (∃ h, (CEv.w (.accept h) ∈ t ∨ CEv.w (.acceptErr h true) ∈ t) ∧
          s'.store h = some x) ∨
        ((CEv.w .acceptAll ∈ t ∨ CEv.w (.acceptBatch true) ∈ t) ∧
          ∃ op args r, CEv.w (.write op args r) ∈ t ∧ W.built s'.store op args = some x)) := by
  obtain ⟨-, hsn, hwr, hrd, hacc⟩ := crun_facts hM hw ha hr (by simp [WState.init])
    (by simp [WState.init, Env.empty]) ∅ (by simp [WState.init, Env.empty])
    (by simp [WState.init])
  refine ⟨hsn, hwr, hrd, fun x hx => ?_⟩
  rcases hacc x hx with h | ⟨hm, hx' | hx'⟩
  · exact .inl h
  · simp at hx'
  · exact .inr ⟨hm, hx'⟩

/-! ## The bridge -/

variable {E F : Sig.{0}}

/-- **The combined store bridge**: if every play of `σ` is assume/guarantee correct for
`combISpec W R pol.sentinel dAsk dAns ρ L` in every environment `ρ` that leaves the sentinel
undefined, asks decode only to `accept` and answers only to writes and reads, then the combined
language (store semantics, trapping reads, no UB, monotone reader) is included in `L`. -/
theorem combLang_subset_of_AG {X Op Q A : Type} {W : Writer Op X}
    {R : Reader Q A (BitVec 32) X} {pol : Policy (BitVec 32)} {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (CEv Op (BitVec 32) Q A)}
    {dAns : (e : E.Op) → E.Ar e → Option (CEv Op (BitVec 32) Q A)}
    (hAG : ∀ ρ : Env (BitVec 32) X, (∀ r, pol.sentinel = some r → ρ r = none) →
      ∀ p ∈ σ, AG (combISpec W R pol.sentinel dAsk dAns ρ L) (topISpec F) p)
    (hask : ∀ e ev, dAsk e = some ev → ∃ h, ev = .w (.accept h))
    (hans : ∀ e v ev, dAns e v = some ev →
      (∃ op args r, ev = .w (.write op args r)) ∨ ∃ q a, ev = .r q a)
    (hM : R.Mono) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    (combined W R pol .trap).lang (handleTraces σ (some (.w .enter)) dAsk dAns) ⊆ L := by
  intro x hx
  obtain ⟨t, ⟨p, hp, rfl⟩, s', S, hr, hxS⟩ := mem_lang.1 hx
  obtain ⟨hsn, hwr, hrd, hacc⟩ := crun_facts_init hM hw ha hr
  have hgood : ∀ o ∈ p, Move.IsO o →
      MoveGood (combISpec W R pol.sentinel dAsk dAns s'.store L) (topISpec F) o := by
    intro o ho hO
    rcases o with (e | ⟨e, v⟩) | (q | ⟨q, r⟩)
    · simp [Move.IsO] at hO
    · exact ⟨fun op args r hd => hwr op args r
          (ans_mem_playEvents (enter := some (.w .enter)) (decAsk := dAsk) ho hd),
        fun q a hd => hrd q a
          (ans_mem_playEvents (enter := some (.w .enter)) (decAsk := dAsk) ho hd)⟩
    · trivial
    · simp [Move.IsO] at hO
  have hP := ag_allP (hAG s'.store hsn p hp) hgood
  rcases hacc x hxS with ⟨h, hm, hh⟩ | ⟨hm, -⟩
  · rcases hm with hm | hm
    · rcases mem_playEvents hm with ⟨e, he, hd⟩ | ⟨e, v, _, hd⟩ | hd
      · exact hP _ he trivial h hd x hh
      · rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
      · cases hd
    · rcases mem_playEvents hm with ⟨e, _, hd⟩ | ⟨e, v, _, hd⟩ | hd
      · obtain ⟨_, h'⟩ := hask e _ hd; cases h'
      · rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
      · cases hd
  · rcases hm with hm | hm <;>
    rcases mem_playEvents hm with ⟨e, _, hd⟩ | ⟨e, v, _, hd⟩ | hd
    all_goals first
      | (obtain ⟨_, h'⟩ := hask e _ hd; cases h')
      | (rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h')
      | cases hd

end Silmaril.Proofs.Wasm.Game.HandleAccept.Combined

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Combined

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Combined
  Silmaril.Accept.Handle

/-! ## The combined cons decoders -/

variable {ts : List FnType}

theorem combDecAsk_isAccept (ix : CombImports) (e : (ifaceSig ts).Op) (ev : ConsCEv)
    (h : combDecAsk ix e = some ev) : ∃ h, ev = .w (.accept h) := by
  unfold combDecAsk at h
  split_ifs at h
  · obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨a, rfl⟩

theorem combDecAns_cases (ix : CombImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e)
    (ev : ConsCEv) (h : combDecAns ix e v = some ev) :
    (∃ op args r, ev = .w (.write op args r)) ∨ ∃ q a, ev = .r q a := by
  unfold combDecAns at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨r, -, h⟩ := h
  split_ifs at h <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h <;>
    obtain ⟨_, -, rfl⟩ := h <;> first | exact .inl ⟨_, _, _, rfl⟩ | exact .inr ⟨_, _, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Combined
