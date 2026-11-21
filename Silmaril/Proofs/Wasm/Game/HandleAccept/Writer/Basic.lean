module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs
public import Silmaril.Semantics.Accept.Handle.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic

/-! # Proofs: writer languages of decoded plays

* `writerLang_subset_of_closed`: without undefined behaviour, if every write of every trace is
  closed in `S`, the writer language is included in `S` (a store invariant).
* `fixedLang_subset_of_AG`: the assume/guarantee bridge for writer APIs in a fixed environment;
  `writerLang_subset_of_AG` for the store semantics, through
  `Silmaril.Accept.Handle.writerLang_subset_fixedLang`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Writers

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Host
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood)

variable {Op X H : Type} [DecidableEq H] {W : Writer Op X}

/-! ## Environments -/

omit [DecidableEq H] in
theorem lookupAll_length {σ : Env H X} :
    ∀ {hs : List H} {ts : List X}, σ.lookupAll hs = some ts → ts.length = hs.length
  | [], ts, h => by simp [Env.lookupAll] at h; subst h; rfl
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨x, -, xs, hxs, rfl⟩ := h
      simp [lookupAll_length (hs := hs) hxs]

omit [DecidableEq H] in
theorem lookupAll_mem {σ : Env H X} :
    ∀ {hs : List H} {ts : List X}, σ.lookupAll hs = some ts → ∀ c ∈ ts, ∃ h, σ h = some c
  | [], ts, h => by simp [Env.lookupAll] at h; subst h; simp
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨h₀, hx⟩
      · exact lookupAll_mem (hs := hs) hxs c hc

omit [DecidableEq H] in
theorem lookupAll_extends {σ ρ : Env H X} (he : σ.Extends ρ) :
    ∀ {hs : List H} {ts : List X}, σ.lookupAll hs = some ts → ρ.lookupAll hs = some ts
  | [], ts, h => h
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      exact ⟨x, he hx, xs, lookupAll_extends he (hs := hs) hxs, rfl⟩

omit [DecidableEq H] in
theorem built_extends {σ ρ : Env H X} (he : σ.Extends ρ) {op : Op} {args : List H} {t : X}
    (h : W.built σ op args = some t) : W.built ρ op args = some t := by
  unfold Writer.built at h ⊢
  rcases hl : σ.lookupAll args with _ | ts
  · simp [hl] at h
  · rw [hl] at h
    rw [lookupAll_extends he hl]
    exact h

/-! ## Closed writes -/

/-- The store invariant of a closed run. -/
def CInv (S : Set X) (s : WState H X) : Prop :=
  s.phase ≠ .chaos ∧ (∀ h y, s.store h = some y → y ∈ S) ∧ s.batch ⊆ S

theorem step_closed {pol : Policy H} (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub)
    {S : Set X} {s s' : WState H X} {e : WEv Op H} {A : Set X}
    (hs : WStep W pol none s e s' A) (hI : CInv S s)
    (hc : ∀ op args r, e = .write op args r → WriteClosed W S op args) :
    CInv S s' ∧ A ⊆ S := by
  obtain ⟨hp, hst, hb⟩ := hI
  cases hs with
  | @writeOk σ B op args r t hbt _ _ =>
      have ht : t ∈ S := by
        unfold Writer.built at hbt
        rcases hl : σ.lookupAll args with _ | ts
        · simp [hl] at hbt
        · rw [hl] at hbt
          refine hc op args r rfl ts t (lookupAll_length hl) hbt fun z hz => ?_
          obtain ⟨h, hh⟩ := lookupAll_mem hl z hz
          exact hst h z hh
      refine ⟨⟨by simp, fun h y hy => ?_, ?_⟩, Set.empty_subset _⟩
      · by_cases hh : h = r
        · subst hh; simp at hy; exact hy ▸ ht
        · simp [Function.update_of_ne hh] at hy; exact hst h y hy
      · exact Set.insert_subset ht hb
  | writeFail => exact ⟨⟨hp, hst, hb⟩, Set.empty_subset _⟩
  | writeChaos _ hu _ => exact absurd hu hw
  | writeFixed _ _ hfix => cases hfix
  | @acceptOk σ B h t hh => exact ⟨⟨hp, hst, hb⟩, by simpa using hst h t hh⟩
  | acceptCallTrap => exact ⟨⟨by simp, hst, hb⟩, Set.empty_subset _⟩
  | acceptSessionTrap => exact ⟨⟨by simp, hst, hb⟩, Set.empty_subset _⟩
  | acceptIgnore => exact ⟨⟨hp, hst, hb⟩, Set.empty_subset _⟩
  | acceptChaos _ hu _ => exact absurd hu ha
  | acceptFixed _ _ hfix => cases hfix
  | @acceptErrOk σ B h t hh => exact ⟨⟨hp, hst, hb⟩, by simpa using hst h t hh⟩
  | acceptErrBad => exact ⟨⟨hp, hst, hb⟩, Set.empty_subset _⟩
  | acceptAll =>
      refine ⟨⟨hp, hst, hb⟩, ?_⟩
      rintro y ⟨h, hh⟩
      exact hst h y hh
  | acceptBatch k =>
      refine ⟨⟨hp, hst, Set.empty_subset _⟩, ?_⟩
      cases k
      · exact Set.empty_subset _
      · exact hb
  | enter => exact ⟨⟨hp, hst, hb⟩, Set.empty_subset _⟩
  | resume => exact ⟨⟨by simp, hst, hb⟩, Set.empty_subset _⟩
  | chaos => exact absurd rfl hp

theorem run_closed {pol : Policy H} (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub)
    {S : Set X} {s s' : WState H X} {t : List (WEv Op H)} {A : Set X}
    (hr : (writer W pol).Run s t s' A) (hI : CInv S s)
    (hc : ∀ op args r, WEv.write op args r ∈ t → WriteClosed W S op args) : A ⊆ S := by
  induction hr with
  | nil => exact Set.empty_subset _
  | cons hs _ ih =>
      obtain ⟨hI', hA⟩ := step_closed ha hw hs hI fun op args r he =>
        hc op args r (he ▸ List.mem_cons_self)
      exact Set.union_subset hA
        (ih hI' fun op args r hm => hc op args r (List.mem_cons_of_mem _ hm))

/-- **Closed writes give a bounded writer language**: without undefined behaviour, if every
write of every trace of `T` is closed in `S`, every accepted tree is in `S`. -/
theorem writerLang_subset_of_closed {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) {S : Set X} {T : Set (List (WEv Op H))}
    (hT : ∀ t ∈ T, ∀ op args r, WEv.write op args r ∈ t → WriteClosed W S op args) :
    writerLang W pol T ⊆ S := by
  intro x hx
  simp only [writerLang, mem_lang] at hx
  obtain ⟨t, ht, s, A, hr, hxA⟩ := hx
  exact run_closed ha hw hr ⟨by simp [writer, WState.init], fun _ _ h => by
    simp [writer, WState.init, Env.empty] at h, by simp [writer, WState.init]⟩ (hT t ht) hxA

/-! ## Fixed environments -/

/-- The invariant of a run in the fixed environment `ρ`. -/
def FInv (ρ : Env H X) (s : WState H X) : Prop :=
  s.phase ≠ .chaos ∧ s.store.Extends ρ ∧ s.batch ⊆ ρ.range

/-- What a write answered in the fixed environment `ρ` returns. -/
def WriteOk (W : Writer Op X) (sent : Option H) (ρ : Env H X) (op : Op) (args : List H)
    (r : H) : Prop :=
  sent = some r ∨ ∃ t, W.built ρ op args = some t ∧ ρ r = some t

/-- Where an accepted tree comes from. -/
def AcceptedBy (ρ : Env H X) (x : X) (e : WEv Op H) : Prop :=
  (∃ h, e = .accept h ∧ ρ h = some x) ∨ (∃ h b, e = .acceptErr h b) ∨ e = .acceptAll ∨
    ∃ k, e = .acceptBatch k

theorem step_fixed {pol : Policy H} {ρ : Env H X} {s s' : WState H X} {e : WEv Op H}
    {A : Set X} (hs : WStep W pol (some ρ) s e s' A) (hI : FInv ρ s) :
    FInv ρ s' ∧ (∀ op args r, e = .write op args r → WriteOk W pol.sentinel ρ op args r) ∧
      ∀ x ∈ A, AcceptedBy ρ x e := by
  obtain ⟨hp, hst, hb⟩ := hI
  cases hs with
  | @writeOk σ B op args r t hbt _ hag =>
      have hr : ρ r = some t := hag ρ rfl
      refine ⟨⟨by simp, fun h y hy => ?_, ?_⟩, ?_, by simp⟩
      · by_cases hh : h = r
        · subst hh; simp at hy; exact hy ▸ hr
        · simp [Function.update_of_ne hh] at hy; exact hst hy
      · exact Set.insert_subset ⟨r, hr⟩ hb
      · rintro op' args' r' he
        cases he
        exact .inr ⟨t, built_extends hst hbt, hr⟩
  | writeFail hsn _ =>
      refine ⟨⟨hp, hst, hb⟩, ?_, by simp⟩
      rintro op' args' r' he
      cases he
      exact .inl hsn
  | writeChaos _ _ hfix => cases hfix
  | @writeFixed σ B op args r t ρ' _ _ hfix hbt _ hr =>
      cases hfix
      refine ⟨⟨by simp, fun h y hy => ?_, ?_⟩, ?_, by simp⟩
      · by_cases hh : h = r
        · subst hh; simp at hy; exact hy ▸ hr
        · simp [Function.update_of_ne hh] at hy; exact hst hy
      · exact Set.insert_subset ⟨r, hr⟩ hb
      · rintro op' args' r' he
        cases he
        exact .inr ⟨t, hbt, hr⟩
  | @acceptOk σ B h t hh =>
      refine ⟨⟨hp, hst, hb⟩, by simp, ?_⟩
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact .inl ⟨h, rfl, hst hh⟩
  | acceptCallTrap => exact ⟨⟨by simp, hst, hb⟩, by simp, by simp⟩
  | acceptSessionTrap => exact ⟨⟨by simp, hst, hb⟩, by simp, by simp⟩
  | acceptIgnore => exact ⟨⟨hp, hst, hb⟩, by simp, by simp⟩
  | acceptChaos _ _ hfix => cases hfix
  | @acceptFixed σ B h ρ' _ _ hfix =>
      cases hfix
      exact ⟨⟨hp, hst, hb⟩, by simp, fun x hx => .inl ⟨h, rfl, hx⟩⟩
  | acceptErrOk => exact ⟨⟨hp, hst, hb⟩, by simp, fun _ _ => .inr (.inl ⟨_, _, rfl⟩)⟩
  | acceptErrBad => exact ⟨⟨hp, hst, hb⟩, by simp, by simp⟩
  | acceptAll => exact ⟨⟨hp, hst, hb⟩, by simp, fun _ _ => .inr (.inr (.inl rfl))⟩
  | acceptBatch k =>
      exact ⟨⟨hp, hst, Set.empty_subset _⟩, by simp, fun _ _ => .inr (.inr (.inr ⟨k, rfl⟩))⟩
  | enter => exact ⟨⟨hp, hst, hb⟩, by simp, by simp⟩
  | resume => exact ⟨⟨by simp, hst, hb⟩, by simp, by simp⟩
  | chaos => exact absurd rfl hp

theorem run_fixed {pol : Policy H} {ρ : Env H X} {s s' : WState H X} {t : List (WEv Op H)}
    {A : Set X} (hr : (writer W pol (some ρ)).Run s t s' A) (hI : FInv ρ s) :
    (∀ op args r, WEv.write op args r ∈ t → WriteOk W pol.sentinel ρ op args r) ∧
      ∀ x ∈ A, ∃ e ∈ t, AcceptedBy ρ x e := by
  induction hr with
  | nil => exact ⟨by simp, by simp⟩
  | cons hs _ ih =>
      obtain ⟨hI', hw, hA⟩ := step_fixed hs hI
      obtain ⟨hw', hA'⟩ := ih hI'
      refine ⟨fun op args r hm => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.1 hm with he | hm
        · exact hw op args r he.symm
        · exact hw' op args r hm
      · rcases hx with hx | hx
        · exact ⟨_, List.mem_cons_self, hA x hx⟩
        · obtain ⟨e, he, h⟩ := hA' x hx
          exact ⟨e, List.mem_cons_of_mem _ he, h⟩

/-! ## The bridge -/

variable {E F : Sig.{0}}

/-- **The writer bridge in a fixed environment**: if every play of `σ` is assume/guarantee
correct for `writerISpec W pol.sentinel dAsk dAns ρ L`, asks decode only to `accept` and
answers only to writes, the writer language of `σ` in `ρ` is included in `L`, for every
policy. -/
theorem fixedLang_subset_of_AG {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {ρ : Env (BitVec 32) X} {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))}
    (hAG : ∀ p ∈ σ, AG (writerISpec W pol.sentinel dAsk dAns ρ L) (topISpec F) p)
    (hask : ∀ e ev, dAsk e = some ev → ∃ h, ev = .accept h)
    (hans : ∀ e v ev, dAns e v = some ev → ∃ op args r, ev = .write op args r) :
    fixedLang W pol {ρ} (handleTraces σ (some .enter) dAsk dAns) ⊆ L := by
  intro x hx
  simp only [fixedLang, langOver, Set.mem_iUnion] at hx
  obtain ⟨⟨ρ', hρ'⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff] at hρ'
  subst ρ'
  obtain ⟨t, ⟨p, hp, rfl⟩, s, A, hr, hxA⟩ := mem_lang.1 hx
  obtain ⟨hwr, hacc⟩ := run_fixed hr ⟨by simp [writer, WState.init],
    fun _ _ h => by simp [writer, WState.init, Env.empty] at h, by simp [writer, WState.init]⟩
  have hgood : ∀ o ∈ p, Move.IsO o →
      MoveGood (writerISpec W pol.sentinel dAsk dAns ρ L) (topISpec F) o := by
    intro o ho hO
    rcases o with (e | ⟨e, v⟩) | (q | ⟨q, r⟩)
    · simp [Move.IsO] at hO
    · exact fun op args r hd =>
        hwr op args r (ans_mem_playEvents (enter := some .enter) (decAsk := dAsk) ho hd)
    · trivial
    · simp [Move.IsO] at hO
  have hP := ag_allP (hAG p hp) hgood
  obtain ⟨ev, hev, hby⟩ := hacc x hxA
  rcases mem_playEvents hev with ⟨e, he, hd⟩ | ⟨e, v, _, hd⟩ | hd
  · obtain ⟨h, rfl⟩ := hask e ev hd
    rcases hby with ⟨h', hh', hρ⟩ | ⟨_, _, hh'⟩ | hh' | ⟨_, hh'⟩ <;> cases hh'
    exact hP _ he trivial h hd x hρ
  · obtain ⟨op, args, r, rfl⟩ := hans e v ev hd
    rcases hby with ⟨_, hh', _⟩ | ⟨_, _, hh'⟩ | hh' | ⟨_, hh'⟩ <;> cases hh'
  · cases hd
    rcases hby with ⟨_, hh', _⟩ | ⟨_, _, hh'⟩ | hh' | ⟨_, hh'⟩ <;> cases hh'

/-- **The writer bridge** (store semantics): without undefined behaviour, if the
assume/guarantee obligation holds in every fixed environment, the writer language is included
in `L`. -/
theorem writerLang_subset_of_AG {X Op : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}
    {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))}
    (hAG : ∀ ρ, ∀ p ∈ σ, AG (writerISpec W pol.sentinel dAsk dAns ρ L) (topISpec F) p)
    (hask : ∀ e ev, dAsk e = some ev → ∃ h, ev = .accept h)
    (hans : ∀ e v ev, dAns e v = some ev → ∃ op args r, ev = .write op args r)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (handleTraces σ (some .enter) dAsk dAns) ⊆ L := by
  intro x hx
  have hx' := writerLang_subset_fixedLang hw ha _ hx
  rw [fixedLang, langOver, Set.mem_iUnion] at hx'
  obtain ⟨⟨ρ, _⟩, hρx⟩ := hx'
  refine fixedLang_subset_of_AG (pol := {pol with onAccept := .ub}) (ρ := ρ) (hAG ρ) hask hans ?_
  simp only [fixedLang, langOver, Set.mem_iUnion]
  exact ⟨⟨ρ, rfl⟩, hρx⟩

/-! ## Writes of decoded traces -/

theorem write_mem_traces {Op : Type} {σ : Strategy E F}
    {dAsk : E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))} {Pw : Op → List (BitVec 32) → Prop}
    (hask : ∀ e op args r, dAsk e ≠ some (.write op args r))
    (hans : ∀ e v op args r, dAns e v = some (.write op args r) → Pw op args) :
    ∀ t ∈ handleTraces σ (some .enter) dAsk dAns, ∀ op args r, WEv.write op args r ∈ t →
      Pw op args := by
  rintro _ ⟨p, -, rfl⟩ op args r hm
  rcases mem_playEvents hm with ⟨e, -, hd⟩ | ⟨e, v, -, hd⟩ | hd
  · exact absurd hd (hask e op args r)
  · exact hans e v op args r hd
  · cases hd

end Silmaril.Proofs.Wasm.Game.HandleAccept.Writers
