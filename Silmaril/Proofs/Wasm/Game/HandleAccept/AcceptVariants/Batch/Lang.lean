module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Basic
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.Basic
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Basic

/-!
# Proofs: the batch bridge

* `step_batch`: one step of the writer host (store semantics, no undefined behaviour) whose
  store extends the fixed environment `ρ`, from a state whose batch is included in the ghost
  `g` and whose store denotes only trees of `C`: under the guarantees of `batchGSpec` for the
  event, the step accepts only trees of `L`, and the next batch is included in the moved ghost
  `batchGhost W ρ g ev`.
* `walk`: along the decoded events of a play that is assume/guarantee correct for
  `batchGSpec … ρ L C` from `g`, every answer meeting the assumption, a writer run whose final
  store extends `ρ` accepts only trees of `L`.
* `storeLang_subset_of_gag`, **the batch bridge**: with `ρ` the final store of each run
  (`Silmaril.Wasm.Game.HandleAccept.Combined.crun_facts_init`), which makes every write answer
  meet the assumption, and the empty initial batch.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Combined Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host
  Silmaril.Proofs.Wasm.Game.HandleAccept
open Silmaril.Proofs.Wasm.Game.HandleAccept.Combined (wstep_facts built_extends extends_trans)
open Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants (noR noR_mono wrun_combined mem_map_w)

variable {Op X : Type} {W : Writer Op X} {pol : Policy (BitVec 32)}

/-- **One step along the batch ghost.** -/
theorem step_batch (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    {ρ : Env (BitVec 32) X} {L C g : Set X} {s s₁ : WState (BitVec 32) X}
    {ev : WEv Op (BitVec 32)} {A : Set X}
    (hs : WStep W pol none s ev s₁ A) (hp : s.phase ≠ .chaos)
    (hext : s₁.store.Extends ρ) (hB : s.batch ⊆ g) (hC : ∀ h y, s.store h = some y → y ∈ C)
    (hacc : ∀ h, (ev = .accept h ∨ ev = .acceptErr h true) → ∀ t, ρ h = some t → t ∈ L)
    (hall : ev = .acceptAll → C ⊆ L) (hbat : ev = .acceptBatch true → g ⊆ L)
    (hwr : ∀ op args r, ev = .write op args r → ∀ t, W.built ρ op args = some t → t ∈ C) :
    A ⊆ L ∧ s₁.phase ≠ .chaos ∧ s₁.batch ⊆ batchGhost W ρ g ev ∧
      ∀ h y, s₁.store h = some y → y ∈ C := by
  have hf := wstep_facts (R := noR (BitVec 32) X) hw ha hs hp
  have hsext : s.store.Extends ρ := extends_trans hf.ext hext
  refine ⟨fun x hx => ?_, hf.phase, fun y hy => ?_, fun h y hy => ?_⟩
  · cases hs with
    | acceptOk hh =>
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact hacc _ (.inl rfl) _ (hsext hh)
    | acceptErrOk hh =>
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact hacc _ (.inr rfl) _ (hsext hh)
    | acceptAll =>
      obtain ⟨h, hh⟩ := hx
      exact hall rfl (hC h x hh)
    | acceptBatch k =>
      cases k
      · simp at hx
      · exact hbat rfl (hB hx)
    | chaos => exact absurd rfl hp
    | writeChaos _ hu _ => exact absurd hu hw
    | acceptChaos _ hu _ => exact absurd hu ha
    | writeFixed _ _ hfix => cases hfix
    | acceptFixed _ _ hfix => cases hfix
    | _ => simp at hx
  · cases hs with
    | writeOk hbt _ _ =>
      rcases Set.mem_insert_iff.1 hy with rfl | hy
      · exact Set.mem_union_right _ (built_extends hsext hbt)
      · exact Set.mem_union_left _ (hB hy)
    | writeFail => exact Set.mem_union_left _ (hB hy)
    | acceptBatch k => simp at hy
    | chaos => exact absurd rfl hp
    | writeChaos _ hu _ => exact absurd hu hw
    | acceptChaos _ hu _ => exact absurd hu ha
    | writeFixed _ _ hfix => cases hfix
    | acceptFixed _ _ hfix => cases hfix
    | _ => exact hB hy
  · rcases hf.store h y hy with hy | ⟨op, args, r, he, hb⟩
    · exact hC h y hy
    · cases he
      exact hwr op args r rfl y (built_extends hsext hb)

variable {E F : Sig.{0}} {dAsk : E.Op → Option (WEv Op (BitVec 32))}
  {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))}

/-- **The walk along a play.** -/
theorem walk (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ρ : Env (BitVec 32) X}
    {L C : Set X}
    (hask : ∀ e ev, dAsk e = some ev →
      (∃ h, ev = .accept h) ∨ ev = .acceptAll ∨ ∃ k, ev = .acceptBatch k)
    (hans : ∀ e v ev, dAns e v = some ev →
      (∃ op args r, ev = .write op args r) ∨ ∃ h b, ev = .acceptErr h b) :
    ∀ (p : List (Move E F)) (g : Set X) (s s' : WState (BitVec 32) X) (S : Set X),
      GAG (batchGSpec W pol.sentinel dAsk dAns ρ L C) g p →
      (∀ e v, (.inl (.ans e v) : Move E F) ∈ p → ∀ g',
        (batchGSpec W pol.sentinel dAsk dAns ρ L C).post g' e v) →
      (writer W pol).Run s (playEvents (some .enter) dAsk dAns p) s' S →
      s.phase ≠ .chaos → s'.store.Extends ρ → s.batch ⊆ g →
      (∀ h y, s.store h = some y → y ∈ C) → S ⊆ L := by
  intro p
  induction p with
  | nil =>
    intro g s s' S _ _ hr _ _ _ _
    cases hr
    exact Set.empty_subset _
  | cons m p ih =>
    intro g s s' S hg hpost hr hp hext hB hC
    -- one decoded event, then the rest of the play
    have one : ∀ (o : Option (WEv Op (BitVec 32))) (g' : Set X),
        (∀ ev, o = some ev → g' = batchGhost W ρ g ev) → (o = none → g' = g) →
        (∀ ev, o = some ev →
          (∀ h, (ev = .accept h ∨ ev = .acceptErr h true) → ∀ t, ρ h = some t → t ∈ L) ∧
          (ev = .acceptAll → C ⊆ L) ∧ (ev = .acceptBatch true → g ⊆ L) ∧
          (∀ op args r, ev = .write op args r → ∀ t, W.built ρ op args = some t → t ∈ C)) →
        GAG (batchGSpec W pol.sentinel dAsk dAns ρ L C) g' p →
        (writer W pol).Run s (o.toList ++ playEvents (some .enter) dAsk dAns p) s' S →
        S ⊆ L := by
      intro o g' hsome hnone hok hg' hr'
      obtain ⟨s₁, A, B, h1, h2, rfl⟩ := Run.append_inv hr'
      have hpost' : ∀ e v, (.inl (.ans e v) : Move E F) ∈ p → ∀ g'',
          (batchGSpec W pol.sentinel dAsk dAns ρ L C).post g'' e v :=
        fun e v hm => hpost e v (List.mem_cons_of_mem _ hm)
      rcases o with _ | ev
      · cases h1
        rw [hnone rfl] at hg'
        exact Set.union_subset (Set.empty_subset _)
          (ih g _ s' B hg' hpost' h2 hp hext hB hC)
      · obtain ⟨hacc, hall, hbat, hwr⟩ := hok ev rfl
        rcases h1 with _ | ⟨hst, hnil⟩
        cases hnil
        obtain ⟨hA, hp₁, hB₁, hC₁⟩ := step_batch hw ha hst hp
          (extends_trans (Handle.Run.store_extends h2) hext) hB hC hacc hall hbat hwr
        rw [hsome ev rfl] at hg'
        exact Set.union_subset (Set.union_subset hA (Set.empty_subset _))
          (ih _ s₁ s' B hg' hpost' h2 hp₁ hext hB₁ hC₁)
    rcases m with (e | ⟨e, v⟩) | (q | ⟨q, r⟩)
    · obtain ⟨hpre, hg'⟩ := hg
      refine one (dAsk e) _ (fun ev hd => by simp [batchGSpec, hd]) (fun hd => by
        simp [batchGSpec, hd]) (fun ev hd => ⟨fun h hh t ht => ?_, fun hh => ?_, fun hh => ?_,
          fun op args r hh => ?_⟩) hg' hr
      · rcases hh with rfl | rfl
        · exact hpre.1 h hd t ht
        · rcases hask e _ hd with ⟨_, h'⟩ | h' | ⟨_, h'⟩ <;> cases h'
      · subst hh
        exact hpre.2.2.2.1 hd
      · subst hh
        exact hpre.2.2.2.2 hd
      · subst hh
        rcases hask e _ hd with ⟨_, h'⟩ | h' | ⟨_, h'⟩ <;> cases h'
    · obtain ⟨⟨g₀, -, hpre⟩, hg'⟩ := hg
      have hg'' := hg' (hpost e v List.mem_cons_self g)
      refine one (dAns e v) _ (fun ev hd => by simp [batchGSpec, hd]) (fun hd => by
        simp [batchGSpec, hd]) (fun ev hd => ⟨fun h hh t ht => ?_, fun hh => ?_, fun hh => ?_,
          fun op args r hh => ?_⟩) hg'' hr
      · rcases hh with rfl | rfl
        · rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
        · exact hpre.2.1 v h true hd t ht
      · subst hh
        rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
      · subst hh
        rcases hans e v _ hd with ⟨_, _, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
      · subst hh
        exact hpre.2.2.1 v op args r hd
    · refine one (some .enter) g (fun ev hd => ?_) (fun hd => by cases hd) (fun ev hd => ?_)
        hg hr
      · cases hd
        simp [batchGhost]
      · cases hd
        refine ⟨fun h hh => ?_, fun hh => ?_, fun hh => ?_, fun op args r hh => ?_⟩
        · rcases hh with h' | h' <;> cases h'
        all_goals cases hh
    · refine one none g (fun ev hd => by cases hd) (fun _ => rfl) (fun ev hd => by cases hd)
        hg hr

/-- **The batch bridge.** -/
theorem storeLang_subset_of_gag {L C : Set X} {σ : Strategy E F}
    (hAG : ∀ ρ : Env (BitVec 32) X, (∀ r, pol.sentinel = some r → ρ r = none) →
      ∀ p ∈ σ, GAG (batchGSpec W pol.sentinel dAsk dAns ρ L C) ∅ p)
    (hask : ∀ e ev, dAsk e = some ev →
      (∃ h, ev = .accept h) ∨ ev = .acceptAll ∨ ∃ k, ev = .acceptBatch k)
    (hans : ∀ e v ev, dAns e v = some ev →
      (∃ op args r, ev = .write op args r) ∨ ∃ h b, ev = .acceptErr h b)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (handleTraces σ (some .enter) dAsk dAns) ⊆ L := by
  intro x hx
  obtain ⟨t, ⟨p, hp, rfl⟩, s', S, hr, hxS⟩ := mem_lang.1 hx
  obtain ⟨hsn, hwr, -, -⟩ := crun_facts_init noR_mono hw ha (wrun_combined hr)
  refine walk hw ha hask hans p ∅ _ s' S (hAG s'.store hsn p hp) ?_ hr (by simp [writer,
    WState.init]) (fun _ _ h => h) (by simp [writer, WState.init]) (fun h y hy => by
    simp [writer, WState.init, Env.empty] at hy) hxS
  intro e v hm _ op args r hd
  exact hwr op args r (mem_map_w.2 (ans_mem_playEvents (enter := some .enter)
    (decAsk := dAsk) hm hd))

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch
