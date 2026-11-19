module

public import Silmaril.Semantics.Accept.Handle.Defs
public import Silmaril.Semantics.Accept.Host.Thms
import Silmaril.Proofs.Semantics.Accept.Handle.Writer

/-! # Proofs: reading one unused allocation failure as a successful allocation -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

universe u v w

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H] {W : Writer Op X}

/-- The sentinel never denotes a tree in the store semantics. -/
theorem run_sentinel_none {pol : Policy H} {s : H} (hs : pol.sentinel = some s) :
    ∀ {a b : WState H X} {t : List (WEv Op H)} {A : Set X}, (writer W pol).Run a t b A →
      a.store s = none → b.store s = none := by
  intro a b t A hr ha
  induction hr with
  | nil => exact ha
  | cons hst _ ih =>
      apply ih
      cases hst with
      | @writeOk σ B op args r t hb hf _ =>
          have : r ≠ s := fun e => hf.1 (by rw [hs, e])
          simpa [Function.update_of_ne (Ne.symm this)] using ha
      | writeFixed _ _ hfix => cases hfix
      | _ => exact ha

/-- Two stores agree off `s`, the second also denoting `t₀` at `s`. -/
def ExtAt (s : H) (t₀ : X) (a b : WState H X) : Prop :=
  b.store = Function.update a.store s (some t₀) ∧ a.batch ⊆ b.batch ∧ b.phase = a.phase ∧
    a.store s = none

theorem lookupAll_update_of_not_mem {σ : Env H X} {s : H} {t₀ : X} :
    ∀ {args : List H}, s ∉ args →
      Env.lookupAll (Function.update σ s (some t₀)) args = σ.lookupAll args
  | [], _ => rfl
  | a :: args, h => by
      have ha : a ≠ s := fun e => h (e ▸ List.mem_cons_self)
      have hrest : s ∉ args := fun e => h (List.mem_cons_of_mem _ e)
      have := lookupAll_update_of_not_mem (σ := σ) (t₀ := t₀) hrest
      simp only [Env.lookupAll] at this ⊢
      simp only [List.mapM_cons, Function.update_of_ne ha, this]

/-- After the reinterpreted failure, the sentinel-free run follows the sentinel run on events
that neither return nor use `s`, accepting at least as much. -/
theorem run_ext {pol : Policy H} {s : H} (hs : pol.sentinel = some s) (hw : pol.onWrite = .trap)
    {t₀ : X} :
    ∀ {v : List (WEv Op H)} {a a' : WState H X} {A : Set X}, (writer W pol).Run a v a' A →
      NoRet s v → (∀ e ∈ v, s ∉ e.uses) → ∀ {b : WState H X}, ExtAt s t₀ a b →
      ∃ b' B, (writer W {pol with sentinel := none}).Run b v b' B ∧ A ⊆ B := by
  intro v a a' A hr hnr huse
  induction hr with
  | nil a => intro b _; exact ⟨b, ∅, .nil b, le_rfl⟩
  | @cons a a₁ a₂ e es A₁ A₂ hst hrest ih =>
      intro b hab
      obtain ⟨hσ, hB, hp, hsn0⟩ := hab
      have hnr' : NoRet s es := fun op args h => hnr op args (List.mem_cons_of_mem _ h)
      have huse' : ∀ e ∈ es, s ∉ e.uses := fun e h => huse e (List.mem_cons_of_mem _ h)
      have hue : s ∉ e.uses := huse e List.mem_cons_self
      obtain ⟨σ', B', p'⟩ := b
      simp only at hσ hB hp
      subst hσ hp
      cases hst with
      | @writeOk σ B op args r t hb hf _ =>
          have hr : r ≠ s := fun h => hnr op args (h ▸ List.mem_cons_self)
          have hargs : s ∉ args := by simpa [WEv.uses] using hue
          have hb' : W.built (Function.update σ s (some t₀)) op args = some t := by
            rw [Writer.built, lookupAll_update_of_not_mem hargs]; exact hb
          have hf' : Fresh {pol with sentinel := none} (Function.update σ s (some t₀)) r t := by
            refine ⟨by simp, ?_⟩
            simpa [Function.update_of_ne hr] using hf.2
          obtain ⟨b', B, hrun, hAB⟩ := ih hnr' huse' (b := ⟨Function.update (Function.update σ s
              (some t₀)) r (some t), insert t B', .live⟩)
            ⟨(Function.update_comm hr _ _ _).symm, Set.insert_subset_insert hB, rfl,
              by simpa [Function.update_of_ne (Ne.symm hr)] using hsn0⟩
          exact ⟨b', ∅ ∪ B, .cons (.writeOk hb' hf' (fun _ h => by cases h)) hrun,
            Set.union_subset_union le_rfl hAB⟩
      | @writeFail σ B op args r hsn _ =>
          rw [hs] at hsn; cases hsn
          exact absurd List.mem_cons_self (hnr op args)
      | writeChaos _ hu _ => rw [hw] at hu; cases hu
      | writeFixed _ _ hfix => cases hfix
      | @acceptOk σ B h t hh =>
          have hne : h ≠ s := fun e => hue (by simp [WEv.uses, e])
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .live⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.acceptOk (t := t) (by simpa [Function.update_of_ne hne] using hh))
            hrun, Set.union_subset_union le_rfl hAB⟩
      | @acceptCallTrap σ B h hh hp =>
          have hne : h ≠ s := fun e => hue (by simp [WEv.uses, e])
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .aborted⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.acceptCallTrap (by simpa [Function.update_of_ne hne] using hh) hp)
            hrun, Set.union_subset_union le_rfl hAB⟩
      | @acceptSessionTrap σ B h hh hp =>
          have hne : h ≠ s := fun e => hue (by simp [WEv.uses, e])
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .dead⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.acceptSessionTrap (by simpa [Function.update_of_ne hne] using hh)
            hp) hrun, Set.union_subset_union le_rfl hAB⟩
      | @acceptIgnore σ B h hh hp =>
          have hne : h ≠ s := fun e => hue (by simp [WEv.uses, e])
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .live⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.acceptIgnore (by simpa [Function.update_of_ne hne] using hh) hp)
            hrun, Set.union_subset_union le_rfl hAB⟩
      | @acceptChaos σ B h hh hp _ =>
          have hne : h ≠ s := fun e => hue (by simp [WEv.uses, e])
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .chaos⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.acceptChaos (by simpa [Function.update_of_ne hne] using hh) hp rfl)
            hrun, Set.union_subset_union le_rfl hAB⟩
      | acceptFixed _ _ hfix => cases hfix
      | @acceptErrOk σ B h t hh =>
          have hne : h ≠ s := fun e => hue (by simp [WEv.uses, e])
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .live⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.acceptErrOk (t := t) (by simpa [Function.update_of_ne hne] using hh))
            hrun, Set.union_subset_union le_rfl hAB⟩
      | @acceptErrBad σ B h hh =>
          have hne : h ≠ s := fun e => hue (by simp [WEv.uses, e])
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .live⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.acceptErrBad (by simpa [Function.update_of_ne hne] using hh))
            hrun, Set.union_subset_union le_rfl hAB⟩
      | @acceptAll σ B =>
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .live⟩) ⟨rfl, hB, rfl, hsn0⟩
          refine ⟨b', _, .cons .acceptAll hrun, Set.union_subset_union ?_ hAB⟩
          rintro x ⟨h, hx⟩
          by_cases hh : h = s
          · subst hh
            simp only at hsn0
            rw [hsn0] at hx; cases hx
          · exact ⟨h, by simpa [Function.update_of_ne hh] using hx⟩
      | @acceptBatch σ B k =>
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, ∅, .live⟩) ⟨rfl, le_rfl, rfl, hsn0⟩
          refine ⟨b', _, .cons (.acceptBatch k) hrun, Set.union_subset_union ?_ hAB⟩
          cases k <;> simp [hB]
      | @enter σ B =>
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .live⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons .enter hrun, Set.union_subset_union le_rfl hAB⟩
      | @resume σ B =>
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .live⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons .resume hrun, Set.union_subset_union le_rfl hAB⟩
      | chaos e =>
          obtain ⟨b', B₂, hrun, hAB⟩ := ih hnr' huse' (b := ⟨_, B', .chaos⟩) ⟨rfl, hB, rfl, hsn0⟩
          exact ⟨b', _, .cons (.chaos _) hrun, Set.union_subset_union le_rfl hAB⟩

end Silmaril.Proofs.Semantics.Accept.Handle

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

universe u v w

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H] {W : Writer Op X}

theorem run_chaos_transfer {pol pol' : Policy H} :
    ∀ {a b : WState H X} {v : List (WEv Op H)} {A : Set X}, (writer W pol).Run a v b A →
      a.phase = .chaos → (writer W pol').Run a v b A := by
  intro a b v A hr ha
  induction hr with
  | nil => exact .nil _
  | cons hst _ ih =>
      cases hst with
      | chaos _ => exact .cons (.chaos _) (ih rfl)
      | _ => simp at ha

theorem run_noRet_transfer {pol : Policy H} {s : H} (hs : pol.sentinel = some s)
    {a b : WState H X} {u : List (WEv Op H)} {A : Set X} (hu : NoRet s u)
    (hr : (writer W pol).Run a u b A) : (writer W {pol with sentinel := none}).Run a u b A :=
  (Host.Run.congr (h := writer W pol) (h₂ := writer W {pol with sentinel := none})
    (fun e => ∀ op args, e ≠ .write op args s) (fun _ _ _ _ he => wstep_sentinel_iff hs he)
    (fun _ he op args h => hu op args (h ▸ he))).1 hr

/-- **One unused failure reads as a successful allocation**: such a trace accepts no more with
the sentinel than without it. -/
theorem accepts_subset_of_oneFailure {pol : Policy H} {s : H} (hs : pol.sentinel = some s)
    (hw : pol.onWrite = .trap) {t : List (WEv Op H)} (ht : OneUnusedFailure s t) :
    (writer W pol).accepts t ⊆ (writer W {pol with sentinel := none}).accepts t := by
  rintro x ⟨b, A, hr, hx⟩
  rcases ht with hnr | ⟨u, op, args, v, rfl, hu, hv, huse⟩
  · exact ⟨b, A, run_noRet_transfer hs hnr hr, hx⟩
  · obtain ⟨m, B, C, hrun_u, hrest, rfl⟩ := Host.Run.append_inv hr
    have hu' := run_noRet_transfer hs hu hrun_u
    have hm : m.store s = none := run_sentinel_none hs hrun_u rfl
    cases hrest with
    | @cons _ m₁ _ _ _ C₁ C₂ hst hrv =>
        cases hst with
        | writeOk _ hf _ => exact absurd (by rw [hs]) hf.1
        | @writeFail σ Bm _ _ _ _ hc =>
            have hbt : ∃ t₀, W.built σ op args = some t₀ := by
              rcases hc with hc | hc
              · exact Option.isSome_iff_exists.1 hc
              · rw [hw] at hc; cases hc
            obtain ⟨t₀, hb⟩ := hbt
            obtain ⟨b', B', hrun, hAB⟩ := run_ext (t₀ := t₀) hs hw hrv hv huse
              (b := ⟨Function.update σ s (some t₀), insert t₀ Bm, .live⟩)
              ⟨rfl, Set.subset_insert _ _, rfl, hm⟩
            refine ⟨b', B ∪ (∅ ∪ B'), Host.Run.append hu' (.cons (.writeOk hb
              ⟨by simp, .inl hm⟩ (fun _ h => by cases h)) hrun), ?_⟩
            rcases hx with hx | hx | hx
            · exact .inl hx
            · simp at hx
            · exact .inr (.inr (hAB hx))
        | writeChaos _ hu _ => rw [hw] at hu; cases hu
        | writeFixed _ _ hfix => cases hfix
        | chaos e =>
            exact ⟨b, _, Host.Run.append hu' (.cons (.chaos _) (run_chaos_transfer hrv rfl)), hx⟩

theorem writerLang_subset_of_oneFailure {pol : Policy H} {s : H} (hs : pol.sentinel = some s)
    (hw : pol.onWrite = .trap) {T : Set (List (WEv Op H))} (hT : ∀ t ∈ T, OneUnusedFailure s t) :
    writerLang W pol T ⊆ writerLang W {pol with sentinel := none} T := by
  intro x hx
  simp only [writerLang, Host.lang, Set.mem_iUnion] at hx ⊢
  obtain ⟨t, ht, hx⟩ := hx
  exact ⟨t, ht, accepts_subset_of_oneFailure hs hw (hT t ht) hx⟩

end Silmaril.Proofs.Semantics.Accept.Handle
