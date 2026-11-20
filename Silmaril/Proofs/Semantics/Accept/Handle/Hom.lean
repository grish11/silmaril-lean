module

public import Silmaril.Semantics.Accept.Handle.Defs
public import Silmaril.Semantics.Accept.Host.Thms

/-! # Proofs: writer homomorphisms transport languages -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

universe u v w

variable {Op Op' : Type u} {H : Type v} {X X' : Type w} [DecidableEq H]
variable {W : Writer Op X} {W' : Writer Op' X'} {f : Op → Op'} {g : X → X'}

/-- The store and batch mapped along `g`. -/
def mapSt (g : X → X') (s : WState H X) : WState H X' :=
  ⟨fun h => (s.store h).map g, g '' s.batch, s.phase⟩

omit [DecidableEq H] in
theorem lookupAll_map (σ : Env H X) :
    ∀ args : List H, Env.lookupAll (fun h => (σ h).map g) args = (σ.lookupAll args).map (List.map g)
  | [] => rfl
  | a :: args => by
      have ih := lookupAll_map σ args
      simp only [Env.lookupAll] at ih ⊢
      simp only [List.mapM_cons, ih]
      rcases σ a with _ | x <;> rcases List.mapM σ args with _ | xs <;> simp

omit [DecidableEq H] in
theorem built_map (hW : W.Hom W' f g) (σ : Env H X) (op : Op) (args : List H) :
    W'.built (fun h => (σ h).map g) (f op) args = (W.built σ op args).map g := by
  simp only [Writer.built, lookupAll_map]
  rcases σ.lookupAll args with _ | ts
  · rfl
  · simp [hW.build]

omit [DecidableEq H] in
theorem fresh_map (hg : Function.Injective g) {pol : Policy H} {σ : Env H X} {r : H} {t : X} :
    Fresh pol (fun h => (σ h).map g) r (g t) ↔ Fresh pol σ r t := by
  simp only [Fresh, Option.map_eq_none_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨h1, h2 | ⟨hi, x, hx, hgx⟩⟩
    · exact ⟨h1, .inl h2⟩
    · exact ⟨h1, .inr ⟨hi, by rw [hx, hg hgx]⟩⟩
  · rintro ⟨h1, h2 | ⟨hi, hx⟩⟩
    · exact ⟨h1, .inl h2⟩
    · exact ⟨h1, .inr ⟨hi, t, hx, rfl⟩⟩

theorem update_map (σ : Env H X) (r : H) (t : X) :
    (fun h => (Function.update σ r (some t) h).map g) =
      Function.update (fun h => (σ h).map g) r (some (g t)) := by
  funext h
  by_cases hh : h = r
  · subst hh; simp
  · simp [Function.update_of_ne hh]

omit [DecidableEq H] in
theorem range_map (σ : Env H X) : Env.range (fun h => (σ h).map g) = g '' σ.range := by
  ext y
  simp only [Env.range, Option.map_eq_some_iff, Set.mem_image]
  constructor
  · rintro ⟨h, x, hx, rfl⟩; exact ⟨x, ⟨h, hx⟩, rfl⟩
  · rintro ⟨x, ⟨h, hx⟩, rfl⟩; exact ⟨h, x, hx, rfl⟩

/-- **Forward**: a run maps to a run accepting at least the image. -/
theorem run_hom (hW : W.Hom W' f g) (pol : Policy H) :
    ∀ {s s' : WState H X} {t : List (WEv Op H)} {A : Set X}, (writer W pol).Run s t s' A →
      ∃ B, (writer W' pol).Run (mapSt g s) (t.map (WEv.mapOp f)) (mapSt g s') B ∧ g '' A ⊆ B := by
  intro s s' t A hr
  induction hr with
  | nil s => exact ⟨∅, .nil _, by simp⟩
  | cons hs _ ih =>
      obtain ⟨B, hB, hAB⟩ := ih
      have step : ∀ {s s₁ : WState H X} {e : WEv Op H} {A : Set X}, WStep W pol none s e s₁ A →
          ∃ C, WStep W' pol none (mapSt g s) (WEv.mapOp f e) (mapSt g s₁) C ∧ g '' A ⊆ C := by
        intro s s₁ e A hs
        cases hs with
        | @writeOk σ B op args r t hb hf _ =>
            refine ⟨∅, ?_, by simp⟩
            have := WStep.writeOk (W := W') (pol := pol) (fix := none)
              (σ := fun h => (σ h).map g) (B := g '' B) (op := f op) (args := args) (r := r)
              (t := g t) (by rw [built_map hW, hb]; rfl) ((fresh_map hW.inj).2 hf)
              (fun _ h => by cases h)
            simpa [mapSt, update_map, Set.image_insert_eq, WEv.mapOp] using this
        | writeFail hsn hc =>
            refine ⟨∅, .writeFail hsn ?_, by simp⟩
            rcases hc with hc | hc
            · exact .inl (by rw [built_map hW]; simpa using hc)
            · exact .inr hc
        | writeChaos hb hu _ =>
            exact ⟨_, .writeChaos (by rw [built_map hW, hb]; rfl) hu rfl, Set.subset_univ _⟩
        | writeFixed _ _ hfix => cases hfix
        | @acceptOk σ B h t hh => exact ⟨_, .acceptOk (t := g t) (by simp [hh]), by simp⟩
        | acceptCallTrap h hp => exact ⟨_, .acceptCallTrap (by simp [h]) hp, by simp⟩
        | acceptSessionTrap h hp => exact ⟨_, .acceptSessionTrap (by simp [h]) hp, by simp⟩
        | acceptIgnore h hp => exact ⟨_, .acceptIgnore (by simp [h]) hp, by simp⟩
        | acceptChaos h hp _ =>
            exact ⟨_, .acceptChaos (by simp [h]) hp rfl, Set.subset_univ _⟩
        | acceptFixed _ _ hfix => cases hfix
        | @acceptErrOk σ B h t hh =>
            exact ⟨_, .acceptErrOk (t := g t) (by simp [hh]), by simp⟩
        | acceptErrBad h => exact ⟨_, .acceptErrBad (by simp [h]), by simp⟩
        | acceptAll =>
            refine ⟨_, ?_, le_of_eq (range_map _).symm⟩
            exact .acceptAll
        | @acceptBatch σ B k =>
            refine ⟨if k then g '' B else ∅, ?_, by cases k <;> simp⟩
            have := WStep.acceptBatch (W := W') (pol := pol) (fix := none)
              (σ := fun h => (σ h).map g) (B := g '' B) k
            simpa [mapSt, WEv.mapOp] using this
        | enter => exact ⟨∅, .enter, by simp⟩
        | resume => exact ⟨∅, .resume, by simp⟩
        | chaos e => exact ⟨_, .chaos _, Set.subset_univ _⟩
      obtain ⟨C, hC, hAC⟩ := step hs
      exact ⟨C ∪ B, .cons hC hB, by rw [Set.image_union]; exact Set.union_subset_union hAC hAB⟩

theorem step_hom_inv (hW : W.Hom W' f g) {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) {s : WState H X} {e : WEv Op H} {s₁' : WState H X'} {C : Set X'}
    (hs : WStep W' pol none (mapSt g s) (WEv.mapOp f e) s₁' C) (hc : s.phase ≠ .chaos) :
    ∃ s₁ A, WStep W pol none s e s₁ A ∧ s₁' = mapSt g s₁ ∧ C ⊆ g '' A ∧ s₁.phase ≠ .chaos := by
  obtain ⟨σ, B, p⟩ := s
  cases e with
  | write op args r =>
      simp only [mapSt, WEv.mapOp] at hs
      cases hs with
      | writeOk hb hf _ =>
          rw [built_map hW] at hb
          obtain ⟨t, hb', rfl⟩ := Option.map_eq_some_iff.1 hb
          refine ⟨⟨Function.update σ r (some t), insert t B, .live⟩, ∅,
            .writeOk hb' ((fresh_map hW.inj).1 hf) (fun _ h => by cases h), ?_, by simp, by simp⟩
          simp [mapSt, update_map, Set.image_insert_eq]
      | writeFail hsn hc' =>
          refine ⟨⟨σ, B, .live⟩, ∅, .writeFail hsn ?_, rfl, by simp, by simp⟩
          rcases hc' with hc' | hc'
          · rw [built_map hW] at hc'; exact .inl (by simpa using hc')
          · exact .inr hc'
      | writeChaos _ hu _ => exact absurd hu hw
      | writeFixed _ _ hfix => cases hfix
      | chaos _ => exact absurd rfl hc
  | accept h =>
      simp only [mapSt, WEv.mapOp] at hs
      cases hs with
      | acceptOk hh =>
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hh
          exact ⟨⟨σ, B, .live⟩, {t}, .acceptOk ht, rfl, by simp, by simp⟩
      | acceptCallTrap hh hp =>
          exact ⟨⟨σ, B, .aborted⟩, ∅, .acceptCallTrap (by simpa using hh) hp, rfl, by simp,
            by simp⟩
      | acceptSessionTrap hh hp =>
          exact ⟨⟨σ, B, .dead⟩, ∅, .acceptSessionTrap (by simpa using hh) hp, rfl, by simp,
            by simp⟩
      | acceptIgnore hh hp =>
          exact ⟨⟨σ, B, .live⟩, ∅, .acceptIgnore (by simpa using hh) hp, rfl, by simp, by simp⟩
      | acceptChaos _ hp _ => exact absurd hp ha
      | acceptFixed _ _ hfix => cases hfix
      | chaos _ => exact absurd rfl hc
  | acceptErr h b =>
      simp only [mapSt, WEv.mapOp] at hs
      cases hs with
      | acceptErrOk hh =>
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hh
          exact ⟨⟨σ, B, .live⟩, {t}, .acceptErrOk ht, rfl, by simp, by simp⟩
      | acceptErrBad hh =>
          exact ⟨⟨σ, B, .live⟩, ∅, .acceptErrBad (by simpa using hh), rfl, by simp, by simp⟩
      | chaos _ => exact absurd rfl hc
  | acceptAll =>
      simp only [mapSt, WEv.mapOp] at hs
      cases hs with
      | acceptAll =>
          exact ⟨⟨σ, B, .live⟩, σ.range, .acceptAll, rfl, le_of_eq (range_map σ), by simp⟩
      | chaos _ => exact absurd rfl hc
  | acceptBatch k =>
      simp only [mapSt, WEv.mapOp] at hs
      cases hs with
      | acceptBatch _ =>
          exact ⟨⟨σ, ∅, .live⟩, if k then B else ∅, .acceptBatch k, by simp [mapSt],
            by cases k <;> simp, by simp⟩
      | chaos _ => exact absurd rfl hc
  | enter =>
      simp only [mapSt, WEv.mapOp] at hs
      cases hs with
      | enter => exact ⟨⟨σ, B, .live⟩, ∅, .enter, rfl, by simp, by simp⟩
      | resume => exact ⟨⟨σ, B, .live⟩, ∅, .resume, rfl, by simp, by simp⟩
      | chaos _ => exact absurd rfl hc

/-- **Backward**: without undefined behaviour, a run of the image trace comes from a run
accepting the preimage. -/
theorem run_hom_inv (hW : W.Hom W' f g) {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    ∀ {t : List (WEv Op H)} {s : WState H X} {s'' : WState H X'} {B : Set X'},
      (writer W' pol).Run (mapSt g s) (t.map (WEv.mapOp f)) s'' B → s.phase ≠ .chaos →
      ∃ s' A, (writer W pol).Run s t s' A ∧ B ⊆ g '' A
  | [], s, s'', B, hr, _ => by cases hr; exact ⟨s, ∅, .nil s, by simp⟩
  | e :: es, s, s'', B, hr, hc => by
      cases hr with
      | cons hs hrest =>
          obtain ⟨s₁, A, hA, rfl, hCA, hc₁⟩ := step_hom_inv hW ha hw hs hc
          obtain ⟨s', A', hA', hBA⟩ := run_hom_inv hW ha hw hrest hc₁
          exact ⟨s', A ∪ A', .cons hA hA', by
            rw [Set.image_union]; exact Set.union_subset_union hCA hBA⟩

/-- **Writer homomorphisms transport languages**: the image module accepts the image of the
language; without undefined behaviour, exactly. -/
theorem writerLang_hom_subset (hW : W.Hom W' f g) (pol : Policy H) (T : Set (List (WEv Op H))) :
    g '' writerLang W pol T ⊆ writerLang W' pol (List.map (WEv.mapOp f) '' T) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨t, ht, s, A, hr, hxA⟩ := mem_lang.1 hx
  obtain ⟨B, hB, hAB⟩ := run_hom hW pol hr
  have hinit : mapSt g (writer W pol).init = (writer W' pol).init := by
    simp only [writer, mapSt, WState.init, Env.empty, Option.map_none, Set.image_empty]; rfl
  rw [hinit] at hB
  exact mem_lang.2 ⟨_, ⟨t, ht, rfl⟩, mapSt g s, B, hB, hAB ⟨x, hxA, rfl⟩⟩

theorem writerLang_hom (hW : W.Hom W' f g) {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) (T : Set (List (WEv Op H))) :
    writerLang W' pol (List.map (WEv.mapOp f) '' T) = g '' writerLang W pol T := by
  apply Set.Subset.antisymm _ (writerLang_hom_subset hW pol T)
  intro y hy
  obtain ⟨_, ⟨t, ht, rfl⟩, s'', B, hr, hyB⟩ := mem_lang.1 hy
  have hinit : (writer W' pol).init = mapSt g (WState.init : WState H X) := by
    simp only [writer, mapSt, WState.init, Env.empty, Option.map_none, Set.image_empty]; rfl
  rw [hinit] at hr
  obtain ⟨s', A, hA, hBA⟩ := run_hom_inv hW ha hw hr (by simp [WState.init])
  obtain ⟨x, hxA, rfl⟩ := hBA hyB
  exact ⟨x, mem_lang.2 ⟨t, ht, s', A, hA, hxA⟩, rfl⟩

end Silmaril.Proofs.Semantics.Accept.Handle
