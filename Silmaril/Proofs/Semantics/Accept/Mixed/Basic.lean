module

public import Silmaril.Semantics.Accept.Mixed.Defs
public import Silmaril.Semantics.Accept.Handle.Thms

/-! # Proofs: mixed writer and parsing sessions -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Mixed

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Accept.Host

universe u

variable {Op V H X : Type u}

/-! ## Environments -/

theorem ext_refl (σ : Env H X) : σ.Extends σ := fun _ _ h => h

theorem ext_trans {σ σ' σ'' : Env H X} (h₁ : σ.Extends σ') (h₂ : σ'.Extends σ'') :
    σ.Extends σ'' := fun _ _ h => h₂ (h₁ h)

theorem lookupAll_mono {σ σ' : Env H X} (hσ : σ.Extends σ') :
    ∀ {hs : List H} {ts : List X}, σ.lookupAll hs = some ts → σ'.lookupAll hs = some ts
  | [], ts, h => by simpa [Env.lookupAll] using h
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      exact ⟨x, hσ hx, xs, lookupAll_mono hσ (hs := hs) hxs, rfl⟩

theorem built_mono {W : Writer Op X} {σ σ' : Env H X} (hσ : σ.Extends σ') {op : Op}
    {args : List H} {t : X} (h : W.built σ op args = some t) : W.built σ' op args = some t := by
  unfold Writer.built at h ⊢
  rcases hl : σ.lookupAll args with _ | ts
  · simp [hl] at h
  · rw [hl, Option.bind_some] at h
    rw [lookupAll_mono hσ hl, Option.bind_some, h]

theorem returns_phase {ppol : PPolicy H} {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hr : Returns ppol s e w h s') : s'.phase = s.phase := by
  cases e with
  | parse v h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | done h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | finish n h' => obtain ⟨-, -, -, rfl⟩ := hr; rfl
  | append v => exact hr.elim
  | feed c => exact hr.elim
  | reset => exact hr.elim

variable [DecidableEq H]

theorem extends_update {σ ρ : Env H X} {r : H} {t : X} (hσ : σ.Extends ρ) (hr : ρ r = some t) :
    Env.Extends (Function.update σ r (some t) : Env H X) ρ := by
  intro h x hx
  by_cases hh : h = r
  · subst hh
    simp only [Function.update_self, Option.some.injEq] at hx
    subst hx
    exact hr
  · rw [Function.update_of_ne hh] at hx
    exact hσ hx

theorem resolve_mono {ppol : PPolicy H} {σ σ' : Env H X} (hσ : σ.Extends σ') {w : List V} {h : H}
    {A : Set (List V × X)} (hr : resolve ppol σ w h = some A) : resolve ppol σ' w h = some A := by
  unfold resolve at hr ⊢
  split_ifs at hr ⊢ with hs
  · exact hr
  · rcases hx : σ h with _ | x
    · simp [hx] at hr
    · rw [hx, Option.map_some] at hr
      rw [hσ hx, Option.map_some, hr]

variable {W : Writer Op X} {pol : Policy H} {ppol : PPolicy H} {fix : Option (Env H X)}

/-! ## Persistence -/

theorem mstep_extends {s s' : MState V H X} {e : MEv Op V H} {A : Set (List V × X)}
    (hs : MStep W pol ppol fix s e s' A) : s.ws.store.Extends s'.ws.store := by
  cases hs with
  | w hw => exact Handle.Run.store_extends (Host.Run.single (h := writer W pol fix) hw)
  | p => exact ext_refl _
  | pChaos => exact ext_refl _

theorem run_extends {s s' : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol fix).Run s t s' A) : s.ws.store.Extends s'.ws.store := by
  induction hr with
  | nil => exact ext_refl _
  | cons hs _ ih => exact ext_trans (mstep_extends hs) ih

/-- Under a fixed environment the store stays below it. -/
theorem wstep_fixed {ρ : Env H X} {s s' : WState H X} {e : WEv Op H} {A : Set X}
    (hs : WStep W pol (some ρ) s e s' A) (hρ : s.store.Extends ρ) : s'.store.Extends ρ := by
  cases hs with
  | writeOk _ _ ha => exact extends_update hρ (ha ρ rfl)
  | writeFixed _ _ hfix _ _ hr =>
      cases hfix
      exact extends_update hρ hr
  | _ => exact hρ

theorem run_fixed {ρ : Env H X} {s s' : MState V H X} {t : List (MEv Op V H)}
    {A : Set (List V × X)} (hr : (mixed W pol ppol (some ρ)).Run s t s' A)
    (hρ : s.ws.store.Extends ρ) : s'.ws.store.Extends ρ := by
  induction hr with
  | nil => exact hρ
  | cons hs _ ih =>
      apply ih
      cases hs with
      | w hw => exact wstep_fixed hw hρ
      | p => exact hρ
      | pChaos => exact hρ

/-- A handle defined after a writer step was defined before or was written by it. -/
theorem wstep_store {s s' : WState H X} {e : WEv Op H} {A : Set X} {h : H} {x : X}
    (hs : WStep W pol fix s e s' A) (hx : s'.store h = some x) :
    s.store h = some x ∨ ∃ op args, e = .write op args h := by
  cases hs with
  | @writeOk σ B op args r t _ _ _ =>
      by_cases hh : h = r
      · subst hh; exact .inr ⟨op, args, rfl⟩
      · dsimp only at hx ⊢; rw [Function.update_of_ne hh] at hx; exact .inl hx
  | @writeFixed σ B op args r t ρ _ _ _ _ _ _ =>
      by_cases hh : h = r
      · subst hh; exact .inr ⟨op, args, rfl⟩
      · dsimp only at hx ⊢; rw [Function.update_of_ne hh] at hx; exact .inl hx
  | _ => exact .inl hx

/-! ## No undefined behaviour -/

theorem wstep_noChaos (hub : NoWriterUB pol fix) {s s' : WState H X} {e : WEv Op H} {A : Set X}
    (hs : WStep W pol fix s e s' A) (hc : s.phase ≠ .chaos) : s'.phase ≠ .chaos := by
  cases hs with
  | writeChaos _ hu hf =>
      rcases hub with h | ⟨h, -⟩
      · simp [hf] at h
      · exact absurd hu h
  | acceptChaos _ hu hf =>
      rcases hub with h | ⟨-, h⟩
      · simp [hf] at h
      · exact absurd hu h
  | chaos => exact absurd rfl hc
  | _ => simp

theorem mstep_noChaos (hub : NoWriterUB pol fix) {s s' : MState V H X} {e : MEv Op V H}
    {A : Set (List V × X)} (hs : MStep W pol ppol fix s e s' A) (hc : s.ws.phase ≠ .chaos) :
    s'.ws.phase ≠ .chaos := by
  cases hs with
  | w hw => exact wstep_noChaos hub hw hc
  | p => exact hc
  | pChaos h => exact absurd h hc

theorem run_noChaos (hub : NoWriterUB pol fix) {s s' : MState V H X} {t : List (MEv Op V H)}
    {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run s t s' A) (hc : s.ws.phase ≠ .chaos) :
    s'.ws.phase ≠ .chaos := by
  induction hr with
  | nil => exact hc
  | cons hs _ ih => exact ih (mstep_noChaos hub hs hc)

theorem pstep_noChaos (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {σ : Env H X}
    {s s' : PState V} {e : PEv V H} {A : Set (List V × X)} (hs : PStep ppol σ s e s' A)
    (hc : s.phase ≠ .chaos) : s'.phase ≠ .chaos := by
  cases hs with
  | ret _ hR _ => rw [returns_phase hR]; exact hc
  | retBadIgnore _ hR _ _ => rw [returns_phase hR]; exact hc
  | retBadSessionTrap => simp
  | retBadUB _ _ _ h => exact absurd h hb
  | overrunUB _ h => exact absurd h ho
  | chaos _ h => exact absurd h hc
  | _ => simp

theorem run_psNoChaos (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {s s' : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol fix).Run s t s' A) (hc : s.ps.phase ≠ .chaos) :
    s'.ps.phase ≠ .chaos := by
  induction hr with
  | nil => exact hc
  | cons hs _ ih =>
      apply ih
      cases hs with
      | w => exact hc
      | p _ hp => exact pstep_noChaos hb ho hp hc
      | pChaos => exact hc

/-- **What a step accepts** without undefined behaviour: a pair is accepted only by a parsing
event returning a non-sentinel handle that the current store resolves to its tree. -/
theorem mstep_acc (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {s s' : MState V H X} {e : MEv Op V H} {A : Set (List V × X)}
    (hs : MStep W pol ppol fix s e s' A) (hc : s.ws.phase ≠ .chaos) (hpc : s.ps.phase ≠ .chaos)
    {q : List V × X} (hq : q ∈ A) :
    ∃ pe, e = .p pe ∧ ∃ w h ps', Returns ppol s.ps pe w h ps' ∧ q.1 = w ∧ h ≠ ppol.sentinel ∧
      s.ws.store h = some q.2 := by
  cases hs with
  | w hw => exact absurd hq (wstep_noChaos hub hw hc)
  | pChaos h => exact absurd h hc
  | @p ws ps ps' pe A _ hp =>
      refine ⟨pe, rfl, ?_⟩
      cases hp with
      | @ret _ s' _ w h _ _ hR hres =>
          refine ⟨w, h, _, hR, ?_⟩
          unfold resolve at hres
          split_ifs at hres with hh
          · cases hres; simp at hq
          · rcases hx : ws.store h with _ | x
            · simp [hx] at hres
            · simp only [hx, Option.map_some, Option.some.injEq] at hres
              subst hres
              rw [Set.mem_singleton_iff] at hq
              subst hq
              exact ⟨rfl, hh, rfl⟩
      | retBadUB _ _ _ h => exact absurd h hb
      | overrunUB _ h => exact absurd h ho
      | chaos _ h => exact absurd h hpc
      | _ => simp at hq

/-- **Writes agree with a final environment**: along a run without undefined behaviour, every
write is the sentinel or denotes, in any `σ` extending the final store (and equal to the fixed
environment, if any), the tree it builds there. -/
theorem run_writes (hub : NoWriterUB pol fix) {σ : Env H X} (hfix : ∀ ρ, fix = some ρ → ρ = σ)
    {s s' : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol fix).Run s t s' A) (hc : s.ws.phase ≠ .chaos)
    (hσ : s'.ws.store.Extends σ) :
    ∀ op args r, MEv.w (.write op args r) ∈ t → WriteAgrees W pol.sentinel σ op args r := by
  induction hr with
  | nil => intro _ _ _ h; simp at h
  | @cons s₀ s₁ s₂ e es A' B' hs hrest ih =>
      have h₁ : s₁.ws.store.Extends σ := ext_trans (run_extends hrest) hσ
      intro op args r hm
      rcases List.mem_cons.1 hm with rfl | hm
      · cases hs with
        | w hw =>
            cases hw with
            | writeOk hb _ _ =>
                exact .inr ⟨_, built_mono h₁ (built_mono (Handle.Run.store_extends
                  (Host.Run.single (h := writer W pol fix) (WStep.writeOk hb ‹_› ‹_›))) hb),
                  h₁ (by simp)⟩
            | writeFail hs _ => exact .inl hs
            | writeChaos _ hu hf =>
                rcases hub with h | ⟨h, -⟩
                · simp [hf] at h
                · exact absurd hu h
            | writeFixed _ _ hf hb _ hr =>
                obtain rfl := hfix _ hf
                exact .inr ⟨_, hb, hr⟩
            | chaos => exact absurd rfl hc
      · exact ih (mstep_noChaos hub hs hc) hσ op args r hm

/-! ## Comparison with a parsing session -/

/-- One parsing step in a store, simulated in an extension of it. -/
theorem pstep_mono (hb : ppol.onBadHandle ≠ .ub) {σ₀ σ : Env H X} (hσ : σ₀.Extends σ)
    {q q' : PState V} {e : PEv V H} {A : Set (List V × X)} (hs : PStep ppol σ₀ q e q' A) :
    ∃ q'' B, PStep ppol σ q e q'' B ∧ (q' = q'' ∨ q'.phase = .dead) ∧ A ⊆ B := by
  cases hs with
  | ret hl hR hres => exact ⟨_, _, .ret hl hR (resolve_mono hσ hres), .inl rfl, le_rfl⟩
  | @retBadIgnore _ s' _ w h hl hR hres hp =>
      rcases hx : resolve ppol σ w h with _ | B
      · exact ⟨_, _, .retBadIgnore hl hR hx hp, .inl rfl, le_rfl⟩
      · exact ⟨_, _, .ret hl hR hx, .inl rfl, Set.empty_subset _⟩
  | @retBadSessionTrap _ s' _ w h hl hR hres hp =>
      rcases hx : resolve ppol σ w h with _ | B
      · exact ⟨_, _, .retBadSessionTrap hl hR hx hp, .inl rfl, le_rfl⟩
      · exact ⟨_, _, .ret hl hR hx, .inr rfl, Set.empty_subset _⟩
  | retBadUB _ _ _ h => exact absurd h hb
  | append v => exact ⟨_, _, .append v, .inl rfl, le_rfl⟩
  | feed c => exact ⟨_, _, .feed c, .inl rfl, le_rfl⟩
  | overrunIgnore hl hp => exact ⟨_, _, .overrunIgnore hl hp, .inl rfl, le_rfl⟩
  | overrunUB hl hp => exact ⟨_, _, .overrunUB hl hp, .inl rfl, le_rfl⟩
  | reset => exact ⟨_, _, .reset, .inl rfl, le_rfl⟩
  | chaos e h => exact ⟨_, _, .chaos e h, .inl rfl, le_rfl⟩

theorem pstep_not_dead {σ : Env H X} {q q' : PState V} {e : PEv V H} {A : Set (List V × X)}
    (hs : PStep ppol σ q e q' A) (hd : q.phase = .dead) : False := by
  cases hs with
  | ret hl => rw [hd] at hl; cases hl
  | retBadIgnore hl => rw [hd] at hl; cases hl
  | retBadSessionTrap hl => rw [hd] at hl; cases hl
  | retBadUB hl => rw [hd] at hl; cases hl
  | chaos _ h => rw [hd] at h; cases h
  | _ => cases hd

/-- **A mixed run is a parsing run in any extension of its final store**: its parsing events,
answered in the store current at each event, are answered in `σ` with at least the same pairs. -/
theorem run_parser (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub) {σ : Env H X}
    {s s' : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol fix).Run s t s' A) (hc : s.ws.phase ≠ .chaos)
    (hσ : s'.ws.store.Extends σ) :
    ∀ q : PState V, (s.ps = q ∨ s.ps.phase = .dead) →
      ∃ q' B, (parser ppol σ).Run q (parseEvents t) q' B ∧ A ⊆ B := by
  induction hr with
  | nil => intro q _; exact ⟨q, ∅, .nil q, le_rfl⟩
  | @cons s₀ s₁ s₂ e es A' B' hs hrest ih =>
      have h₁ : s₁.ws.store.Extends σ := ext_trans (run_extends hrest) hσ
      have hc₁ := mstep_noChaos hub hs hc
      intro q hq
      cases hs with
      | w hw =>
          obtain ⟨q', B, hrun, hAB⟩ := ih hc₁ hσ q hq
          refine ⟨q', B, hrun, Set.union_subset (fun x hx => absurd hx hc₁) hAB⟩
      | pChaos h => exact absurd h hc
      | @p ws ps ps' pe C hl hp =>
          rcases hq with rfl | hd
          · obtain ⟨q'', D, hD, hrel, hCD⟩ := pstep_mono hb h₁ hp
            obtain ⟨q', B, hrun, hAB⟩ := ih hc₁ hσ q'' (by simpa using hrel)
            exact ⟨q', D ∪ B, .cons hD hrun, Set.union_subset_union hCD hAB⟩
          · exact (pstep_not_dead hp hd).elim

/-- A pair accepted by a mixed run is accepted by the parsing session of its parsing events in
`σ`. -/
theorem accepts_parser (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub) {σ : Env H X}
    {s : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol fix).Run MState.init t s A) (hσ : s.ws.store.Extends σ)
    {q : List V × X} (hq : q ∈ A) : q ∈ (parser ppol σ).accepts (parseEvents t) := by
  obtain ⟨q', B, hrun, hAB⟩ := run_parser hub hb hr (by simp [MState.init, WState.init]) hσ
    PState.init (.inl rfl)
  exact ⟨q', B, hrun, hAB hq⟩

theorem mixedRel_subset_parseRel (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (T : Set (List (MEv Op V H))) :
    mixedRel W pol ppol T ⊆ parseRel ppol (reachStores W pol ppol T) (parseEvents '' T) := by
  intro q hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  rw [parseRel, langOver, Set.mem_iUnion]
  refine ⟨⟨s.ws.store, t, ht, s, A, hr, rfl⟩, Set.mem_biUnion (Set.mem_image_of_mem _ ht) ?_⟩
  exact accepts_parser (.inr ⟨hw, ha⟩) hb hr (ext_refl _) hqA

theorem mixedFixed_subset_parser (hb : ppol.onBadHandle ≠ .ub) (ρ : Env H X)
    (T : Set (List (MEv Op V H))) :
    (mixed W pol ppol (some ρ)).lang T ⊆ (parser ppol ρ).lang (parseEvents '' T) := by
  intro q hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  refine Set.mem_biUnion (Set.mem_image_of_mem _ ht) ?_
  exact accepts_parser (.inl rfl) hb hr (run_fixed hr (fun _ _ h => by cases h)) hqA

theorem mixedFixedRel_subset_parseRel (hb : ppol.onBadHandle ≠ .ub) (Envs : Set (Env H X))
    (T : Set (List (MEv Op V H))) :
    mixedFixedRel W pol ppol Envs T ⊆ parseRel ppol Envs (parseEvents '' T) := by
  intro q hq
  rw [mixedFixedRel, langOver, Set.mem_iUnion] at hq
  obtain ⟨ρ, hq⟩ := hq
  rw [parseRel, langOver, Set.mem_iUnion]
  exact ⟨ρ, mixedFixed_subset_parser hb ρ.1 T hq⟩

/-! ## Accepted pairs come from constructed trees -/

theorem mstep_store {s s' : MState V H X} {e : MEv Op V H} {A : Set (List V × X)}
    (hs : MStep W pol ppol fix s e s' A) {h : H} {x : X} (hx : s'.ws.store h = some x) :
    s.ws.store h = some x ∨ ∃ op args, e = .w (.write op args h) := by
  cases hs with
  | w hw =>
      rcases wstep_store hw hx with hx | ⟨op, args, rfl⟩
      · exact .inl hx
      · exact .inr ⟨op, args, rfl⟩
  | p => exact .inl hx
  | pChaos => exact .inl hx

theorem run_resolves_gen (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {σ : Env H X} {s s' : MState V H X} {t : List (MEv Op V H)}
    {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run s t s' A)
    (hc : s.ws.phase ≠ .chaos) (hpc : s.ps.phase ≠ .chaos) (hσ : s'.ws.store.Extends σ)
    {q : List V × X} (hq : q ∈ A) :
    ∃ u e v, t = u ++ .p e :: v ∧ ∃ ps w h ps', Returns ppol ps e w h ps' ∧ q.1 = w ∧
      h ≠ ppol.sentinel ∧ σ h = some q.2 ∧
      (s.ws.store h = some q.2 ∨ ∃ op args, MEv.w (.write op args h) ∈ u) := by
  induction hr with
  | nil => simp at hq
  | @cons s₀ s₁ s₂ e es A' B' hs hrest ih =>
      rcases hq with hq | hq
      · obtain ⟨pe, rfl, w, h, ps', hR, hw, hh, hx⟩ := mstep_acc hub hb ho hs hc hpc hq
        exact ⟨[], pe, es, rfl, s₀.ps, w, h, ps', hR, hw, hh,
          hσ (run_extends hrest (mstep_extends hs hx)), .inl hx⟩
      · have hc₁ := mstep_noChaos hub hs hc
        have hpc₁ := run_psNoChaos hb ho (Host.Run.single (h := mixed W pol ppol fix) hs) hpc
        obtain ⟨u, e', v, rfl, ps, w, h, ps', hR, hw, hh, hx, hu⟩ := ih hc₁ hpc₁ hσ hq
        refine ⟨e :: u, e', v, rfl, ps, w, h, ps', hR, hw, hh, hx, ?_⟩
        rcases hu with hu | ⟨op, args, hm⟩
        · rcases mstep_store hs hu with hu | ⟨op, args, rfl⟩
          · exact .inl hu
          · exact .inr ⟨op, args, List.mem_cons_self⟩
        · exact .inr ⟨op, args, List.mem_cons_of_mem _ hm⟩

/-- **Every accepted pair is a returned, constructed tree**: without undefined behaviour, a pair
`q` accepted along a run from the initial state is accepted at a parsing event returning a
non-sentinel handle `h` for the input `q.1`; `h` was returned by an earlier write of the same
trace, and every `σ` extending the final store resolves `h` to `q.2`. -/
theorem run_resolves (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {σ : Env H X} {s : MState V H X} {t : List (MEv Op V H)}
    {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run MState.init t s A)
    (hσ : s.ws.store.Extends σ) {q : List V × X} (hq : q ∈ A) :
    ∃ u e v, t = u ++ .p e :: v ∧ ∃ ps w h ps', Returns ppol ps e w h ps' ∧ q.1 = w ∧
      h ≠ ppol.sentinel ∧ σ h = some q.2 ∧ ∃ op args, MEv.w (.write op args h) ∈ u := by
  obtain ⟨u, e, v, rfl, ps, w, h, ps', hR, hw, hh, hx, hu⟩ := run_resolves_gen hub hb ho hr
    (by simp [MState.init, WState.init]) (by simp [MState.init, PState.init]) hσ hq
  refine ⟨u, e, v, rfl, ps, w, h, ps', hR, hw, hh, hx, ?_⟩
  rcases hu with hu | hu
  · simp [MState.init, WState.init, Env.empty] at hu
  · exact hu

/-! ## Assume/guarantee -/

/-- The writes of a run without undefined behaviour agree with `σ`. -/
theorem run_writesAgree (hub : NoWriterUB pol fix) {σ : Env H X}
    (hfix : ∀ ρ, fix = some ρ → ρ = σ) {s : MState V H X} {t : List (MEv Op V H)}
    {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run MState.init t s A)
    (hσ : s.ws.store.Extends σ) : WritesAgree W pol.sentinel σ t :=
  run_writes hub hfix hr (by simp [MState.init, WState.init]) hσ

/-- **The assume/guarantee composition on one run**: if the writes agreeing with `σ` guarantee
that the returns are related in `σ`, every accepted pair is in `R`. -/
theorem run_subset_of_AG (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {σ : Env H X} (hfix : ∀ ρ, fix = some ρ → ρ = σ)
    {R : Set (List V × X)} {s : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol fix).Run MState.init t s A) (hσ : s.ws.store.Extends σ)
    (hAG : WritesAgree W pol.sentinel σ t → ReturnsIn ppol σ R t) : A ⊆ R := by
  intro q hq
  obtain ⟨u, e, v, rfl, ps, w, h, ps', hR, hw, hh, hx, -⟩ := run_resolves hub hb ho hr hσ hq
  have := hAG (run_writesAgree hub hfix hr hσ) e (by simp) ps w h ps' hR hh q.2 hx
  rw [← hw] at this
  exact this

theorem mixedRel_subset_of_AG (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ t ∈ T, ∀ σ, WritesAgree W pol.sentinel σ t → ReturnsIn ppol σ R t) :
    mixedRel W pol ppol T ⊆ R := by
  intro q hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  exact run_subset_of_AG (.inr ⟨hw, ha⟩) hb ho (fun _ h => by cases h) hr (ext_refl _)
    (hAG t ht _) hqA

theorem mixedFixedRel_subset_of_AG (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))} {R : Set (List V × X)}
    (hAG : ∀ ρ ∈ Envs, ∀ t ∈ T, WritesAgree W pol.sentinel ρ t → ReturnsIn ppol ρ R t) :
    mixedFixedRel W pol ppol Envs T ⊆ R := by
  intro q hq
  rw [mixedFixedRel, langOver, Set.mem_iUnion] at hq
  obtain ⟨⟨ρ, hρ⟩, hq⟩ := hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  exact run_subset_of_AG (.inl rfl) hb ho (fun _ h => (Option.some.inj h).symm) hr
    (run_fixed hr (fun _ _ h => by cases h)) (hAG ρ hρ t ht) hqA

/-- **Pairs of the store semantics are returned, constructed trees.** -/
theorem mixedRel_constructed (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {q : List V × X} (hq : q ∈ mixedRel W pol ppol T) :
    ∃ t ∈ T, ∃ u e v, t = u ++ .p e :: v ∧ ∃ ps w h ps', Returns ppol ps e w h ps' ∧ q.1 = w ∧
      h ≠ ppol.sentinel ∧ ∃ op args, MEv.w (.write op args h) ∈ u := by
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  obtain ⟨u, e, v, he, ps, w, h, ps', hR, hw', hh, -, hu⟩ :=
    run_resolves (.inr ⟨hw, ha⟩) hb ho hr (ext_refl _) hqA
  exact ⟨t, ht, u, e, v, he, ps, w, h, ps', hR, hw', hh, hu⟩

/-- **Pairs over a fixed environment resolve in it.** -/
theorem mixedFixedRel_resolves (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))} {q : List V × X}
    (hq : q ∈ mixedFixedRel W pol ppol Envs T) :
    ∃ ρ ∈ Envs, ∃ t ∈ T, WritesAgree W pol.sentinel ρ t ∧ ∃ u e v, t = u ++ .p e :: v ∧
      ∃ ps w h ps', Returns ppol ps e w h ps' ∧ q.1 = w ∧ h ≠ ppol.sentinel ∧
        ρ h = some q.2 ∧ ∃ op args, MEv.w (.write op args h) ∈ u := by
  rw [mixedFixedRel, langOver, Set.mem_iUnion] at hq
  obtain ⟨⟨ρ, hρ⟩, hq⟩ := hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  have hσ := run_fixed hr (fun _ _ h => by cases h)
  exact ⟨ρ, hρ, t, ht, run_writesAgree (.inl rfl) (fun _ h => (Option.some.inj h).symm) hr hσ,
    run_resolves (.inl rfl) hb ho hr hσ hqA⟩

end Silmaril.Proofs.Semantics.Accept.Mixed
