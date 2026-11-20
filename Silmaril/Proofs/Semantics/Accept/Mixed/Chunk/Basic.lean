module

public import Silmaril.Semantics.Accept.Mixed.Chunk.Defs
public import Silmaril.Proofs.Semantics.Accept.Mixed.Basic

/-! # Proofs: chunk mixed sessions, returns along the chunk buffer -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Mixed.Chunk

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Proofs.Semantics.Accept.Mixed

universe u

variable {Op V H X : Type u}

/-- A handle-returning call moves the chunk buffer by `chunkStep`. -/
theorem returns_buf {ppol : PPolicy H} {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hr : Returns ppol s e w h s') : s'.buf = chunkStep s.buf e := by
  cases e with
  | parse v h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | done h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | finish n h' => obtain ⟨hn, -, -, rfl⟩ := hr; simp [chunkStep, hn]
  | append v => exact hr.elim
  | feed c => exact hr.elim
  | reset => exact hr.elim

variable [DecidableEq H]

/-- **A parsing step moves the chunk buffer by `chunkStep`**, outside undefined behaviour. -/
theorem pstep_buf {ppol : PPolicy H} {σ : Env H X} {s s' : PState V} {e : PEv V H}
    {A : Set (List V × X)} (hs : PStep ppol σ s e s' A) (hc : s.phase ≠ .chaos) :
    s'.buf = chunkStep s.buf e := by
  cases hs with
  | ret _ hR _ => exact returns_buf hR
  | retBadIgnore _ hR _ _ => exact returns_buf hR
  | retBadSessionTrap _ hR _ _ => have := returns_buf hR; exact this
  | retBadUB _ hR _ _ => have := returns_buf hR; exact this
  | append v => rfl
  | feed c => rfl
  | overrunIgnore hl _ => simp only [chunkStep]; split <;> first | rfl | omega
  | overrunUB hl _ => simp only [chunkStep]; split <;> first | rfl | omega
  | reset => rfl
  | chaos _ h => exact absurd h hc

variable {W : Writer Op X} {pol : Policy H} {ppol : PPolicy H} {fix : Option (Env H X)}

/-- **Assume/guarantee along the chunk buffer on one run.** -/
theorem run_subset_chunk (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {σ : Env H X} {R : Set (List V × X)} {s s' : MState V H X}
    {t : List (MEv Op V H)} {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run s t s' A)
    (hc : s.ws.phase ≠ .chaos) (hpc : s.ps.phase ≠ .chaos) (hσ : s'.ws.store.Extends σ)
    (hAG : ∀ u e v, t = u ++ .p e :: v → ∀ ps w h ps',
      ps.buf = chunkFold s.ps.buf (parseEvents u) → Returns ppol ps e w h ps' →
      h ≠ ppol.sentinel → ∀ x, σ h = some x → (w, x) ∈ R) : A ⊆ R := by
  induction hr with
  | nil => exact Set.empty_subset _
  | @cons s₀ s₁ s₂ e es A' B' hs hrest ih =>
      have hc₁ := mstep_noChaos hub hs hc
      have hpc₁ := run_psNoChaos hb ho (Host.Run.single (h := mixed W pol ppol fix) hs) hpc
      refine Set.union_subset (fun q hq => ?_) (ih hc₁ hpc₁ hσ fun u e' v he => ?_)
      · obtain ⟨pe, rfl, w, h, ps', hR, hw', hh, hx⟩ := mstep_acc hub hb ho hs hc hpc hq
        have hx' := hσ (run_extends hrest (mstep_extends hs hx))
        have := hAG [] pe es rfl s₀.ps w h ps' (by simp [chunkFold, parseEvents]) hR hh q.2 hx'
        rw [← hw'] at this
        exact this
      · intro ps w h ps' hps
        refine hAG (e :: u) e' v (by rw [he]; rfl) ps w h ps' ?_
        rw [hps]
        cases hs with
        | w => rfl
        | @p ws ps₀ ps₁ pe C hl hp =>
            have := pstep_buf hp hpc
            simp only at this ⊢
            rw [this]
            rfl
        | pChaos h => exact absurd h hc

theorem mixedRel_subset_of_chunkAG (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ t ∈ T, ∀ σ, WritesAgree W pol.sentinel σ t → ∀ u e v, t = u ++ .p e :: v →
      ∀ ps w h ps', ps.buf = chunkFold [] (parseEvents u) → Returns ppol ps e w h ps' →
        h ≠ ppol.sentinel → ∀ x, σ h = some x → (w, x) ∈ R) :
    mixedRel W pol ppol T ⊆ R := by
  intro q hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  have hσ := ext_refl s.ws.store
  exact run_subset_chunk (.inr ⟨hw, ha⟩) hb ho hr (by simp [mixed, MState.init, WState.init])
    (by simp [mixed, MState.init, PState.init]) hσ
    (hAG t ht _ (run_writesAgree (.inr ⟨hw, ha⟩) (fun _ h => by cases h) hr hσ)) hqA

theorem mixedFixedRel_subset_of_chunkAG (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ ρ ∈ Envs, ∀ t ∈ T, WritesAgree W pol.sentinel ρ t → ∀ u e v, t = u ++ .p e :: v →
      ∀ ps w h ps', ps.buf = chunkFold [] (parseEvents u) → Returns ppol ps e w h ps' →
        h ≠ ppol.sentinel → ∀ x, ρ h = some x → (w, x) ∈ R) :
    mixedFixedRel W pol ppol Envs T ⊆ R := by
  intro q hq
  rw [mixedFixedRel, langOver, Set.mem_iUnion] at hq
  obtain ⟨⟨ρ, hρ⟩, hq⟩ := hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  have hσ := run_fixed hr (fun _ _ h => by cases h)
  exact run_subset_chunk (.inl rfl) hb ho hr (by simp [mixed, MState.init, WState.init])
    (by simp [mixed, MState.init, PState.init]) hσ
    (hAG ρ hρ t ht (run_writesAgree (.inl rfl) (fun _ h => (Option.some.inj h).symm) hr hσ)) hqA

end Silmaril.Proofs.Semantics.Accept.Mixed.Chunk
