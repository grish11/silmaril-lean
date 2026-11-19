module

public import Silmaril.Semantics.Accept.Mixed.Stream.Defs
public import Silmaril.Proofs.Semantics.Accept.Mixed.Basic

/-! # Proofs: streaming mixed sessions, returns along the trace -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Mixed.Stream

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Proofs.Semantics.Accept.Mixed

universe u

variable {Op V H X : Type u}

/-! ## The append buffer -/

/-- A handle-returning call moves the append buffer by `accStep`. -/
theorem returns_acc {ppol : PPolicy H} {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hr : Returns ppol s e w h s') : s'.acc = accStep ppol.doneClears s.acc e := by
  cases e with
  | parse v h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | done h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | finish n h' => obtain ⟨-, -, -, rfl⟩ := hr; rfl
  | append v => exact hr.elim
  | feed c => exact hr.elim
  | reset => exact hr.elim

/-- `pending` is the iterated `accStep`. -/
theorem pending_eq_foldl (clears : Bool) :
    ∀ (acc : List V) (t : List (PEv V H)), pending clears acc t = t.foldl (accStep clears) acc
  | _, [] => rfl
  | acc, .append v :: es => pending_eq_foldl clears (acc ++ [v]) es
  | _, .done _ :: es => pending_eq_foldl clears _ es
  | _, .reset :: es => pending_eq_foldl clears [] es
  | acc, .parse _ _ :: es => pending_eq_foldl clears acc es
  | acc, .feed _ :: es => pending_eq_foldl clears acc es
  | acc, .finish _ _ :: es => pending_eq_foldl clears acc es

variable [DecidableEq H]

/-- **A parsing step moves the append buffer by `accStep`**, outside undefined behaviour. -/
theorem pstep_acc {ppol : PPolicy H} {σ : Env H X} {s s' : PState V} {e : PEv V H}
    {A : Set (List V × X)} (hs : PStep ppol σ s e s' A) (hc : s.phase ≠ .chaos) :
    s'.acc = accStep ppol.doneClears s.acc e := by
  cases hs with
  | ret _ hR _ => exact returns_acc hR
  | retBadIgnore _ hR _ _ => exact returns_acc hR
  | retBadSessionTrap _ hR _ _ => have := returns_acc hR; exact this
  | retBadUB _ hR _ _ => have := returns_acc hR; exact this
  | append v => rfl
  | feed c => rfl
  | overrunIgnore _ _ => rfl
  | overrunUB _ _ => rfl
  | reset => rfl
  | chaos _ h => exact absurd h hc

omit [DecidableEq H] in
/-- `StreamRetFrom` read at a decomposition `t = u ++ .p e :: v`: the buffer at `e` is the
pending buffer of the parsing events of `u`. -/
theorem streamRetFrom_at {ppol : PPolicy H} {σ : Env H X} {R : Set (List V × X)} :
    ∀ {acc : List V} {u : List (MEv Op V H)} {e : PEv V H} {v : List (MEv Op V H)},
      StreamRetFrom ppol σ R acc (u ++ .p e :: v) →
      ∀ ps w h ps', ps.acc = pending ppol.doneClears acc (parseEvents u) →
        Returns ppol ps e w h ps' → h ≠ ppol.sentinel → ∀ x, σ h = some x → (w, x) ∈ R
  | _, [], _, _, hS => by simpa [StreamRetFrom, parseEvents, pending] using hS.1
  | acc, .w _ :: u, _, _, hS => by
      simpa [parseEvents] using streamRetFrom_at (acc := acc) (u := u) hS
  | acc, .p e' :: u, _, _, hS => by
      intro ps w h ps' hps
      have := streamRetFrom_at (acc := accStep ppol.doneClears acc e') (u := u) hS.2
      rw [pending_eq_foldl] at hps
      refine this ps w h ps' ?_
      rw [hps, pending_eq_foldl]
      cases e' <;> rfl

/-! ## Accepted pairs -/

variable {W : Writer Op X} {pol : Policy H} {ppol : PPolicy H} {fix : Option (Env H X)}

/-- **Streaming assume/guarantee on one run**: if the returns along the trace, read from the
current append buffer, are related in an extension `σ` of the final store, every accepted pair
is in `R`. -/
theorem run_subset_stream (hub : NoWriterUB pol fix) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {σ : Env H X} {R : Set (List V × X)} {s s' : MState V H X}
    {t : List (MEv Op V H)} {A : Set (List V × X)} (hr : (mixed W pol ppol fix).Run s t s' A)
    (hc : s.ws.phase ≠ .chaos) (hpc : s.ps.phase ≠ .chaos) (hσ : s'.ws.store.Extends σ)
    (hS : StreamRetFrom ppol σ R s.ps.acc t) : A ⊆ R := by
  induction hr with
  | nil => exact Set.empty_subset _
  | @cons s₀ s₁ s₂ e es A' B' hs hrest ih =>
      have hc₁ := mstep_noChaos hub hs hc
      have hpc₁ := run_psNoChaos hb ho (Host.Run.single (h := mixed W pol ppol fix) hs) hpc
      refine Set.union_subset (fun q hq => ?_) (ih hc₁ hpc₁ hσ ?_)
      · obtain ⟨pe, rfl, w, h, ps', hR, hw, hh, hx⟩ := mstep_acc hub hb ho hs hc hpc hq
        have hx' := hσ (run_extends hrest (mstep_extends hs hx))
        have := hS.1 s₀.ps w h ps' rfl hR hh q.2 hx'
        rw [← hw] at this
        exact this
      · cases hs with
        | w => exact hS
        | @p ws ps ps' pe C hl hp =>
            have := pstep_acc hp hpc
            simp only at this ⊢
            rw [this]
            exact hS.2
        | pChaos h => exact absurd h hc

theorem mixedRel_subset_of_streamAG (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ t ∈ T, ∀ σ, WritesAgree W pol.sentinel σ t → StreamReturnsIn ppol σ R t) :
    mixedRel W pol ppol T ⊆ R := by
  intro q hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  have hσ := ext_refl s.ws.store
  exact run_subset_stream (.inr ⟨hw, ha⟩) hb ho hr (by simp [mixed, MState.init, WState.init])
    (by simp [mixed, MState.init, PState.init]) hσ
    (hAG t ht _ (run_writesAgree (.inr ⟨hw, ha⟩) (fun _ h => by cases h) hr hσ)) hqA

theorem mixedFixedRel_subset_of_streamAG (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {Envs : Set (Env H X)} {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ ρ ∈ Envs, ∀ t ∈ T, WritesAgree W pol.sentinel ρ t → StreamReturnsIn ppol ρ R t) :
    mixedFixedRel W pol ppol Envs T ⊆ R := by
  intro q hq
  rw [mixedFixedRel, langOver, Set.mem_iUnion] at hq
  obtain ⟨⟨ρ, hρ⟩, hq⟩ := hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  have hσ := run_fixed hr (fun _ _ h => by cases h)
  exact run_subset_stream (.inl rfl) hb ho hr (by simp [mixed, MState.init, WState.init])
    (by simp [mixed, MState.init, PState.init]) hσ
    (hAG ρ hρ t ht (run_writesAgree (.inl rfl) (fun _ h => (Option.some.inj h).symm) hr hσ)) hqA

end Silmaril.Proofs.Semantics.Accept.Mixed.Stream
