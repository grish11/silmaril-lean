module

public import Silmaril.Semantics.Accept.Parse.Cursor.Defs
public import Silmaril.Semantics.Accept.Host.Thms
import Silmaril.Proofs.Semantics.Accept.Parse.Basic

/-! # Proofs: parsing sessions — the effective cursor under every overrun policy -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Parse

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Host

universe u v w

variable {V : Type u} {H : Type v} {X : Type w}

theorem effConsumed_le : ∀ (n : Nat) (t : List (PEv V H)), effConsumed n t ≤ consumed t
  | _, [] => Nat.le_refl _
  | n, .feed c :: es => by
      simp only [effConsumed, consumed]
      exact effConsumed_le _ es
  | n, .finish k _ :: es => by
      simp only [effConsumed, consumed]
      split
      · have := effConsumed_le (n - k) es
        omega
      · have := effConsumed_le n es
        omega
  | n, .parse _ _ :: es => by simpa [effConsumed, consumed] using effConsumed_le n es
  | n, .append _ :: es => by simpa [effConsumed, consumed] using effConsumed_le n es
  | n, .done _ :: es => by simpa [effConsumed, consumed] using effConsumed_le n es
  | n, .reset :: es => by simpa [effConsumed, consumed] using effConsumed_le n es

variable [DecidableEq H] {pol : PPolicy H} {ρ : Env H X}

/-- **The effective cursor invariant**, for every overrun policy. -/
theorem run_cursor_eff :
    ∀ {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)},
      (parser pol ρ).Run s t s' A → ChunkOnly t → s'.phase = .live →
      s'.buf = (s.buf ++ fed t).drop (effConsumed s.buf.length t) ∧
        effConsumed s.buf.length t ≤ (s.buf ++ fed t).length := by
  intro s s' t A hr hc hl
  induction hr with
  | nil => simp [fed, effConsumed]
  | @cons s s₁ s₂ e es A' B hs hrest ih =>
      have hc' : ChunkOnly es := fun e he => hc e (List.mem_cons_of_mem _ he)
      obtain ⟨ih1, ih2⟩ := ih hc' hl
      have hl₁ := run_live hrest hl
      rcases hc e List.mem_cons_self with ⟨c, rfl⟩ | ⟨n, h, rfl⟩
      · cases hs with
        | ret _ hR _ => simp [Returns] at hR
        | retBadIgnore _ hR _ _ => simp [Returns] at hR
        | retBadSessionTrap _ hR _ _ => simp [Returns] at hR
        | retBadUB _ hR _ _ => simp [Returns] at hR
        | feed _ =>
            simp only [fed, effConsumed, List.length_append, List.append_assoc] at ih1 ih2 ⊢
            exact ⟨ih1, ih2⟩
        | chaos _ hch => rw [hch] at hl₁; cases hl₁
      · have hstep : (∃ w h', Returns pol s (.finish n h) w h' s₁) ∨
            (s.buf.length < n ∧ s₁ = s) := by
          cases hs with
          | ret _ hR _ => exact .inl ⟨_, _, hR⟩
          | retBadIgnore _ hR _ _ => exact .inl ⟨_, _, hR⟩
          | retBadSessionTrap _ _ _ _ => simp at hl₁
          | retBadUB _ _ _ _ => simp at hl₁
          | overrunIgnore hlt _ => exact .inr ⟨hlt, rfl⟩
          | overrunUB _ _ => simp at hl₁
          | chaos _ hch => rw [hch] at hl₁; cases hl₁
        rcases hstep with ⟨w, h', hle, -, -, rfl⟩ | ⟨hlt, hss⟩
        · simp only [fed, effConsumed, hle, ↓reduceIte, List.length_drop] at ih1 ih2 ⊢
          refine ⟨?_, ?_⟩
          · rw [ih1, drop_append_le hle]
          · simp only [List.length_append, List.length_drop] at ih2 ⊢
            omega
        · subst hss
          have hn : ¬ n ≤ s₁.buf.length := by omega
          simp only [fed, effConsumed, hn, ↓reduceIte] at ih1 ih2 ⊢
          exact ⟨ih1, ih2⟩

/-- **Under `sessionTrap`, the effective count is the plain count** along live runs. -/
theorem effConsumed_eq_consumed (ho : pol.onOverrun = .sessionTrap) :
    ∀ {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)},
      (parser pol ρ).Run s t s' A → ChunkOnly t → s'.phase = .live →
      effConsumed s.buf.length t = consumed t := by
  intro s s' t A hr hc hl
  induction hr with
  | nil => rfl
  | @cons s s₁ s₂ e es A' B hs hrest ih =>
      have hc' : ChunkOnly es := fun e he => hc e (List.mem_cons_of_mem _ he)
      have ih' := ih hc' hl
      have hl₁ := run_live hrest hl
      rcases hc e List.mem_cons_self with ⟨c, rfl⟩ | ⟨n, h, rfl⟩
      · cases hs with
        | ret _ hR _ => simp [Returns] at hR
        | retBadIgnore _ hR _ _ => simp [Returns] at hR
        | retBadSessionTrap _ hR _ _ => simp [Returns] at hR
        | retBadUB _ hR _ _ => simp [Returns] at hR
        | feed _ =>
            simp only [effConsumed, consumed, List.length_append] at ih' ⊢
            exact ih'
        | chaos _ hch => rw [hch] at hl₁; cases hl₁
      · have hstep : ∃ w h', Returns pol s (.finish n h) w h' s₁ := by
          cases hs with
          | ret _ hR _ => exact ⟨_, _, hR⟩
          | retBadIgnore _ hR _ _ => exact ⟨_, _, hR⟩
          | retBadSessionTrap _ _ _ _ => simp at hl₁
          | retBadUB _ _ _ _ => simp at hl₁
          | overrunIgnore _ hp => rw [ho] at hp; simp at hp
          | overrunUB _ _ => simp at hl₁
          | chaos _ hch => rw [hch] at hl₁; cases hl₁
        obtain ⟨w, h', hle, -, -, rfl⟩ := hstep
        simp only [effConsumed, consumed, hle, ↓reduceIte, List.length_drop] at ih' ⊢
        rw [ih']

/-- **The accepted input of a chunked `done` is the `used` slice after the effective
cursor**, for every overrun policy without undefined behaviour. -/
theorem rel_slice_eff (ho : pol.onOverrun ≠ .ub) (hb : pol.onBadHandle ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (PEv V H))} (hT : ∀ t ∈ T, ChunkOnly t)
    {p : List V × X} (hp : p ∈ parseRel pol Envs T) :
    ∃ t ∈ T, ∃ u n h v, t = u ++ PEv.finish n h :: v ∧
      p.1 = ((fed u).drop (effConsumed 0 u)).take n ∧ effConsumed 0 u + n ≤ (fed u).length ∧
      h ≠ pol.sentinel ∧ ∃ ρ ∈ Envs, ρ h = some p.2 := by
  obtain ⟨ρ, hρ, t, ht, u, e, v, s₁, s₂, B, C, rfl, hu, he, hpC⟩ := rel_event hp
  have hcu : ChunkOnly u := fun e he => hT _ ht e (List.mem_append_left _ he)
  have hnc : s₁.phase ≠ .chaos := run_not_chaos ho hb hu (by simp [PState.init])
  have hcur := fun hl => run_cursor_eff (pol := pol) hu hcu hl
  rcases hT _ ht e (by simp) with ⟨c, rfl⟩ | ⟨n, h, rfl⟩
  · cases he with
    | ret _ hR _ => simp [Returns] at hR
    | retBadIgnore _ hR _ _ => simp [Returns] at hR
    | retBadSessionTrap _ hR _ _ => simp [Returns] at hR
    | retBadUB _ hR _ _ => simp [Returns] at hR
    | feed _ => simp at hpC
    | chaos _ h => exact absurd h hnc
  · cases he with
    | @ret _ s₂ _ w h' A hlive hR hres =>
        obtain ⟨hle, rfl, rfl, rfl⟩ := hR
        obtain ⟨hbuf, hcons⟩ := hcur hlive
        simp only [PState.init, List.nil_append, List.length_nil] at hbuf hcons
        unfold resolve at hres
        split at hres
        · cases hres; simp at hpC
        · rename_i hns
          rcases hx : ρ h' with _ | x <;> rw [hx] at hres <;> cases hres
          simp only [Set.mem_singleton_iff] at hpC
          subst hpC
          refine ⟨_, ht, u, n, h', v, rfl, by rw [hbuf], ?_, hns, ρ, hρ, hx⟩
          rw [hbuf, List.length_drop] at hle
          omega
    | retBadIgnore _ _ _ _ => simp at hpC
    | retBadSessionTrap _ _ _ _ => simp at hpC
    | retBadUB _ _ _ h => exact absurd h hb
    | overrunIgnore _ _ => simp at hpC
    | overrunUB _ h => exact absurd h ho
    | chaos _ h => exact absurd h hnc

end Silmaril.Proofs.Semantics.Accept.Parse
