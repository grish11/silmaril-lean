module

public import Silmaril.Semantics.Accept.Parse.Defs
public import Silmaril.Semantics.Accept.Host.Thms

/-! # Proofs: parsing sessions — cursor invariant, slices and buffers -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Parse

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Host

universe u v w

variable {V : Type u} {H : Type v} {X : Type w} [DecidableEq H] {pol : PPolicy H} {ρ : Env H X}

theorem drop_append_le {L M : List V} {n k : Nat} (h : n ≤ L.length) :
    (L.drop n ++ M).drop k = (L ++ M).drop (n + k) := by
  rw [← List.drop_drop, List.drop_append_of_le_length h]

/-- Steps leave a live state only from a live state. -/
theorem pstep_live {s s' : PState V} {e : PEv V H} {A : Set (List V × X)}
    (hs : PStep pol ρ s e s' A) (hl : s'.phase = .live) : s.phase = .live := by
  cases hs with
  | ret h _ _ => exact h
  | retBadIgnore h _ _ _ => exact h
  | retBadSessionTrap _ _ _ _ => simp at hl
  | retBadUB _ _ _ _ => simp at hl
  | chaos _ h => rw [h] at hl; cases hl
  | overrunUB _ _ => simp at hl
  | _ => rfl

theorem run_live {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)}
    (hr : (parser pol ρ).Run s t s' A) (hl : s'.phase = .live) : s.phase = .live := by
  induction hr with
  | nil => exact hl
  | cons hs _ ih => exact pstep_live hs (ih hl)

/-- **The cursor invariant** of chunked input: the buffer is the fed input after the consumed
prefix, and the consumed count never exceeds it. -/
theorem run_cursor (ho : pol.onOverrun = .sessionTrap) :
    ∀ {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)},
      (parser pol ρ).Run s t s' A → ChunkOnly t → s'.phase = .live →
      s'.buf = (s.buf ++ fed t).drop (consumed t) ∧ consumed t ≤ (s.buf ++ fed t).length := by
  intro s s' t A hr hc hl
  induction hr with
  | nil => simp [fed, consumed]
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
            simp only [fed, consumed, List.append_assoc] at ih1 ih2 ⊢
            exact ⟨ih1, ih2⟩
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
        simp only [fed, consumed] at ih1 ih2 ⊢
        refine ⟨?_, ?_⟩
        · rw [ih1, drop_append_le hle]
        · simp only [List.length_append, List.length_drop] at ih2 ⊢
          omega

end Silmaril.Proofs.Semantics.Accept.Parse

namespace Silmaril.Proofs.Semantics.Accept.Parse

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Host

universe u v w

variable {V : Type u} {H : Type v} {X : Type w} [DecidableEq H] {pol : PPolicy H} {ρ : Env H X}

omit [DecidableEq H] in
theorem returns_phase {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hR : Returns pol s e w h s') : s'.phase = s.phase := by
  cases e <;> simp only [Returns] at hR
  · obtain ⟨-, -, rfl⟩ := hR; rfl
  · obtain ⟨-, -, rfl⟩ := hR; rfl
  · obtain ⟨-, -, -, rfl⟩ := hR; rfl

omit [DecidableEq H] in
theorem returns_pending {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hR : Returns pol s e w h s') (es : List (PEv V H)) :
    pending pol.doneClears s'.acc es = pending pol.doneClears s.acc (e :: es) := by
  cases e <;> simp only [Returns] at hR
  · obtain ⟨-, -, rfl⟩ := hR; rfl
  · obtain ⟨-, -, rfl⟩ := hR; rfl
  · obtain ⟨-, -, -, rfl⟩ := hR; rfl

theorem run_not_chaos (ho : pol.onOverrun ≠ .ub) (hb : pol.onBadHandle ≠ .ub) :
    ∀ {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)},
      (parser pol ρ).Run s t s' A → s.phase ≠ .chaos → s'.phase ≠ .chaos := by
  intro s s' t A hr hs
  induction hr with
  | nil => exact hs
  | cons hst _ ih =>
      apply ih
      cases hst with
      | ret _ hR _ => rw [returns_phase hR]; exact hs
      | retBadIgnore _ hR _ _ => rw [returns_phase hR]; exact hs
      | retBadSessionTrap _ _ _ _ => simp
      | retBadUB _ _ _ h => exact absurd h hb
      | overrunUB _ h => exact absurd h ho
      | chaos _ h => exact absurd h hs
      | _ => simp

theorem run_pending :
    ∀ {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)},
      (parser pol ρ).Run s t s' A → s'.phase = .live →
      s'.acc = pending pol.doneClears s.acc t := by
  intro s s' t A hr hl
  induction hr with
  | nil => rfl
  | @cons s s₁ s₂ e es A' B hs hrest ih =>
      have hl₁ := run_live hrest hl
      rw [ih hl]
      cases hs with
      | ret _ hR _ => exact returns_pending hR es
      | retBadIgnore _ hR _ _ => exact returns_pending hR es
      | retBadSessionTrap _ _ _ _ => simp at hl₁
      | retBadUB _ _ _ _ => simp at hl₁
      | overrunUB _ _ => simp at hl₁
      | chaos _ h => rw [h] at hl₁; cases hl₁
      | append v => rfl
      | feed c => rfl
      | overrunIgnore _ _ => rfl
      | reset => rfl

/-- Extract the event of a parse relation pair. -/
theorem rel_event {Envs : Set (Env H X)} {T : Set (List (PEv V H))} {p : List V × X}
    (hp : p ∈ parseRel pol Envs T) :
    ∃ ρ ∈ Envs, ∃ t ∈ T, ∃ u e v s₁ s₂ B C, t = u ++ e :: v ∧
      (parser pol ρ).Run PState.init u s₁ B ∧ PStep pol ρ s₁ e s₂ C ∧ p ∈ C := by
  unfold parseRel langOver at hp
  rw [Set.mem_iUnion] at hp
  obtain ⟨⟨ρ, hρ⟩, hp⟩ := hp
  obtain ⟨t, ht, s, A, hr, hpA⟩ := mem_lang.1 hp
  obtain ⟨u, e, v, s₁, s₂, B, C, rfl, hu, he, hpC⟩ :=
    Host.Run.mem_split (h := parser pol ρ) hr hpA
  exact ⟨ρ, hρ, _, ht, u, e, v, s₁, s₂, B, C, rfl, hu, he, hpC⟩

/-- **The accepted input of a chunked `done` is the `used` slice after the cursor.** -/
theorem rel_slice (ho : pol.onOverrun = .sessionTrap) (hb : pol.onBadHandle ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (PEv V H))} (hT : ∀ t ∈ T, ChunkOnly t)
    {p : List V × X} (hp : p ∈ parseRel pol Envs T) :
    ∃ t ∈ T, ∃ u n h v, t = u ++ PEv.finish n h :: v ∧
      p.1 = ((fed u).drop (consumed u)).take n ∧ consumed u + n ≤ (fed u).length ∧
      h ≠ pol.sentinel ∧ ∃ ρ ∈ Envs, ρ h = some p.2 := by
  obtain ⟨ρ, hρ, t, ht, u, e, v, s₁, s₂, B, C, rfl, hu, he, hpC⟩ := rel_event hp
  have hcu : ChunkOnly u := fun e he => hT _ ht e (List.mem_append_left _ he)
  have hnc : s₁.phase ≠ .chaos :=
    run_not_chaos (by rw [ho]; simp) hb hu (by simp [PState.init])
  have hcur := fun hl => run_cursor (pol := pol) ho hu hcu hl
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
        simp only [PState.init, List.nil_append] at hbuf hcons
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
    | overrunUB _ h => rw [ho] at h; cases h
    | chaos _ h => exact absurd h hnc

/-- **The accepted input of `done()` is the pending append buffer.** -/
theorem rel_done (hb : pol.onBadHandle ≠ .ub) (ho : pol.onOverrun ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (PEv V H))} (hT : ∀ t ∈ T, AppendOnly t)
    {p : List V × X} (hp : p ∈ parseRel pol Envs T) :
    ∃ t ∈ T, ∃ u h v, t = u ++ PEv.done h :: v ∧ p.1 = pending pol.doneClears [] u := by
  obtain ⟨ρ, -, t, ht, u, e, v, s₁, s₂, B, C, rfl, hu, he, hpC⟩ := rel_event hp
  have hnc : s₁.phase ≠ .chaos := run_not_chaos ho hb hu (by simp [PState.init])
  rcases hT _ ht e (by simp) with ⟨c, rfl⟩ | ⟨h, rfl⟩
  · cases he with
    | ret _ hR _ => simp [Returns] at hR
    | retBadIgnore _ hR _ _ => simp [Returns] at hR
    | retBadSessionTrap _ hR _ _ => simp [Returns] at hR
    | retBadUB _ hR _ _ => simp [Returns] at hR
    | append _ => simp at hpC
    | chaos _ h => exact absurd h hnc
  · cases he with
    | @ret _ s₂ _ w h' A hlive hR hres =>
        obtain ⟨rfl, rfl, rfl⟩ := hR
        have hacc := run_pending hu hlive
        unfold resolve at hres
        split at hres
        · cases hres; simp at hpC
        · rcases hx : ρ h' with _ | x <;> rw [hx] at hres <;> cases hres
          simp only [Set.mem_singleton_iff] at hpC
          subst hpC
          exact ⟨_, ht, u, h', v, rfl, by simpa [PState.init] using hacc⟩
    | retBadIgnore _ _ _ _ => simp at hpC
    | retBadSessionTrap _ _ _ _ => simp at hpC
    | retBadUB _ _ _ h => exact absurd h hb
    | chaos _ h => exact absurd h hnc

end Silmaril.Proofs.Semantics.Accept.Parse
