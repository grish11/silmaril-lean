module

public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.StratThread.Thms
public import Silmaril.Games.DPair.Thms
public import Silmaril.Proofs.Games.Abstract.SessionPair.Sim
public import Silmaril.Proofs.Games.Abstract.SessionPair.Trace
import Silmaril.Proofs.Games.Abstract.SessionPair.Basic
import Silmaril.Proofs.Games.Abstract.SessionPair.Plays
import Mathlib.Data.List.Basic

/-!
# Pairing sessions: infinite plays

For triples without plain traps, `J` is an infinite play of the pairing of two sessions iff its
relabelling `List.map pairMove '' J` is an infinite play of the paired session
(`mem_inf_pair_iff`), and every infinite play of the paired session is a relabelling
(`exists_image_pairMove`).

The infinite plays of a threading are productive streams after an idle run, or traces that return
to idle infinitely often.

* Returning to idle infinitely often transfers along the simulations `fwd` and `bwd`.
* A productive stream: after the last idle point of the pairing (`last_idle`) the running side
  receives all later moves, which are lower moves (`lows_of_never_idle`). The stream of the
  component on that side starts at the half of the last idle point (`comp_stream`), and the other
  side's projection is bounded. Streams are identified through equality of nested infinite traces
  (`isInfPlay_eq_of_subset`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionPair

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.StratObs (callMoves satP)

universe u

variable {E : Sig.{u}}

/-! ## Infinite traces of threadings -/

theorem isInfPlay_image' {α β : Type u} (f : α → β) {I : Set (List α)} (hI : IsInfPlay I) :
    IsInfPlay (List.map f '' I) where
  of_prefix := by
    rintro s _ ⟨t, ht, rfl⟩ hs
    obtain ⟨s', hs', rfl⟩ := exists_of_prefix_map hs
    exact ⟨s', hI.of_prefix ht hs', rfl⟩
  total := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    rcases hI.total hs ht with h | h
    · exact .inl (h.map _)
    · exact .inr (h.map _)
  unbounded k := by
    obtain ⟨s, hs, hk⟩ := hI.unbounded k
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hk⟩

/-- The moves of import calls are lower moves. -/
def callEvs (c : List (Call E)) : List (Ev E) := c.flatMap fun x => [.ask x.1, .ans x.1 x.2]

theorem callMoves_eq {F : Sig.{u}} (c : List (Call E)) :
    (callMoves c : List (Move E F)) = lows (callEvs c) := by
  simp [callMoves, callEvs, lows, List.map_flatMap]

section Comp

variable {S A B : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

theorem unmerge_injective : Function.Injective (unmerge : Move E (sig1 A B) → _) :=
  fun o o' h => by rw [← relMove_unmerge o, h, relMove_unmerge]

theorem map_unmerge_lows (es : List (Ev E)) :
    (lows es : List (Move E (sig1 A B))).map unmerge = lows es := by
  simp [lows, unmerge]

theorem mem_inf_threadS_iff (ht : NoPlainTrap t) {J : Set (List (Move E (sig1 A B)))} :
    J ∈ (threadS t s₀).inf ↔ List.map unmerge '' J ∈ (threadT t s₀).inf := by
  constructor
  · rintro ⟨I, hI, rfl⟩
    have : ∀ p ∈ I, (p.map relMove).map unmerge = p := fun p hp =>
      let ⟨_, hr⟩ := (threadT t s₀).inf_sub hI hp
      map_unmerge_relMove ht hr
    rwa [Set.image_image, Set.image_congr this, Set.image_id']
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Set.image_image]
    simp only [map_relMove_unmerge, Set.image_id']

/-- **A component stream**: an infinite play of a threading that contains the question `a` after
`H` and stays, after it, within lower moves, is the stream play of `H` and `a`. -/
theorem comp_stream {I : Set (List (Move E (sig1 A (B ⊕ PUnit.{u + 1}))))}
    (hI : I ∈ (threadT t s₀).inf) {H : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} {a : A}
    (hY : H ++ [.inr (.ask a)] ∈ I)
    (hb : ∀ p ∈ I, ∃ es, p <+: H ++ .inr (.ask a) :: lows es ∧ H ++ .inr (.ask a) :: lows es ∈ I) :
    ∃ s ω, TRun t.1 (satP t) (.idle s₀) H (.idle s) ∧ ω ∈ t.2.2 s a ∧ I = streamPlay H a ω := by
  obtain ⟨hIi, -, hs | ho⟩ := hI
  · obtain ⟨pre, s, a', ω, hrun, hω, rfl⟩ := hs
    have hX : pre ++ [.inr (.ask a')] ∈ streamPlay pre a' ω :=
      ⟨0, (List.prefix_append_right_inj pre).2 (List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩)⟩
    obtain ⟨k, hk⟩ := hY
    rw [callMoves_eq] at hk
    have l₁ := le_of_prefix_lows hk (fun e h => by cases h)
    obtain ⟨es, hes, -⟩ := hb _ hX
    have l₂ := le_of_prefix_lows hes (fun e h => by cases h)
    have hXY : pre ++ [.inr (.ask a')] = H ++ [.inr (.ask a)] := by
      rcases hIi.total hX ⟨k, by rw [callMoves_eq]; exact hk⟩ with h | h
      · exact h.eq_of_length (by simp; omega)
      · exact (h.eq_of_length (by simp; omega)).symm
    obtain ⟨rfl, h⟩ := List.append_inj hXY (by omega)
    simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq, and_true] at h
    subst h
    exact ⟨s, ω, hrun, hω, rfl⟩
  · exfalso
    obtain ⟨p', hp', hpp, s, hr⟩ := ho _ hY
    obtain ⟨es, hes, -⟩ := hb _ hp'
    obtain ⟨u, rfl⟩ := hpp
    rw [show H ++ .inr (.ask a) :: lows es = (H ++ [.inr (.ask a)]) ++ lows es by simp,
      List.prefix_append_right_inj] at hes
    obtain ⟨es', -, rfl⟩ := exists_of_prefix_map hes
    have hp := hr.pos
    rw [List.append_assoc, Path.append_iff] at hp
    obtain ⟨_, -, hp⟩ := hp
    exact ne_idle_of_ask_lows hp rfl

end Comp

/-! ## The paired session -/

section Pair

variable {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}
  {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})} {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})}
  {s₁ : S₁} {s₂ : S₂}

theorem pm_injective : Function.Injective
    (pm : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂) → Move E (sig1 (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit))) :=
  unmerge_injective.comp pairMove_injective

theorem map_pm_lows (es : List (Ev E)) :
    (lows es : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))).map pm = lows es := by
  simp only [lows, List.map_map]
  rfl

/-- A game-idle play of the pairing runs the paired automaton to an idle state. -/
theorem run_idle_of_path (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))}
    (hq : q ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).toStrategy) (hid : Path .idle q .idle) :
    ∃ σ, TRun (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) (.idle (s₁, s₂)) (q.map pm) (.idle σ) := by
  obtain ⟨y₁, r₁⟩ := (mem_threadS_iff h₁).1 hq.2.1
  obtain ⟨y₂, r₂⟩ := (mem_threadS_iff h₂).1 hq.2.2
  obtain ⟨y, hy, hr⟩ := bwd r₁ r₂ (.idle s₁ s₂ false) hid
  have hp := Path.det (path_of_run hy) hid
  generalize Split.side false q = b at hr
  cases hr with
  | idle => exact ⟨_, hy⟩
  | _ => simp [posOf] at hp

/-- Plays of a pairing whose halves are runs from idle states; the paired run to an idle state. -/
theorem run_idle_of_runs {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} {s : S₁} {y₂ : TSt E S₂ A₂}
    (r₁ : TRun t₁.1 (satP t₁) (.idle s₁) ((Split.halves false q).1.map unmerge) (.idle s))
    (r₂ : TRun t₂.1 (satP t₂) (.idle s₂) ((Split.halves false q).2.map unmerge) y₂)
    (hid : Path .idle q .idle) :
    ∃ s', TRun (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) (.idle (s₁, s₂)) (q.map pm) (.idle (s, s')) := by
  obtain ⟨y, hy, hr⟩ := bwd r₁ r₂ (.idle s₁ s₂ false) hid
  have hp := Path.det (path_of_run hy) hid
  generalize Split.side false q = b at hr
  cases hr with
  | idle => exact ⟨_, hy⟩
  | _ => simp [posOf] at hp

theorem run_idle_of_runs' {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} {s : S₂} {y₁ : TSt E S₁ A₁}
    (r₁ : TRun t₁.1 (satP t₁) (.idle s₁) ((Split.halves false q).1.map unmerge) y₁)
    (r₂ : TRun t₂.1 (satP t₂) (.idle s₂) ((Split.halves false q).2.map unmerge) (.idle s))
    (hid : Path .idle q .idle) :
    ∃ s', TRun (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) (.idle (s₁, s₂)) (q.map pm) (.idle (s', s)) := by
  obtain ⟨y, hy, hr⟩ := bwd r₁ r₂ (.idle s₁ s₂ false) hid
  have hp := Path.det (path_of_run hy) hid
  generalize Split.side false q = b at hr
  cases hr with
  | idle => exact ⟨_, hy⟩
  | _ => simp [posOf] at hp

/-- The halves of a play after its last idle point, on the left. -/
theorem halves_last_inl (qi : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))) (a : A₁)
    (es : List (Ev E)) :
    Split.halves false (qi ++ (.inr (.ask (Sum.inl a)) :: lows es : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))) =
      ((Split.halves false qi).1 ++ .inr (.ask a) :: lows es, (Split.halves false qi).2) := by
  rw [halves_append, halves_ask_inl]; simp

/-- The halves of a play after its last idle point, on the right. -/
theorem halves_last_inr (qi : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))) (a : A₂)
    (es : List (Ev E)) :
    Split.halves false (qi ++ (.inr (.ask (Sum.inr a)) :: lows es : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))) =
      ((Split.halves false qi).1, (Split.halves false qi).2 ++ .inr (.ask a) :: lows es) := by
  rw [halves_append, halves_ask_inr]; simp

/-- After the last idle point of a member of an infinite play that never returns to idle, every
member is a prefix of a member made of that idle point, the question, and lower moves. -/
theorem stuck_form {J : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))} (hJi : IsInfPlay J)
    (hJl : ∀ q ∈ J, Legal q) {q₀ : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} (hq₀ : q₀ ∈ J)
    (hn : ∀ q ∈ J, q₀ <+: q → ¬ Path .idle q .idle) :
    ∃ qi a, Path .idle qi .idle ∧ qi ++ [.inr (.ask a)] ∈ J ∧
      ∀ q ∈ J, ∃ es, q <+: qi ++ .inr (.ask a) :: lows es ∧ qi ++ .inr (.ask a) :: lows es ∈ J := by
  obtain ⟨g, hg⟩ := hJl q₀ hq₀
  have hg0 : g ≠ .idle := fun h => hn q₀ hq₀ (List.prefix_refl _) (h ▸ hg)
  obtain ⟨qi, a, w, rfl, hqi, hnw⟩ := last_idle hg hg0
  have hform : ∀ q ∈ J, qi ++ .inr (.ask a) :: w <+: q →
      ∃ es, q = qi ++ .inr (.ask a) :: lows es := by
    rintro q hq ⟨z, rfl⟩
    obtain ⟨g', hg'⟩ := hJl _ hq
    rw [List.append_assoc, Path.append_iff] at hg'
    obtain ⟨y, hy, hy'⟩ := hg'
    cases Path.det hy hqi
    simp only [List.cons_append] at hy'
    cases hy' with
    | cons hs hp =>
      cases hs
      obtain ⟨es, hes⟩ := lows_of_never_idle (.inl rfl) ⟨_, hp⟩ fun w' hw g'' hg'' => by
        rcases List.prefix_or_prefix_of_prefix hw (List.prefix_append w z) with h | h
        · exact hnw w' h g'' (hqi.append (.cons (.ask a) hg''))
        · rintro rfl
          refine hn (qi ++ .inr (.ask a) :: w') ?_ ?_ (hqi.append (.cons (.ask a) hg''))
          · exact hJi.of_prefix hq (by
              simpa using (List.prefix_append_right_inj (qi ++ [.inr (.ask a)])).2 hw)
          · simpa using (List.prefix_append_right_inj (qi ++ [.inr (.ask a)])).2 h
      exact ⟨es, by simp [hes]⟩
  refine ⟨qi, a, hqi, hJi.of_prefix hq₀ (by simp), fun q hq => ?_⟩
  rcases hJi.total hq hq₀ with h | h
  · obtain ⟨es, hes⟩ := hform _ hq₀ (List.prefix_refl _)
    exact ⟨es, hes ▸ h, hes ▸ hq₀⟩
  · obtain ⟨es, rfl⟩ := hform q hq h
    exact ⟨es, List.prefix_refl _, hq⟩

theorem not_isInfPlay_infL {J : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))} (hJi : IsInfPlay J)
    {n : ℕ} (h : ∀ q ∈ J, (Split.halves false q).1.length ≤ n) : ¬ IsInfPlay (Split.infL J) := by
  rw [Split.isInfPlay_infL_iff hJi]
  intro hk
  obtain ⟨p, hp, hl⟩ := hk (n + 1)
  have := h p hp
  omega

theorem not_isInfPlay_infR {J : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))} (hJi : IsInfPlay J)
    {n : ℕ} (h : ∀ q ∈ J, (Split.halves false q).2.length ≤ n) : ¬ IsInfPlay (Split.infR J) := by
  rw [Split.isInfPlay_infR_iff hJi]
  intro hk
  obtain ⟨p, hp, hl⟩ := hk (n + 1)
  have := h p hp
  omega

theorem map_unmerge_ask {A B : Type u} (L : List (Move E (sig1 A B))) (a : A) (es : List (Ev E)) :
    (L ++ (.inr (.ask a) : Move E (sig1 A B)) :: lows es).map unmerge =
      L.map unmerge ++ (.inr (.ask a) : Move E (sig1 A (B ⊕ PUnit.{u + 1}))) :: lows es := by
  rw [List.map_append, List.map_cons, map_unmerge_lows]; rfl

theorem map_pm_ask (L : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))) (c : A₁ ⊕ A₂)
    (es : List (Ev E)) :
    (L ++ (.inr (.ask c) : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)) :: lows es).map pm =
      L.map pm ++
        (.inr (.ask c) : Move E (sig1 (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1}))) :: lows es := by
  rw [List.map_append, List.map_cons, map_pm_lows]; rfl

/-- **Infinite plays of the pairing are relabelled infinite plays of the paired session.** -/
theorem inf_fwd (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {J : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))}
    (hJ : J ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).inf) :
    List.map pm '' J ∈ (threadT (pairS t₁ t₂) (s₁, s₂)).inf := by
  obtain ⟨hJi, hJp, hL, hR⟩ := hJ
  have hKi := isInfPlay_image' pm hJi
  refine ⟨hKi, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have := (mem_pair_iff h₁ h₂).1 (hJp hq)
    rw [mem_threadS_iff (noPlainTrap_pairS h₁ h₂), map_pm] at this
    exact this
  by_cases hof : ∀ q ∈ J, ∃ q' ∈ J, q <+: q' ∧ Path .idle q' .idle
  · refine .inr ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨q', hq', hqq, hid⟩ := hof q hq
    obtain ⟨σ, hσ⟩ := run_idle_of_path h₁ h₂ (hJp hq') hid
    exact ⟨_, ⟨q', hq', rfl⟩, hqq.map _, σ, hσ⟩
  refine .inl ?_
  simp only [not_forall, not_exists, not_and] at hof
  obtain ⟨q₀, hq₀, hn⟩ := hof
  obtain ⟨qi, c, hqi, hc, hform⟩ := stuck_form hJi (fun q hq => (hJp hq).1) hq₀ hn
  have hqiJ : qi ∈ J := hJi.of_prefix hc (List.prefix_append _ _)
  have hsub : ∀ {I : Set (List (Move E (sig1 (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1}))))},
      IsInfPlay I → I ⊆ List.map pm '' J → List.map pm '' J = I := fun hI hs =>
    (isInfPlay_eq_of_subset hKi hI hs).symm
  rcases c with a | a
  · have hbR : ¬ IsInfPlay (Split.infR J) :=
      not_isInfPlay_infR hJi (n := (Split.halves false qi).2.length) fun q hq => by
        obtain ⟨es, hqe, -⟩ := hform q hq
        have := ((Split.halves_prefix hqe false).2).length_le
        rwa [halves_last_inl] at this
    have hI := (mem_inf_threadS_iff h₁).1 (hL ((Split.isInfPlay_infL_or_infR hJi).resolve_right hbR))
    have hmem : ∀ es, qi ++ .inr (.ask (Sum.inl a)) :: lows es ∈ J →
        (Split.halves false qi).1.map unmerge ++ (.inr (.ask a) : Move E (sig1 A₁ (B₁ ⊕ PUnit.{u + 1}))) :: lows es ∈
          List.map unmerge '' Split.infL J := fun es he =>
      ⟨(Split.halves false qi).1 ++ .inr (.ask a) :: lows es,
        ⟨_, he, by rw [halves_last_inl]; exact List.prefix_refl _⟩, map_unmerge_ask _ _ _⟩
    obtain ⟨s, ω, hrun, hω, hIeq⟩ := comp_stream hI (hmem [] hc) (fun p hp => by
      obtain ⟨r, ⟨q, hq, hr⟩, rfl⟩ := hp
      obtain ⟨es, hqe, hJe⟩ := hform q hq
      refine ⟨es, ?_, hmem es hJe⟩
      have h := (Split.halves_prefix hqe false).1
      rw [halves_last_inl] at h
      have h' := (hr.trans h).map unmerge
      rwa [map_unmerge_ask] at h')
    obtain ⟨y₂, r₂⟩ := (mem_threadS_iff h₂).1 (hJp hqiJ).2.2
    obtain ⟨s', hs'⟩ := run_idle_of_runs hrun r₂ hqi
    refine ⟨qi.map pm, (s, s'), Sum.inl a, ω, hs', hω, hsub (isInfPlay_streamPlay _ _ _) ?_⟩
    rintro p ⟨k, hk⟩
    have hmI : (Split.halves false qi).1.map unmerge ++ (.inr (.ask a) : Move E (sig1 A₁ (B₁ ⊕ PUnit.{u + 1}))) ::
        callMoves (streamTake ω k) ∈ List.map unmerge '' Split.infL J :=
      hIeq ▸ ⟨k, List.prefix_refl _⟩
    rw [callMoves_eq] at hmI
    obtain ⟨r, ⟨q, hq, hr⟩, hre⟩ := hmI
    obtain ⟨es, hqe, hJe⟩ := hform q hq
    have h := (Split.halves_prefix hqe false).1
    rw [halves_last_inl] at h
    have h' := (hr.trans h).map unmerge
    rw [hre, map_unmerge_ask, List.prefix_append_right_inj, List.cons_prefix_cons] at h'
    have hce := prefix_of_map_prefix Sum.inl_injective h'.2
    have hq' : qi ++ .inr (.ask (Sum.inl a)) :: lows (callEvs (streamTake ω k)) ∈ J :=
      hJi.of_prefix hJe ((List.prefix_append_right_inj qi).2
        (List.cons_prefix_cons.2 ⟨rfl, hce.map _⟩))
    refine hKi.of_prefix ⟨_, hq', rfl⟩ ?_
    rw [map_pm_ask, ← callMoves_eq]
    exact hk
  · have hbL : ¬ IsInfPlay (Split.infL J) :=
      not_isInfPlay_infL hJi (n := (Split.halves false qi).1.length) fun q hq => by
        obtain ⟨es, hqe, -⟩ := hform q hq
        have := ((Split.halves_prefix hqe false).1).length_le
        rwa [halves_last_inr] at this
    have hI := (mem_inf_threadS_iff h₂).1 (hR ((Split.isInfPlay_infL_or_infR hJi).resolve_left hbL))
    have hmem : ∀ es, qi ++ .inr (.ask (Sum.inr a)) :: lows es ∈ J →
        (Split.halves false qi).2.map unmerge ++ (.inr (.ask a) : Move E (sig1 A₂ (B₂ ⊕ PUnit.{u + 1}))) :: lows es ∈
          List.map unmerge '' Split.infR J := fun es he =>
      ⟨(Split.halves false qi).2 ++ .inr (.ask a) :: lows es,
        ⟨_, he, by rw [halves_last_inr]; exact List.prefix_refl _⟩, map_unmerge_ask _ _ _⟩
    obtain ⟨s, ω, hrun, hω, hIeq⟩ := comp_stream hI (hmem [] hc) (fun p hp => by
      obtain ⟨r, ⟨q, hq, hr⟩, rfl⟩ := hp
      obtain ⟨es, hqe, hJe⟩ := hform q hq
      refine ⟨es, ?_, hmem es hJe⟩
      have h := (Split.halves_prefix hqe false).2
      rw [halves_last_inr] at h
      have h' := (hr.trans h).map unmerge
      rwa [map_unmerge_ask] at h')
    obtain ⟨y₁, r₁⟩ := (mem_threadS_iff h₁).1 (hJp hqiJ).2.1
    obtain ⟨s', hs'⟩ := run_idle_of_runs' r₁ hrun hqi
    refine ⟨qi.map pm, (s', s), Sum.inr a, ω, hs', hω, hsub (isInfPlay_streamPlay _ _ _) ?_⟩
    rintro p ⟨k, hk⟩
    have hmI : (Split.halves false qi).2.map unmerge ++ (.inr (.ask a) : Move E (sig1 A₂ (B₂ ⊕ PUnit.{u + 1}))) ::
        callMoves (streamTake ω k) ∈ List.map unmerge '' Split.infR J :=
      hIeq ▸ ⟨k, List.prefix_refl _⟩
    rw [callMoves_eq] at hmI
    obtain ⟨r, ⟨q, hq, hr⟩, hre⟩ := hmI
    obtain ⟨es, hqe, hJe⟩ := hform q hq
    have h := (Split.halves_prefix hqe false).2
    rw [halves_last_inr] at h
    have h' := (hr.trans h).map unmerge
    rw [hre, map_unmerge_ask, List.prefix_append_right_inj, List.cons_prefix_cons] at h'
    have hce := prefix_of_map_prefix Sum.inl_injective h'.2
    have hq' : qi ++ .inr (.ask (Sum.inr a)) :: lows (callEvs (streamTake ω k)) ∈ J :=
      hJi.of_prefix hJe ((List.prefix_append_right_inj qi).2
        (List.cons_prefix_cons.2 ⟨rfl, hce.map _⟩))
    refine hKi.of_prefix ⟨_, hq', rfl⟩ ?_
    rw [map_pm_ask, ← callMoves_eq]
    exact hk

/-- **Relabelled infinite plays of the paired session are infinite plays of the pairing.** -/
theorem inf_bwd (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {J : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))}
    (hK : List.map pm '' J ∈ (threadT (pairS t₁ t₂) (s₁, s₂)).inf) :
    J ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).inf := by
  obtain ⟨hKi, hKp, hK⟩ := hK
  have hJi := isInfPlay_of_image pm_injective hKi
  have hJp : J ⊆ ((threadS t₁ s₁).pair (threadS t₂ s₂)).toStrategy.plays := fun q hq =>
    (mem_pair_iff h₁ h₂).2 (by
      rw [mem_threadS_iff (noPlainTrap_pairS h₁ h₂), map_pm]; exact hKp ⟨q, hq, rfl⟩)
  have hP₁ : List.map unmerge '' Split.infL J ⊆ plays t₁.1 (satP t₁) s₁ := by
    rintro _ ⟨r, ⟨q, hq, hr⟩, rfl⟩
    exact (mem_threadS_iff h₁).1 ((threadS t₁ s₁).toStrategy.of_prefix (hJp hq).2.1 hr)
  have hP₂ : List.map unmerge '' Split.infR J ⊆ plays t₂.1 (satP t₂) s₂ := by
    rintro _ ⟨r, ⟨q, hq, hr⟩, rfl⟩
    exact (mem_threadS_iff h₂).1 ((threadS t₂ s₂).toStrategy.of_prefix (hJp hq).2.2 hr)
  refine ⟨hJi, hJp, fun hLi => (mem_inf_threadS_iff h₁).2 ⟨isInfPlay_image' _ hLi, hP₁, ?_⟩,
    fun hRi => (mem_inf_threadS_iff h₂).2 ⟨isInfPlay_image' _ hRi, hP₂, ?_⟩⟩
  · rcases hK with hs | ho
    · obtain ⟨pre, σ, c, ω, hrun, hω, hKeq⟩ := hs
      obtain ⟨qp, hqp, rfl⟩ : pre ∈ List.map pm '' J :=
        hKeq ▸ ⟨0, List.prefix_append _ _⟩
      have hk : ∀ k, qp ++ .inr (.ask c) :: lows (callEvs (streamTake ω k)) ∈ J := fun k => by
        obtain ⟨q, hq, he⟩ : qp.map pm ++ .inr (.ask c) :: callMoves (streamTake ω k) ∈
            List.map pm '' J := hKeq ▸ ⟨k, List.prefix_refl _⟩
        rw [callMoves_eq, ← map_pm_ask] at he
        rwa [← List.map_injective_iff.2 pm_injective he]
      have hb : ∀ q ∈ J, ∃ k, q <+: qp ++ .inr (.ask c) :: lows (callEvs (streamTake ω k)) :=
        fun q hq => by
          obtain ⟨k, hqk⟩ : q.map pm ∈ streamPlay (qp.map pm) c ω := hKeq ▸ ⟨q, hq, rfl⟩
          rw [callMoves_eq, ← map_pm_ask] at hqk
          exact ⟨k, prefix_of_map_prefix pm_injective hqk⟩
      obtain ⟨y₁, y₂, r₁, r₂, hr⟩ := fwd hrun (.idle s₁ s₂ false)
      generalize Split.side false qp = b at hr
      cases hr
      rcases c with a | a
      · refine .inl ⟨_, _, a, ω, r₁, hω, (isInfPlay_eq_of_subset (isInfPlay_image' _ hLi)
          (isInfPlay_streamPlay _ _ _) ?_).symm⟩
        rintro p ⟨k, hpk⟩
        rw [callMoves_eq, ← map_unmerge_ask] at hpk
        obtain ⟨r, hr, rfl⟩ := exists_of_prefix_map hpk
        exact ⟨r, ⟨_, hk k, by rw [halves_last_inl]; exact hr⟩, rfl⟩
      · exact (not_isInfPlay_infL hJi (n := (Split.halves false qp).1.length) (fun q hq => by
          obtain ⟨k, hqk⟩ := hb q hq
          have := ((Split.halves_prefix hqk false).1).length_le
          rwa [halves_last_inr] at this) hLi).elim
    · refine .inr ?_
      rintro _ ⟨r, ⟨q, hq, hr⟩, rfl⟩
      obtain ⟨_, ⟨q', hq', rfl⟩, hpre, σ, hrun⟩ := ho _ ⟨q, hq, rfl⟩
      have hqq := prefix_of_map_prefix pm_injective hpre
      obtain ⟨y₁, y₂, r₁, r₂, hr'⟩ := fwd hrun (.idle s₁ s₂ false)
      generalize Split.side false q' = b at hr'
      cases hr'
      exact ⟨_, ⟨_, ⟨q', hq', List.prefix_refl _⟩, rfl⟩,
        (hr.trans (Split.halves_prefix hqq false).1).map _, _, r₁⟩
  · rcases hK with hs | ho
    · obtain ⟨pre, σ, c, ω, hrun, hω, hKeq⟩ := hs
      obtain ⟨qp, hqp, rfl⟩ : pre ∈ List.map pm '' J :=
        hKeq ▸ ⟨0, List.prefix_append _ _⟩
      have hk : ∀ k, qp ++ .inr (.ask c) :: lows (callEvs (streamTake ω k)) ∈ J := fun k => by
        obtain ⟨q, hq, he⟩ : qp.map pm ++ .inr (.ask c) :: callMoves (streamTake ω k) ∈
            List.map pm '' J := hKeq ▸ ⟨k, List.prefix_refl _⟩
        rw [callMoves_eq, ← map_pm_ask] at he
        rwa [← List.map_injective_iff.2 pm_injective he]
      have hb : ∀ q ∈ J, ∃ k, q <+: qp ++ .inr (.ask c) :: lows (callEvs (streamTake ω k)) :=
        fun q hq => by
          obtain ⟨k, hqk⟩ : q.map pm ∈ streamPlay (qp.map pm) c ω := hKeq ▸ ⟨q, hq, rfl⟩
          rw [callMoves_eq, ← map_pm_ask] at hqk
          exact ⟨k, prefix_of_map_prefix pm_injective hqk⟩
      obtain ⟨y₁, y₂, r₁, r₂, hr⟩ := fwd hrun (.idle s₁ s₂ false)
      generalize Split.side false qp = b at hr
      cases hr
      rcases c with a | a
      · exact (not_isInfPlay_infR hJi (n := (Split.halves false qp).2.length) (fun q hq => by
          obtain ⟨k, hqk⟩ := hb q hq
          have := ((Split.halves_prefix hqk false).2).length_le
          rwa [halves_last_inl] at this) hRi).elim
      · refine .inl ⟨_, _, a, ω, r₂, hω, (isInfPlay_eq_of_subset (isInfPlay_image' _ hRi)
          (isInfPlay_streamPlay _ _ _) ?_).symm⟩
        rintro p ⟨k, hpk⟩
        rw [callMoves_eq, ← map_unmerge_ask] at hpk
        obtain ⟨r, hr, rfl⟩ := exists_of_prefix_map hpk
        exact ⟨r, ⟨_, hk k, by rw [halves_last_inr]; exact hr⟩, rfl⟩
    · refine .inr ?_
      rintro _ ⟨r, ⟨q, hq, hr⟩, rfl⟩
      obtain ⟨_, ⟨q', hq', rfl⟩, hpre, σ, hrun⟩ := ho _ ⟨q, hq, rfl⟩
      have hqq := prefix_of_map_prefix pm_injective hpre
      obtain ⟨y₁, y₂, r₁, r₂, hr'⟩ := fwd hrun (.idle s₁ s₂ false)
      generalize Split.side false q' = b at hr'
      cases hr'
      exact ⟨_, ⟨_, ⟨q', hq', List.prefix_refl _⟩, rfl⟩,
        (hr.trans (Split.halves_prefix hqq false).2).map _, _, r₂⟩

/-- **The infinite plays of the pairing of two sessions** are the relabelled infinite plays of the
paired session. -/
theorem mem_inf_pair_iff (h₁ : NoPlainTrap t₁) (h₂ : NoPlainTrap t₂)
    {J : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)))} :
    J ∈ ((threadS t₁ s₁).pair (threadS t₂ s₂)).inf ↔
      List.map pairMove '' J ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).inf := by
  rw [mem_inf_threadS_iff (noPlainTrap_pairS h₁ h₂), Set.image_image]
  have : (fun q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)) => (q.map pairMove).map unmerge) =
      List.map pm := funext map_pm
  rw [this]
  exact ⟨inf_fwd h₁ h₂, inf_bwd h₁ h₂⟩

/-- Every infinite play of the paired session is a relabelling. -/
theorem exists_image_pairMove {K : Set (List (Move E (sig1 (A₁ ⊕ A₂) (B₁ ⊕ B₂))))}
    (hK : K ∈ (threadS (pairS t₁ t₂) (s₁, s₂)).inf) :
    ∃ J : Set (List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))), K = List.map pairMove '' J := by
  refine ⟨{q | q.map pairMove ∈ K}, Set.ext fun p => ⟨fun hp => ?_, ?_⟩⟩
  · obtain ⟨q, rfl⟩ := exists_map_pairMove ((threadS (pairS t₁ t₂) (s₁, s₂)).inf_sub hK hp)
    exact ⟨q, hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact hq

end Pair

end Silmaril.Proofs.Games.Abstract.SessionPair
