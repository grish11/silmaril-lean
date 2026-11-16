module

public import Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.Link

/-!
# Linking sessions: associativity of finished behaviours (proofs)

The finished behaviours of `linkS (linkS t u) v` and of `linkS t (linkS u v)` correspond along the
store reassociation. A return of the client `v` is served by rounds of `u`, served by rounds of
`t` in both bracketings. The divergences regroup:

* a divergence of `u` inside a call of `v` is a divergence of `linkS t u` (outer bracketing) or
  of `linkS u v` (inner bracketing);
* a divergence of `t` inside a call of `u` inside a call of `v` is in both a server divergence of
  the outer link, the inner pending call being a pending call of the linked triple;
* hidden chatter of `u` inside a call of `v` is chatter of `linkS t u`, or of the outer link along
  a productive stream of `linkS u v`;
* hidden chatter of `v` served by `linkS t u` is, inside, chatter of `v` against `u` (finitely
  many calls of `u`) served by finitely many rounds of `t`, or (infinitely many calls of `u`) a
  productive stream of `linkS u v` chattering against `t`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkAssoc

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionLinkAssoc

universe u

variable {E : Sig.{u}} {S₁ S₂ S₃ A B A' B' A'' B'' : Type u}
  {t : ObsTriple E S₁ A (B ⊕ PUnit.{u + 1})} {u : ObsTriple (sig1 A B) S₂ A' (B' ⊕ PUnit.{u + 1})}
  {v : ObsTriple (sig1 A' B') S₃ A'' (B'' ⊕ PUnit.{u + 1})}

theorem mapEnd_assoc_linkEnd (s₁ : S₁) (s₂ : S₂) (e : End S₃ (B'' ⊕ PUnit.{u + 1})) :
    mapEnd (Equiv.prodAssoc S₁ S₂ S₃) (linkEnd (s₁, s₂) e) = linkEnd s₁ (linkEnd s₂ e) := by
  cases e <;> rfl

theorem mapEnd_assoc_symm_linkEnd (s₁ : S₁) (s₂ : S₂) (e : End S₃ (B'' ⊕ PUnit.{u + 1})) :
    mapEnd (Equiv.prodAssoc S₁ S₂ S₃).symm (linkEnd s₁ (linkEnd s₂ e)) = linkEnd (s₁, s₂) e := by
  cases e <;> rfl

/-- Finished behaviours, outer to inner bracketing. -/
theorem fst_fwd {s₁ : S₁} {s₂ : S₂} {s₃ : S₃} {a'' : A''}
    {x : List (Call E) × End ((S₁ × S₂) × S₃) (B'' ⊕ PUnit.{u + 1})}
    (hx : x ∈ (linkS (linkS t u) v).1 ((s₁, s₂), s₃) a'') :
    (x.1, mapEnd (Equiv.prodAssoc S₁ S₂ S₃) x.2) ∈ (linkS t (linkS u v)).1 (s₁, (s₂, s₃)) a'' := by
  rcases hx with ⟨rs, σ₁, e, hr, he, rfl⟩ | ⟨rs, σ₁, a', c, hr, hp, hc, rfl⟩ |
    ⟨ω, hω, l, st, n, hs, hl, rfl⟩
  · -- the client `v` ends
    obtain ⟨rt, ru, ht, hu, h₁, h₂, h₃⟩ := rounds_linkS_fwd hr
    refine .inl ⟨rt, σ₁.1, linkEnd σ₁.2 e, ht, .inl ⟨ru, σ₁.2, e, hu, h₂ ▸ he, by rw [h₁]⟩, ?_⟩
    rw [h₃]
    exact congrArg _ (mapEnd_assoc_linkEnd σ₁.1 σ₁.2 e)
  · -- `linkS t u` diverges inside a call of `v`
    obtain ⟨rt₀, ru, ht, hu, h₁, h₂, h₃⟩ := rounds_linkS_fwd hr
    rcases hc with ⟨rt₁, s₁', e₁, hr₁, he₁, hx₁⟩ | ⟨rt₁, s₁', a, c', hr₁, hp₁, hc₁, hx₁⟩ |
      ⟨ω, hω, lt, stt, n, hs, hl, hx₁⟩
    · -- `u` diverges
      obtain ⟨rfl, he₁'⟩ := Prod.mk.inj hx₁
      obtain rfl := linkEnd_eq_div he₁'.symm
      refine .inl ⟨rt₀ ++ rt₁, s₁', .div, rounds_append ht hr₁,
        .inr (.inl ⟨ru, σ₁.2, a', served rt₁, hu, h₂ ▸ hp, he₁, by simp [h₁]⟩), ?_⟩
      simp [h₃, mapEnd, linkEnd]
    · -- `t` diverges inside a call of `u`
      obtain ⟨rfl, -⟩ := Prod.mk.inj hx₁
      refine .inr (.inl ⟨rt₀ ++ rt₁, s₁', a, c', rounds_append ht hr₁, ?_, hc₁, ?_⟩)
      · exact satP_linkS_iff.2 ⟨ru, σ₁.2, a', served rt₁, hu, h₂ ▸ hp, hp₁, by simp [h₁]⟩
      · simp [h₃, mapEnd]
    · -- `u` chatters against `t`
      obtain ⟨rfl, -⟩ := Prod.mk.inj hx₁
      obtain ⟨st', hs'⟩ := infServe_prepend ht hs
      rw [h₁] at hs'
      refine .inr (.inr ⟨_, .inl ⟨ru, σ₁.2, a', ω, hu, h₂ ▸ hp, hω,
        fun k => streamTake_prependStream _ _ k⟩, _, st', (rt₀.map (·.2.1)).length + n, hs',
        fun k hk => ?_, ?_⟩)
      · rw [prependStream_of_le _ (by omega)]
        exact hl _ (by omega)
      · rw [logTake_prependStream, flatten_map_log, h₃]
        simp [mapEnd]
  · -- `v` chatters against `linkS t u`
    obtain ⟨rt, hrt, hsu, hlog, h₀⟩ := infServe_linkS_fwd hs
    have hl' : l = fun k => servedLog (rt k) := funext hlog
    subst hl'
    rcases eventually_nil_or_unbounded (fun k => served (rt k)) with ⟨n', hn'⟩ | hunb
    · -- finitely many calls of `u`: `linkS u v` chatters, served by finitely many rounds of `t`
      have hnil : ∀ k, n' ≤ k → servedLog (rt k) = [] := fun k hk => by
        rw [served_eq_nil.1 (hn' k hk)]; rfl
      refine .inl ⟨(streamTake rt n').flatten, (st n').1, .div, h₀ ▸ rounds_flatten hrt n',
        .inr (.inr ⟨ω, hω, _, _, n', hsu, hn', by rw [served_flatten]⟩), ?_⟩
      simp only [mapEnd, linkEnd, Prod.mk.injEq, and_true]
      rw [servedLog_flatten, ← logTake_of_nil hl (le_max_left n n'),
        logTake_of_nil hnil (le_max_right n n')]
    · -- infinitely many calls of `u`: a stream of `linkS u v` chatters against `t`
      obtain ⟨ω'', lt, stt, hst, hpre, hlt⟩ := infServe_flat hrt h₀ hunb
      set N := (logTake (fun k => served (rt k)) n).length
      refine .inr (.inr ⟨ω'', .inr ⟨ω, hω, _, _, hsu, hunb, hpre⟩, lt, stt, N, hst,
        fun i hi => ?_, ?_⟩)
      · obtain ⟨k, hk⟩ := hunb (i + 1)
        replace hk : i + 1 ≤ (logTake (fun k => served (rt k)) k).length := hk
        have hkn : n ≤ k := by
          by_contra hkn
          have := length_logTake_mono (fun k => served (rt k)) (le_of_not_ge hkn)
          omega
        have heq : logTake lt (N + ((logTake (fun k => served (rt k)) k).length - N)) =
            logTake lt N := by
          rw [Nat.add_sub_cancel' (length_logTake_mono _ hkn), hlt, hlt, logTake_of_nil hl hkn]
        have := logTake_nil_of_eq heq (j := i - N) (by omega)
        rwa [Nat.add_sub_cancel' hi] at this
      · simp only [mapEnd, Prod.mk.injEq, and_true]
        rw [hlt]

/-- Finished behaviours, inner to outer bracketing. -/
theorem fst_bwd {s₁ : S₁} {s₂ : S₂} {s₃ : S₃} {a'' : A''}
    {z : List (Call E) × End (S₁ × (S₂ × S₃)) (B'' ⊕ PUnit.{u + 1})}
    (hz : z ∈ (linkS t (linkS u v)).1 (s₁, (s₂, s₃)) a'') :
    (z.1, mapEnd (Equiv.prodAssoc S₁ S₂ S₃).symm z.2) ∈
      (linkS (linkS t u) v).1 ((s₁, s₂), s₃) a'' := by
  rcases hz with ⟨rt, s₁', e', ht, he', rfl⟩ | ⟨rt, s₁', a, c, ht, hp, hc, rfl⟩ |
    ⟨ω'', hω'', lt, stt, n, hs, hl, rfl⟩
  · rcases he' with ⟨ru, s₂', e, hu, he, hx⟩ | ⟨ru, s₂', a', c, hu, hp, hc, hx⟩ |
      ⟨ω, hω, lu, stu, n', hsu, hlu, hx⟩
    · -- the client `v` ends
      obtain ⟨h₁, rfl⟩ := Prod.mk.inj hx
      obtain ⟨rs, hrs, hs₁, hs₂⟩ := rounds_linkS_bwd ht hu h₁
      refine .inl ⟨rs, (s₁', s₂'), e, hrs, hs₁ ▸ he, ?_⟩
      rw [hs₂]
      exact congrArg _ (mapEnd_assoc_symm_linkEnd s₁' s₂' e)
    · -- `u` diverges inside a call of `v`
      obtain ⟨h₁, rfl⟩ := Prod.mk.inj hx
      obtain ⟨rt₀, rt₁, rfl, h₁, h₂⟩ := served_eq_append h₁
      obtain ⟨sm, hr₀, hr₁⟩ := rounds_of_append ht
      obtain ⟨rs, hrs, hs₁, hs₂⟩ := rounds_linkS_bwd hr₀ hu h₁
      refine .inr (.inl ⟨rs, (sm, s₂'), a', servedLog rt₁, hrs, hs₁ ▸ hp,
        .inl ⟨rt₁, s₁', .div, hr₁, h₂ ▸ hc, rfl⟩, ?_⟩)
      simp [hs₂, mapEnd, linkEnd]
    · -- `v` chatters against `u`, served by finitely many rounds of `t`
      obtain ⟨h₁, rfl⟩ := Prod.mk.inj hx
      obtain ⟨rtb, stb, hst₀, hk, hnil, hlog⟩ := rounds_blocks' hlu ht h₁
      refine .inr (.inr ⟨ω, hω, fun k => servedLog (rtb k), fun k => (stb k, stu k), n',
        ⟨by simp [hst₀, hsu.zero], fun k => ret_linkS_iff.2 ⟨rtb k, (hk k).1,
          (hk k).2 ▸ hsu.step k, rfl⟩⟩, fun k hk' => by
          show servedLog (rtb k) = []; rw [hnil k hk']; rfl, ?_⟩)
      simp [hlog, mapEnd, linkEnd]
  · -- `t` diverges inside a pending call of `linkS u v`
    obtain ⟨ru, s₂', a', cu, hu, hpv, hpu, hd⟩ := satP_linkS_iff.1 hp
    obtain ⟨rt₀, rt₁, rfl, h₁, h₂⟩ := served_eq_append hd
    obtain ⟨sm, hr₀, hr₁⟩ := rounds_of_append ht
    obtain ⟨rs, hrs, hs₁, hs₂⟩ := rounds_linkS_bwd hr₀ hu h₁
    refine .inr (.inl ⟨rs, (sm, s₂'), a', servedLog rt₁ ++ c, hrs, hs₁ ▸ hpv,
      .inr (.inl ⟨rt₁, s₁', a, c, hr₁, h₂ ▸ hpu, hc, rfl⟩), ?_⟩)
    simp [hs₂, mapEnd]
  · rcases hω'' with ⟨ru, s₂', a', ω, hu, hpv, hω, hpre⟩ | ⟨ω, hω, lu, stu, hsu, hunb, hpre⟩
    · -- a stream of `u` inside a call of `v`, chattering against `t`
      set M := (servedLog ru).length
      have hω''eq := prefix_iff_prependStream.1 hpre
      have hr₀ := rounds_block hs 0 M
      rw [Nat.zero_add, hs.zero] at hr₀
      have h₁ : served (streamTake (serveRounds ω'' lt 0) M) = servedLog ru := by
        rw [served_serveRounds]
        simpa using hpre 0
      obtain ⟨rs, hrs, hs₁, hs₂⟩ := rounds_linkS_bwd hr₀ hu h₁
      have hsh : (fun k => ω'' (M + k)) = ω := by
        funext k; rw [hω''eq]; exact prependStream_add _ _ k
      have hs' := infServe_shift hs M
      rw [hsh] at hs'
      refine .inr (.inl ⟨rs, (stt M, s₂'), a', logTake (fun k => lt (M + k)) (max n M - M), hrs,
        hs₁ ▸ hpv, .inr (.inr ⟨ω, hω, _, _, max n M - M, hs', fun k hk => hl _ (by omega),
          rfl⟩), ?_⟩)
      simp only [mapEnd, Prod.mk.injEq, and_true]
      rw [hs₂, servedLog_serveRounds]
      simp only [Nat.zero_add]
      rw [← logTake_add, Nat.add_sub_cancel' (le_max_right n M)]
      exact (logTake_of_nil hl (le_max_left n M)).symm
    · -- a stream of `linkS u v` serving infinitely many calls of `u`, chattering against `t`
      obtain ⟨l, st, hsl, hlk, hlt⟩ := infServe_linkS_bwd hsu hs hpre
      obtain ⟨nL, hnL⟩ := hunb n
      refine .inr (.inr ⟨ω, hω, l, st, nL, hsl, fun k hk => ?_, ?_⟩)
      · rw [hlk]
        refine List.flatten_eq_nil_iff.2 fun y hy => ?_
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_ofFn.1 hy
        have := length_logTake_mono lu hk
        exact hl _ (by simp only; omega)
      · simp only [mapEnd, Prod.mk.injEq, and_true]
        rw [hlt, logTake_of_nil hl hnL]

end Silmaril.Proofs.Games.Abstract.SessionLinkAssoc
