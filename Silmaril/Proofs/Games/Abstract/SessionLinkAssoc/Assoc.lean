module

public import Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.AssocFin

/-!
# Linking sessions: associativity (proofs)

Pending calls and productive streams of the two bracketings correspond as well; with the finished
behaviours (`AssocFin`) this gives the literal associativity of `linkS` along the store
reassociation.

* A pending call of `t` inside a call of `u` inside a call of `v`: in both bracketings, a pending
  call of the server inside a pending call of the client, the linked triples being saturated.
* A stream of `t` inside a call of `u` inside a call of `v`: as for pending calls.
* A stream of `u` inside a call of `v`, served by `t` with infinitely many calls: a stream of
  `linkS t u` (outer) or a stream of `linkS u v` served by `t` (inner); the service of `t` is
  prefixed by the rounds serving the earlier calls of `u`.
* A stream of `v` served by `linkS t u` with infinitely many calls on `E`: inside, a stream of `v`
  served by `u` with infinitely many calls of `u` (each call of `u` is served by one round of
  `t`), served by `t`. The blocks of rounds of `t` serving the rounds of `u` are flattened
  (`infServe_flat`) or cut along the rounds of `u` (`infServe_linkS_bwd`).
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

/-- Pending calls of the two bracketings. -/
theorem snd_iff {s₁ : S₁} {s₂ : S₂} {s₃ : S₃} {a'' : A''} {x : List (Call E) × E.Op} :
    x ∈ (linkS (linkS t u) v).2.1 ((s₁, s₂), s₃) a'' ↔
      x ∈ (linkS t (linkS u v)).2.1 (s₁, (s₂, s₃)) a'' := by
  constructor
  · rintro ⟨rs, σ₁, a', c, hr, hp, hc, hx⟩
    obtain ⟨rt₁, s₁'', a, ct, hr₁, hp₁, hc₁, rfl⟩ := satP_linkS_iff.1 hc
    obtain ⟨rt₀, ru, ht, hu, h₁, h₂, h₃⟩ := rounds_linkS_fwd hr
    exact ⟨rt₀ ++ rt₁, s₁'', a, ct, rounds_append ht hr₁,
      satP_linkS_iff.2 ⟨ru, σ₁.2, a', served rt₁, hu, h₂ ▸ hp, hp₁, by simp [h₁]⟩, hc₁,
      by simp [hx, h₃]⟩
  · rintro ⟨rt, s₁', a, c, ht, hp, hc, hx⟩
    obtain ⟨ru, s₂', a', cu, hu, hpv, hpu, hd⟩ := satP_linkS_iff.1 hp
    obtain ⟨rt₀, rt₁, rfl, h₁, h₂⟩ := served_eq_append hd
    obtain ⟨sm, hr₀, hr₁⟩ := rounds_of_append ht
    obtain ⟨rs, hrs, hs₁, hs₂⟩ := rounds_linkS_bwd hr₀ hu h₁
    exact ⟨rs, (sm, s₂'), a', servedLog rt₁ ++ c, hrs, hs₁ ▸ hpv,
      satP_linkS_iff.2 ⟨rt₁, s₁', a, c, hr₁, h₂ ▸ hpu, hc, rfl⟩, by simp [hx, hs₂]⟩

/-- Productive streams, outer to inner bracketing. -/
theorem thrd_fwd {s₁ : S₁} {s₂ : S₂} {s₃ : S₃} {a'' : A''} {x : ℕ → Call E}
    (hx : x ∈ (linkS (linkS t u) v).2.2 ((s₁, s₂), s₃) a'') :
    x ∈ (linkS t (linkS u v)).2.2 (s₁, (s₂, s₃)) a'' := by
  rcases hx with ⟨rs, σ₁, a', ω', hr, hp, hω', hpre⟩ | ⟨ω, hω, l, st, hs, hunb, hpre⟩
  · obtain ⟨rt₀, ru, ht, hu, h₁, h₂, h₃⟩ := rounds_linkS_fwd hr
    have hx := prefix_iff_prependStream.1 hpre
    rcases hω' with ⟨rt₁, s₁'', a, ω₀, hr₁, hp₁, hω₀, hpre₁⟩ |
      ⟨ωu, hωu, lt, stt, hst, hunbt, hpret⟩
    · -- a stream of `t` inside a call of `u` inside a call of `v`
      refine .inl ⟨rt₀ ++ rt₁, s₁'', a, ω₀, rounds_append ht hr₁,
        satP_linkS_iff.2 ⟨ru, σ₁.2, a', served rt₁, hu, h₂ ▸ hp, hp₁, by simp [h₁]⟩, hω₀,
        prefix_iff_prependStream.2 ?_⟩
      rw [hx, prefix_iff_prependStream.1 hpre₁, servedLog_append, prependStream_append, h₃]
    · -- a stream of `u` inside a call of `v`, served by `t`
      obtain ⟨st', hs'⟩ := infServe_prepend ht hst
      rw [h₁] at hs'
      have hlog : ∀ k, logTake (prependStream (rt₀.map (·.2.1)) lt)
          ((rt₀.map (·.2.1)).length + k) = servedLog rs ++ logTake lt k := fun k => by
        rw [logTake_prependStream, flatten_map_log, h₃]
      refine .inr ⟨_, .inl ⟨ru, σ₁.2, a', ωu, hu, h₂ ▸ hp, hωu,
        fun k => streamTake_prependStream _ _ k⟩, _, st', hs', fun n => ?_, fun j => ?_⟩
      · obtain ⟨k, hk⟩ := hunbt n
        exact ⟨(rt₀.map (·.2.1)).length + k, by rw [hlog, List.length_append]; omega⟩
      · refine streamTake_of_prefix (M := (servedLog rs).length + (logTake lt j).length) ?_
        refine (logTake_mono _ (Nat.le_add_left j (rt₀.map (·.2.1)).length)).trans ?_
        rw [hlog, hpre, hpret]
        exact List.prefix_refl _
  · -- a stream of `v` served by `linkS t u`
    obtain ⟨rt, hrt, hsu, hlog, h₀⟩ := infServe_linkS_fwd hs
    have hl' : l = fun k => servedLog (rt k) := funext hlog
    subst hl'
    rcases eventually_nil_or_unbounded (fun k => served (rt k)) with ⟨n', hn'⟩ | hunbu
    · exfalso
      have hnil : ∀ k, n' ≤ k → servedLog (rt k) = [] := fun k hk => by
        rw [served_eq_nil.1 (hn' k hk)]; rfl
      obtain ⟨k, hk⟩ := hunb ((logTake (fun k => servedLog (rt k)) n').length + 1)
      have h₁ := length_logTake_mono (fun k => servedLog (rt k)) (le_max_left k n')
      rw [logTake_of_nil hnil (le_max_right k n')] at h₁
      omega
    · obtain ⟨ω'', lt, stt, hst, hpre'', hlt⟩ := infServe_flat hrt h₀ hunbu
      refine .inr ⟨ω'', .inr ⟨ω, hω, _, _, hsu, hunbu, hpre''⟩, lt, stt, hst, fun n => ?_,
        fun j => ?_⟩
      · obtain ⟨k, hk⟩ := hunb n
        exact ⟨_, by rw [hlt]; exact hk⟩
      · obtain ⟨k, hk⟩ := hunbu j
        refine streamTake_of_prefix (M := (logTake (fun k => servedLog (rt k)) k).length) ?_
        rw [hpre k, ← hlt k]
        exact logTake_mono _ hk

/-- Productive streams, inner to outer bracketing. -/
theorem thrd_bwd {s₁ : S₁} {s₂ : S₂} {s₃ : S₃} {a'' : A''} {x : ℕ → Call E}
    (hx : x ∈ (linkS t (linkS u v)).2.2 (s₁, (s₂, s₃)) a'') :
    x ∈ (linkS (linkS t u) v).2.2 ((s₁, s₂), s₃) a'' := by
  rcases hx with ⟨rt, s₁', a, ω₀, ht, hp, hω₀, hpre⟩ | ⟨ω'', hω'', lt, stt, hs, hunb, hpre⟩
  · -- a stream of `t` inside a pending call of `linkS u v`
    obtain ⟨ru, s₂', a', cu, hu, hpv, hpu, hd⟩ := satP_linkS_iff.1 hp
    obtain ⟨rt₀, rt₁, rfl, h₁, h₂⟩ := served_eq_append hd
    obtain ⟨sm, hr₀, hr₁⟩ := rounds_of_append ht
    obtain ⟨rs, hrs, hs₁, hs₂⟩ := rounds_linkS_bwd hr₀ hu h₁
    refine .inl ⟨rs, (sm, s₂'), a', prependStream (servedLog rt₁) ω₀, hrs, hs₁ ▸ hpv,
      .inl ⟨rt₁, s₁', a, ω₀, hr₁, h₂ ▸ hpu, hω₀, fun k => streamTake_prependStream _ _ k⟩,
      prefix_iff_prependStream.2 ?_⟩
    rw [prefix_iff_prependStream.1 hpre, ← prependStream_append, hs₂, servedLog_append]
  · rcases hω'' with ⟨ru, s₂', a', ωu, hu, hpv, hωu, hpreu⟩ |
      ⟨ω, hω, lu, stu, hsu, hunbu, hpreu⟩
    · -- a stream of `linkS u v` inside a call of `v`, served by `t`
      set M := (servedLog ru).length
      have hω''eq := prefix_iff_prependStream.1 hpreu
      have hr₀ := rounds_block hs 0 M
      rw [Nat.zero_add, hs.zero] at hr₀
      have h₁ : served (streamTake (serveRounds ω'' lt 0) M) = servedLog ru := by
        rw [served_serveRounds]
        simpa using hpreu 0
      obtain ⟨rs, hrs, hs₁, hs₂⟩ := rounds_linkS_bwd hr₀ hu h₁
      have hP : servedLog rs = logTake lt M := by
        rw [hs₂, servedLog_serveRounds]
        simp only [Nat.zero_add]
      have hsh : (fun k => ω'' (M + k)) = ωu := by
        funext k; rw [hω''eq]; exact prependStream_add _ _ k
      have hs' := infServe_shift hs M
      rw [hsh] at hs'
      have hxP : streamTake x (servedLog rs).length = servedLog rs := by
        rw [hP]; exact hpre M
      refine .inl ⟨rs, (stt M, s₂'), a', fun i => x ((servedLog rs).length + i), hrs, hs₁ ▸ hpv,
        .inr ⟨ωu, hωu, _, _, hs', fun n => ?_, fun k => ?_⟩,
        prefix_iff_prependStream.2 (prependStream_shift hxP)⟩
      · obtain ⟨k, hk⟩ := hunb ((logTake lt M).length + n)
        refine ⟨k, ?_⟩
        have h₂ := length_logTake_mono lt (Nat.le_add_left k M)
        rw [logTake_add, List.length_append] at h₂
        omega
      · have h₂ := hpre (M + k)
        rw [logTake_add, List.length_append, streamTake_add, ← hP, hxP] at h₂
        exact List.append_cancel_left h₂
    · -- a stream of `v` served by `u` with infinitely many calls, served by `t`
      obtain ⟨l, st, hsl, -, hlt⟩ := infServe_linkS_bwd hsu hs hpreu
      refine .inr ⟨ω, hω, l, st, hsl, fun n => ?_, fun k => ?_⟩
      · obtain ⟨j, hj⟩ := hunb n
        obtain ⟨k, hk⟩ := hunbu j
        refine ⟨k, ?_⟩
        rw [hlt]
        have := length_logTake_mono lt hk
        omega
      · rw [hlt]
        exact hpre _

/-- **Linking is associative**, literally, along the store reassociation. -/
theorem linkS_assoc (t : ObsTriple E S₁ A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S₂ A' (B' ⊕ PUnit.{u + 1}))
    (v : ObsTriple (sig1 A' B') S₃ A'' (B'' ⊕ PUnit.{u + 1})) :
    linkS (linkS t u) v = mapStore (Equiv.prodAssoc S₁ S₂ S₃).symm (linkS t (linkS u v)) := by
  refine obsTriple_ext (fun σ a x => ?_) (fun σ a x => ?_) (fun σ a x => ?_)
  · obtain ⟨⟨s₁, s₂⟩, s₃⟩ := σ
    simp only [mapStore, Equiv.symm_symm, Equiv.prodAssoc_apply, Set.mem_image]
    constructor
    · intro hx
      refine ⟨(x.1, mapEnd (Equiv.prodAssoc S₁ S₂ S₃) x.2), fst_fwd hx, ?_⟩
      rw [mapEnd_mapEnd, Equiv.symm_comp_self, mapEnd_id]
    · rintro ⟨z, hz, rfl⟩
      exact fst_bwd hz
  · obtain ⟨⟨s₁, s₂⟩, s₃⟩ := σ
    exact snd_iff
  · obtain ⟨⟨s₁, s₂⟩, s₃⟩ := σ
    exact ⟨thrd_fwd, thrd_bwd⟩

end Silmaril.Proofs.Games.Abstract.SessionLinkAssoc
