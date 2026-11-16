module

public import Silmaril.Proofs.Games.Abstract.SessionHost.Div

/-!
# Infinite plays of a session with host imports (proofs)

* `inf_fwd` (no hypothesis): an infinite play of the composite is a linked infinite play. The
  visible parts of the interaction are those of the session of `t` up to one forwarded move
  (`lim_eq_of_stage`), so they have the same limit. The session's limit is a productive stream
  after completed rounds, with infinitely many component calls since the visible part grows (their
  limit `ω'` is a linked productive stream, `exists_stream_lim`), or completes infinitely many
  rounds, each a linked round.
* `inf_bwd` (`StoreDet (hostLinkS R t)`): a linked stream is the visible part of the stream of `t`
  it comes from; a coherent infinite sequence of linked rounds is the visible part of a coherent
  infinite sequence of rounds of `t`, chosen round by round. Store determinism of the linked
  triple makes the linked rounds coherent (`StratSession.mem_inf_iff_of_storeDet`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionHost
  Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession

universe u

variable {E F : Sig.{u}} {S A B : Type u} {R : HostRel E}

/-! ## Limits -/

section Limits

variable {α β : Type u}

/-- **The limit stream of an increasing unbounded chain of lists.** -/
theorem exists_stream_lim {c : ℕ → List α} (hm : ∀ k, c k <+: c (k + 1))
    (hu : ∀ n, ∃ k, n ≤ (c k).length) : ∃ ω : ℕ → α, ∀ k, streamTake ω (c k).length = c k := by
  choose K hK using fun j => hu (j + 1)
  refine ⟨fun j => (c (K j))[j]'(hK j), fun k => List.ext_getElem (by simp) fun i h₁ h₂ => ?_⟩
  simp only [streamTake, List.getElem_ofFn]
  have hmono : Chain.Mono c := hm
  rcases le_total (K i) k with h | h
  · exact (hmono.le h).getElem _
  · exact ((hmono.le h).getElem h₂).symm

theorem lim_map_eq {c d : Chain α} (h : c.lim = d.lim) (f : List α → List β)
    (hf : ∀ {x y}, x <+: y → f x <+: f y) :
    Chain.lim (fun n => f (c n)) = Chain.lim (fun n => f (d n)) := by
  refine Chain.lim_eq_of (fun n => ?_) (fun n => ?_)
  · obtain ⟨m, hm⟩ : c n ∈ d.lim := h ▸ Chain.mem_lim_self c n
    exact ⟨m, hf hm⟩
  · obtain ⟨m, hm⟩ : d n ∈ c.lim := h.symm ▸ Chain.mem_lim_self d n
    exact ⟨m, hf hm⟩

/-- Chains equal up to one move at the end have the same limit. -/
theorem lim_eq_of_stage {q V : Chain α} (hq : q.Mono) (hV : V.Mono) (hu : q.Unbounded)
    (h : ∀ n, ∃ a b : List α, a.length ≤ 1 ∧ b.length ≤ 1 ∧ q n ++ a = V n ++ b) :
    q.lim = V.lim := by
  refine Chain.lim_eq_of (fun n => ?_) (fun n => ?_)
  · obtain ⟨n', hn', hl⟩ := hq.unbounded_ge hu ((q n).length + 1) n
    obtain ⟨a, b, ha, hb, he⟩ := h n'
    have h₁ : q n <+: V n' ++ b := he ▸ (hq.le hn').trans (List.prefix_append _ _)
    have := congrArg List.length he
    simp only [List.length_append] at this
    exact ⟨n', List.prefix_of_prefix_length_le h₁ (List.prefix_append _ _) (by omega)⟩
  · obtain ⟨n', hn', hl⟩ := hq.unbounded_ge hu ((V n).length + 1) n
    obtain ⟨a, b, ha, hb, he⟩ := h n'
    have h₁ : V n <+: q n' ++ a := he.symm ▸ (hV.le hn').trans (List.prefix_append _ _)
    exact ⟨n', List.prefix_of_prefix_length_le h₁ (List.prefix_append _ _) (by omega)⟩

end Limits

/-! ## Linked streams -/

theorem fCalls_mono (ω : ℕ → Call (E ⊕ₛ F)) (k : ℕ) :
    fCalls (streamTake ω k) <+: fCalls (streamTake ω (k + 1)) :=
  fCalls_prefix (streamTake_mono ω (Nat.le_succ k))

/-- The visible parts of a stream of `t` are the plays of its linked stream. -/
theorem lim_vis_sPlay (rs : List (A × List (Call (E ⊕ₛ F)) × (B ⊕ PUnit.{u + 1}))) (a : A)
    {ω : ℕ → Call (E ⊕ₛ F)} {ω' : ℕ → Call F}
    (hu : ∀ n, ∃ k, n ≤ (fCalls (streamTake ω k)).length)
    (hs : ∀ k, streamTake ω' (fCalls (streamTake ω k)).length = fCalls (streamTake ω k)) :
    Chain.lim (fun k => vis (sPlay rs a ω k)) = streamPlay (sroundsMoves (projR rs)) a ω' := by
  have heq : ∀ k, vis (sPlay rs a ω k) = sPlay (projR rs) a ω' (fCalls (streamTake ω k)).length :=
    fun k => by rw [vis_sPlay, sPlay, hs]
  refine Chain.lim_eq_of
    (fun k => ⟨(fCalls (streamTake ω k)).length, by rw [heq k]; exact List.prefix_refl _⟩)
    (fun j => ?_)
  obtain ⟨k, hk⟩ := hu j
  exact ⟨k, by rw [heq k]; exact sPlay_mono _ a ω' hk⟩

/-! ## The forward direction -/

variable {t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

theorem inf_fwd {I : Set (List (Move F (sig1 A B)))}
    (hI : I ∈ ((hostCopy F R).comp (threadS t s₀)).inf) :
    I ∈ (threadS (hostLinkS R t) s₀).inf := by
  obtain ⟨i, hu, rfl⟩ := hI
  have hst := fun n => stage (i.mem_s n) (i.mem_t n) (i.zip n)
  have hlen : ∀ n, (i.p n).length ≤ (vis (i.t n)).length + 1 := fun n => by
    obtain ⟨-, h, g, -, -, he⟩ := hst n
    exact (stage_length he).2
  have hpV : i.p.lim = Chain.lim fun n => vis (i.t n) :=
    lim_eq_of_stage i.mono_p (fun n => vis_prefix (i.mono_t n)) hu fun n => by
      obtain ⟨-, h, g, -, -, he⟩ := hst n
      exact ⟨aOf h, bOf h, length_aOf_le h, length_bOf_le h, he⟩
  have htu : i.t.Unbounded := fun k => by
    obtain ⟨n, hn⟩ := hu (k + 1)
    exact ⟨n, by have := hlen n; have := length_vis_le (i.t n); omega⟩
  rcases mem_inf_iff.1 (i.lim_t htu) with ⟨rs, s, a, ω, hrs, hω, hI⟩ | ⟨a, r, hI, hR⟩
  · -- a productive stream after completed rounds
    have hP : ∀ k, ∃ n, sPlay rs a ω k <+: i.t n := fun k => by
      have : sPlay rs a ω k ∈ i.t.lim := hI ▸ ⟨k, List.prefix_refl _⟩
      exact this
    have hokP : ∀ k, OkV R (sPlay rs a ω k) := fun k => by
      obtain ⟨n, hn⟩ := hP k; exact (hst n).1.of_prefix hn
    have hokrs : ∀ r ∈ rs, Ok R F r.2.1 :=
      ok_of_okV_sroundsMoves ((hokP 0).of_prefix (List.prefix_append _ _))
    have hokω : ∀ k, Ok R F (streamTake ω k) := fun k =>
      ok_of_okV_callMoves (G := sig1 A B) fun o ho => hokP k o
        (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
    have hall : ∀ k, sumL R F (ω k).1 (.answer (ω k).2) := fun k =>
      hokω (k + 1) (ω k) (by rw [streamTake_succ']; simp)
    have hunb : ∀ N, ∃ k, N ≤ (fCalls (streamTake ω k)).length := fun N => by
      obtain ⟨n, hn⟩ := hu ((sroundsMoves (projR rs)).length + 2 + 2 * N)
      obtain ⟨k, hk⟩ : i.t n ∈ streamPlay (sroundsMoves rs) a ω := hI ▸ Chain.mem_lim_self _ n
      have h₁ := (vis_prefix hk).length_le
      rw [vis_sPlay] at h₁
      simp only [List.length_append, List.length_cons, length_callMoves'] at h₁
      have := hlen n
      exact ⟨k, by omega⟩
    obtain ⟨ω', hω'⟩ := exists_stream_lim (fCalls_mono ω) hunb
    have hlim : i.p.lim = streamPlay (sroundsMoves (projR rs)) a ω' := by
      rw [hpV, lim_map_eq (d := sPlay rs a ω) hI vis vis_prefix]
      exact lim_vis_sPlay rs a hunb hω'
    rw [hlim]
    exact mem_inf.2 ⟨s, rounds_proj hrs hokrs, ω, ⟨hω, hall⟩, hunb, hω'⟩
  · -- infinitely many completed rounds
    have hX : ∀ k, ∃ n, sroundsMoves (streamTake (fun i => (a i, r i)) k) <+: i.t n := fun k => by
      have : sroundsMoves (streamTake (fun i => (a i, r i)) k) ∈ i.t.lim :=
        hI ▸ Chain.mem_lim_self _ k
      exact this
    have hok : ∀ k, Ok R F (r k).1 := fun k => by
      obtain ⟨n, hn⟩ := hX (k + 1)
      refine ok_of_okV_sroundsMoves ((hst n).1.of_prefix hn) (a k, r k) ?_
      rw [streamTake_succ']; simp
    let r' : ℕ → List (Call F) × (B ⊕ PUnit.{u + 1}) := fun k => (fCalls (r k).1, (r k).2)
    have hproj : ∀ k, projR (streamTake (fun i => (a i, r i)) k) =
        streamTake (fun i => (a i, r' i)) k := fun k => by
      simp only [projR, streamTake, List.map_ofFn]; rfl
    have hlim : i.p.lim = sroundsPlay a r' := by
      rw [hpV, lim_map_eq (d := fun k => sroundsMoves (streamTake (fun i => (a i, r i)) k)) hI vis
        vis_prefix]
      simp only [vis_sroundsMoves, hproj]
      rfl
    rw [hlim]
    refine mem_inf_iff.2 (.inr ⟨a, r', rfl, fun k => ?_⟩)
    obtain ⟨s, hs⟩ := hR k
    refine ⟨s, hproj k ▸ rounds_proj hs fun x hx => ?_⟩
    obtain ⟨j, -, rfl⟩ := Silmaril.Games.Abstract.streamTake_mem hx
    exact hok j

/-! ## The backward direction -/

/-- A play of the session with allowed host answers, with its host moves. -/
theorem interaction_of_mem {v : List (Move (E ⊕ₛ F) (sig1 A B))}
    (hv : v ∈ (threadS t s₀).toStrategy) (hok : OkV R v) :
    hmv v ∈ (hostCopy F R).toStrategy ∧ Zip (hmv v) v (vis v) := by
  obtain ⟨g, hg⟩ := (threadS t s₀).toStrategy.legal hv
  exact ⟨⟨_, hrun_hmv hg hok⟩, zip_hmv v⟩

/-- An interaction along a chain of plays of the session with allowed host answers. -/
noncomputable def chainInteraction (v : ℕ → List (Move (E ⊕ₛ F) (sig1 A B)))
    (hv : ∀ k, v k ∈ (threadS t s₀).toStrategy) (hok : ∀ k, OkV R (v k))
    (hm : ∀ k, v k <+: v (k + 1)) (hu : ∀ k, k ≤ (v k).length)
    (hlim : Chain.lim v ∈ (threadS t s₀).inf) :
    DStrategy.InfInteraction (hostCopy F R) (threadS t s₀) where
  s := fun k => hmv (v k)
  t := v
  p := fun k => vis (v k)
  zip := fun k => (interaction_of_mem (hv k) (hok k)).2
  mem_s := fun k => (interaction_of_mem (hv k) (hok k)).1
  mem_t := hv
  mono_s := fun k => hmv_prefix (hm k)
  mono_t := hm
  mono_p := fun k => vis_prefix (hm k)
  unbounded := fun k => ⟨k, by have := hu k; omega⟩
  lim_s := fun hs => ⟨Chain.isInfPlay_lim (fun k => hmv_prefix (hm k)) hs, fun _ ⟨n, hx⟩ =>
    (hostCopy F R).toStrategy.of_prefix (interaction_of_mem (hv n) (hok n)).1 hx⟩
  lim_t := fun _ => hlim

theorem sroundsMoves_mono {X : Sig.{u}} (f : ℕ → A × List (Call X) × (B ⊕ PUnit.{u + 1})) (k : ℕ) :
    sroundsMoves (streamTake f k) <+: sroundsMoves (streamTake f (k + 1)) := by
  rw [streamTake_succ']; simp [sroundsMoves]

theorem le_length_sroundsMoves {X : Sig.{u}} (f : ℕ → A × List (Call X) × (B ⊕ PUnit.{u + 1}))
    (k : ℕ) : k ≤ (sroundsMoves (streamTake f k)).length := by
  have := two_mul_le_sroundsMoves (streamTake f k)
  simp only [length_streamTake'] at this
  omega

theorem inf_bwd (hL : StoreDet (hostLinkS R t)) {I : Set (List (Move F (sig1 A B)))}
    (hI : I ∈ (threadS (hostLinkS R t) s₀).inf) :
    I ∈ ((hostCopy F R).comp (threadS t s₀)).inf := by
  rcases (StratSession.mem_inf_iff_of_storeDet hL).1 hI with ⟨rs', s, a, ω', hrs', hω', rfl⟩ |
    ⟨a, r', st, hIR, rfl⟩
  · -- a linked stream after completed linked rounds
    obtain ⟨rs, hrs, rfl, hokrs⟩ := rounds_lift hrs'
    obtain ⟨ω, hω, hunb, hstr⟩ := hω'
    have hlim : Chain.lim (sPlay rs a ω) ∈ (threadS t s₀).inf := mem_inf.2 ⟨s, hrs, hω.1⟩
    have hv : ∀ k, sPlay rs a ω k ∈ (threadS t s₀).toStrategy := fun k =>
      (threadS t s₀).inf_sub hlim (Chain.mem_lim_self _ k)
    have hok : ∀ k, OkV R (sPlay rs a ω k) := fun k =>
      okV_append.2 ⟨okV_sroundsMoves hokrs,
        okV_cons.2 ⟨trivial, okV_callMoves (hostObsInf_consistent hω k)⟩⟩
    let i := chainInteraction (sPlay rs a ω) hv hok (fun k => sPlay_mono rs a ω (Nat.le_succ k))
      (fun k => by simp [sPlay, length_callMoves']; omega) hlim
    refine ⟨i, fun N => ?_, (lim_vis_sPlay rs a hunb hstr).symm⟩
    obtain ⟨k, hk⟩ := hunb N
    refine ⟨k, ?_⟩
    show N ≤ (vis (sPlay rs a ω k)).length
    rw [vis_sPlay]
    simp only [List.length_append, List.length_cons, length_callMoves']
    omega
  · -- a coherent infinite sequence of linked rounds
    have hlift : ∀ k, ∃ c, (c, End.ret (r' k).2 (st (k + 1))) ∈ t.1 (st k) (a k) ∧ Ok R F c ∧
        (r' k).1 = fCalls c := fun k => by
      rcases hIR.step k with ⟨c, hc, hok, he⟩ | ⟨hd, -⟩
      · exact ⟨c, hc, hok, he⟩
      · cases hd
    choose c hc hokc hfc using hlift
    let r : ℕ → List (Call (E ⊕ₛ F)) × (B ⊕ PUnit.{u + 1}) := fun k => (c k, (r' k).2)
    have hR : InfRounds t s₀ a r st := ⟨hIR.zero, hc⟩
    let v : ℕ → List (Move (E ⊕ₛ F) (sig1 A B)) := fun k =>
      sroundsMoves (streamTake (fun i => (a i, r i)) k)
    have hlim : Chain.lim v ∈ (threadS t s₀).inf := StratSession.InfRounds.mem_sinf hR
    have hv : ∀ k, v k ∈ (threadS t s₀).toStrategy := fun k =>
      (threadS t s₀).inf_sub hlim (Chain.mem_lim_self _ k)
    have hok : ∀ k, OkV R (v k) := fun k => okV_sroundsMoves fun x hx => by
      obtain ⟨j, -, rfl⟩ := Silmaril.Games.Abstract.streamTake_mem hx
      exact hokc j
    have hvis : ∀ k, vis (v k) = sroundsMoves (streamTake (fun i => (a i, r' i)) k) := fun k => by
      simp only [v, vis_sroundsMoves, projR, streamTake, List.map_ofFn]
      congr 2
      funext j
      simp only [r, Function.comp, ← hfc]
    let i := chainInteraction v hv hok (fun k => sroundsMoves_mono _ k)
      (fun k => le_length_sroundsMoves _ k) hlim
    refine ⟨i, fun N => ⟨N, ?_⟩, ?_⟩
    · show N ≤ (vis (v N)).length
      rw [hvis]; exact le_length_sroundsMoves _ N
    · show _ = Chain.lim fun k => vis (v k)
      simp only [hvis]; rfl

/-- **Infinite plays**: those of the composite are linked infinite plays; conversely for a
store-deterministic linked triple. -/
theorem comp_inf (hL : StoreDet (hostLinkS R t)) :
    ((hostCopy F R).comp (threadS t s₀)).inf = (threadS (hostLinkS R t) s₀).inf :=
  Set.ext fun _ => ⟨inf_fwd, inf_bwd hL⟩

end Silmaril.Proofs.Games.Abstract.SessionHost
