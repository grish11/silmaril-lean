module

public import Silmaril.Proofs.Games.Abstract.SessionLinkCex.Basic
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DivComp.Defs

/-!
# Linking counterexamples: a non-coherent linked triple

The client's first round calls the echo server with some `n`, and `n` bounds its later rounds.
The call is hidden by linking, so the linked triple has every finite number of rounds from
`((), none)`, and the linked session plays `unitRounds`. An infinite interaction playing
`unitRounds` either moves the client forever, which bounds its rounds by the call of its first
round (`lim_t`), or moves it finitely, which bounds the visible play by the client's moves
(`zip_length_le`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCex

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionLinkCex

variable {E : Sig.{0}}

theorem noPlainTrap_echoServer : NoPlainTrap (echoServer (E := E)) := by
  intro _ _ _ h
  simp [echoServer] at h

theorem det_echoServer : AFun.Det (echoServer (E := E)).1 := by
  rintro _ _ x y hx hy
  simp only [echoServer, Set.mem_singleton_iff] at hx hy
  subst hx hy
  rfl

theorem storeDet_boundClient : StoreDet boundClient := by
  rintro s a c b s₁ s₂ (⟨rfl, n, x, h⟩ | ⟨n, rfl, h⟩) h₂
  · rcases h₂ with ⟨-, n', x', h'⟩ | ⟨_, h', _⟩
    · simp only [Prod.mk.injEq, End.ret.injEq] at h h'
      obtain ⟨rfl, -, rfl⟩ := h
      obtain ⟨h', -, rfl⟩ := h'
      simp only [List.cons.injEq, Sigma.mk.injEq] at h'
      rw [h'.1.1]
    · cases h'
  · rcases h₂ with ⟨h', _⟩ | ⟨n', h', h''⟩
    · cases h'
    · simp only [Prod.mk.injEq, End.ret.injEq] at h h''
      cases h'
      rw [h.2.2, h''.2.2]

theorem linkS_bound_ret_none (k : ℕ) :
    (([] : List (Call E)), End.ret (Sum.inl ()) ((), some k)) ∈
      (linkS (echoServer (E := E)) boundClient).1 ((), none) () :=
  .inl ⟨[(k, [], .inl ())], (), _, .cons rfl (.nil _), .inl ⟨rfl, k, .inl (), rfl⟩, rfl⟩

theorem not_storeDet_linkS_bound : ¬ StoreDet (linkS (echoServer (E := E)) boundClient) := by
  intro h
  have := h _ _ _ _ _ _ (linkS_bound_ret_none 0) (linkS_bound_ret_none 1)
  simp at this

theorem link_down (j : ℕ) :
    Rounds (linkS (echoServer (E := E)) boundClient) ((), some j)
      (List.replicate j ((), [], .inl ())) ((), some 0) := by
  induction j with
  | zero => exact .nil _
  | succ j ih =>
    rw [List.replicate_succ]
    exact .cons (.inl ⟨[], (), _, .nil _, .inr ⟨j, rfl, rfl⟩, rfl⟩) ih

theorem unitRounds_mem_linkS :
    unitRounds ∈ (threadS (linkS (echoServer (E := E)) boundClient) ((), none)).inf := by
  refine mem_inf_iff.2 (.inr ⟨_, _, rfl, fun k => ?_⟩)
  show ∃ s, Rounds _ _ (streamTake (fun _ => ((), [], Sum.inl ())) k) s
  rw [streamTake_const]
  cases k with
  | zero => exact ⟨_, .nil _⟩
  | succ k =>
    rw [List.replicate_succ]
    exact ⟨_, .cons (linkS_bound_ret_none k) (link_down k)⟩

/-! ## No interaction plays `unitRounds` -/

theorem bound_some_length {m : ℕ} {rs : List (Unit × List (Call (sig1 ℕ Unit)) × (Unit ⊕ Unit))}
    {s : Option ℕ} (h : Rounds boundClient (some m) rs s) : rs.length ≤ m := by
  induction rs generalizing m with
  | nil => simp
  | cons x rs ih =>
    obtain ⟨s₁, hx, hr⟩ := rounds_cons_iff.1 h
    rcases hx with ⟨h', _⟩ | ⟨n, h', hx⟩
    · cases h'
    · cases h'
      simp only [Prod.mk.injEq, End.ret.injEq] at hx
      rw [hx.2.2] at hr
      have := ih hr
      simp only [List.length_cons]; omega

theorem bound_none_call {x : Unit × List (Call (sig1 ℕ Unit)) × (Unit ⊕ Unit)}
    {rs : List (Unit × List (Call (sig1 ℕ Unit)) × (Unit ⊕ Unit))} {s : Option ℕ}
    (h : Rounds boundClient none (x :: rs) s) :
    ∃ n y, x.2.1 = [⟨n, y⟩] ∧ rs.length ≤ n := by
  obtain ⟨s₁, hx, hr⟩ := rounds_cons_iff.1 h
  rcases hx with ⟨-, n, y, hx⟩ | ⟨n, h', _⟩
  · simp only [Prod.mk.injEq, End.ret.injEq] at hx
    rw [hx.2.2] at hr
    exact ⟨n, y, hx.1, bound_some_length hr⟩
  · cases h'

theorem zip_length_le {α β γ : Type} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (hp : ∀ x ∈ p, ∃ c, x = .inr c) : p.length ≤ t.length := by
  induction h with
  | nil => simp
  | left a _ _ => obtain ⟨_, h⟩ := hp _ (List.mem_cons_self ..); cases h
  | right c _ ih =>
    have := ih fun x hx => hp x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons]; omega
  | sync b _ ih => have := ih hp; simp only [List.length_cons]; omega

theorem mem_sroundsMoves_unit (k : ℕ) :
    ∀ x ∈ sroundsMoves (List.replicate k ((), ([] : List (Call E)), (.inl () : Unit ⊕ Unit))),
      ∃ c, x = .inr c := by
  induction k with
  | zero => simp [sroundsMoves]
  | succ k ih =>
    rw [List.replicate_succ]
    intro x hx
    change x ∈ _ :: _ :: _ at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, rfl⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, rfl⟩
    exact ih x hx

theorem unitRounds_not_mem_comp :
    unitRounds ∉ ((threadS (echoServer (E := E)) ()).comp (threadS boundClient none)).inf := by
  rintro ⟨i, hu, hI⟩
  by_cases ht : i.t.Unbounded
  · rcases mem_inf_iff.1 (i.lim_t ht) with ⟨_, _, _, _, _, hω, _⟩ | ⟨a, r, -, hk⟩
    · simp [boundClient] at hω
    obtain ⟨_, h₁⟩ := hk 1
    rw [streamTake_succ] at h₁
    obtain ⟨n, y, hn, -⟩ := bound_none_call h₁
    obtain ⟨_, h₂⟩ := hk (n + 2)
    rw [streamTake_succ] at h₂
    obtain ⟨n', y', hn', hl⟩ := bound_none_call h₂
    rw [hn] at hn'
    simp only [List.cons.injEq, Sigma.mk.injEq] at hn'
    rw [← hn'.1.1] at hl
    simp [streamTake] at hl
    omega
  · simp only [Chain.Unbounded, not_forall, not_exists, not_le] at ht
    obtain ⟨K, hK⟩ := ht
    obtain ⟨n, hn⟩ := hu K
    have hmem : i.p n ∈ unitRounds (E := E) := hI ▸ ⟨n, List.prefix_refl _⟩
    obtain ⟨k, hk⟩ := hmem
    have hp : ∀ x ∈ i.p n, ∃ c, x = .inr c := fun x hx =>
      mem_sroundsMoves_unit k x (by rw [← streamTake_const]; exact hk.subset hx)
    have := zip_length_le (i.zip n) hp
    have := hK n
    omega

end Silmaril.Proofs.Games.Abstract.SessionLinkCex
