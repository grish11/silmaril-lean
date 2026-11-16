module

public import Silmaril.Games.Abstract.SessionHostCex.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DPair.Defs
public import Silmaril.Games.DivComp.Defs

/-!
# Sessions with host imports: a non-coherent linked triple

The component's first round asks the host for some `n`, and `n` bounds its later rounds. The host
call is hidden by linking, so the linked triple has every finite number of rounds from `none`, and
the linked session plays `unitRounds`. An infinite interaction playing `unitRounds` either moves
the component forever, which bounds its rounds by the host answer of its first round (`lim_t`), or
moves it finitely, which bounds the visible play by the component's moves (`zip_length_le`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionHostCex

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionHost Silmaril.Games.Abstract.SessionHostCex

variable {F : Sig.{0}}

/-! ## Streams, rounds and interactions -/

theorem streamTake_const {α : Type} (x : α) (n : ℕ) :
    streamTake (fun _ => x) n = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, ← ih]; simp [streamTake, List.ofFn_succ]

theorem streamTake_succ {α : Type} (ω : ℕ → α) (n : ℕ) :
    streamTake ω (n + 1) = ω 0 :: streamTake (fun i => ω (i + 1)) n := by
  simp [streamTake, List.ofFn_succ]

theorem rounds_cons_iff {E : Sig.{0}} {S A B : Type} {t : ObsTriple E S A B} {s s₂ : S}
    {x : A × List (Call E) × B} {rs : List (A × List (Call E) × B)} :
    Rounds t s (x :: rs) s₂ ↔ ∃ s₁, (x.2.1, End.ret x.2.2 s₁) ∈ t.1 s x.1 ∧ Rounds t s₁ rs s₂ := by
  constructor
  · rintro (_ | ⟨h, hr⟩)
    exact ⟨_, h, hr⟩
  · rintro ⟨_, h, hr⟩
    exact .cons h hr

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
    ∀ x ∈ sroundsMoves (List.replicate k ((), ([] : List (Call F)), (.inl () : Unit ⊕ Unit))),
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

/-! ## The component -/

theorem det_boundHostComp : AFun.Det (boundHostComp (F := F)).1 := by
  rintro s a x y (⟨rfl, n, rfl⟩ | ⟨n, rfl, rfl⟩) hy
  · rcases hy with ⟨-, n', rfl⟩ | ⟨_, h, _⟩
    · refine ⟨rfl, fun h => ?_⟩
      cases eq_of_heq h
      rfl
    · cases h
  · rcases hy with ⟨h, _⟩ | ⟨n', h, rfl⟩
    · cases h
    · cases h
      rfl

theorem consistent_pickCall (k : ℕ) : (sumL pickHost F).Consistent [pickCall k] := by
  intro c hc
  cases List.mem_singleton.1 hc
  exact ⟨k, rfl⟩

theorem hostLinkS_ret_none (k : ℕ) :
    (([] : List (Call F)), End.ret (Sum.inl ()) (some k)) ∈
      (hostLinkS pickHost (boundHostComp (F := F))).1 none () :=
  .inl ⟨[pickCall k], .inl ⟨rfl, k, rfl⟩, consistent_pickCall k, rfl⟩

theorem not_storeDet_hostLinkS : ¬ StoreDet (hostLinkS pickHost (boundHostComp (F := F))) := by
  intro h
  have := h _ _ _ _ _ _ (hostLinkS_ret_none (F := F) 0) (hostLinkS_ret_none 1)
  simp at this

theorem hostLink_down (j : ℕ) :
    Rounds (hostLinkS pickHost (boundHostComp (F := F))) (some j)
      (List.replicate j ((), [], .inl ())) (some 0) := by
  induction j with
  | zero => exact .nil _
  | succ j ih =>
    rw [List.replicate_succ]
    have h : (([] : List (Call (pickSig ⊕ₛ F))), End.ret (Sum.inl ()) (some j)) ∈
        (boundHostComp (F := F)).1 (some (j + 1)) () := .inr ⟨j, rfl, rfl⟩
    exact .cons (.inl ⟨[], h, (fun _ h => nomatch h), rfl⟩) ih

theorem unitRounds_mem_hostLinkS :
    unitRounds ∈ (threadS (hostLinkS pickHost (boundHostComp (F := F))) none).inf := by
  refine mem_inf_iff.2 (.inr ⟨_, _, rfl, fun k => ?_⟩)
  show ∃ s, Rounds _ _ (streamTake (fun _ => ((), [], Sum.inl ())) k) s
  rw [streamTake_const]
  cases k with
  | zero => exact ⟨_, .nil _⟩
  | succ k =>
    rw [List.replicate_succ]
    exact ⟨_, .cons (hostLinkS_ret_none k) (hostLink_down k)⟩

/-! ## No interaction plays `unitRounds` -/

theorem bound_some_length {m : ℕ}
    {rs : List (Unit × List (Call (pickSig ⊕ₛ F)) × (Unit ⊕ Unit))} {s : Option ℕ}
    (h : Rounds boundHostComp (some m) rs s) : rs.length ≤ m := by
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

theorem bound_none_call {x : Unit × List (Call (pickSig ⊕ₛ F)) × (Unit ⊕ Unit)}
    {rs : List (Unit × List (Call (pickSig ⊕ₛ F)) × (Unit ⊕ Unit))} {s : Option ℕ}
    (h : Rounds boundHostComp none (x :: rs) s) :
    ∃ n, x.2.1 = [pickCall n] ∧ rs.length ≤ n := by
  obtain ⟨s₁, hx, hr⟩ := rounds_cons_iff.1 h
  rcases hx with ⟨-, n, hx⟩ | ⟨n, h', _⟩
  · simp only [Prod.mk.injEq, End.ret.injEq] at hx
    rw [hx.2.2] at hr
    exact ⟨n, hx.1, bound_some_length hr⟩
  · cases h'

theorem unitRounds_not_mem_comp :
    unitRounds ∉ (((hostDOn F pickHost).pair (DStrategy.id F)).comp
      (threadS (boundHostComp (F := F)) none)).inf := by
  rintro ⟨i, hu, hI⟩
  by_cases ht : i.t.Unbounded
  · rcases mem_inf_iff.1 (i.lim_t ht) with ⟨_, _, _, _, _, hω, _⟩ | ⟨a, r, -, hk⟩
    · simp [boundHostComp] at hω
    obtain ⟨_, h₁⟩ := hk 1
    rw [streamTake_succ] at h₁
    obtain ⟨n, hn, -⟩ := bound_none_call h₁
    obtain ⟨_, h₂⟩ := hk (n + 2)
    rw [streamTake_succ] at h₂
    obtain ⟨n', hn', hl⟩ := bound_none_call h₂
    rw [hn] at hn'
    cases (List.cons.inj hn').1
    simp [streamTake] at hl
    omega
  · simp only [Chain.Unbounded, not_forall, not_exists, not_le] at ht
    obtain ⟨K, hK⟩ := ht
    obtain ⟨n, hn⟩ := hu K
    have hmem : i.p n ∈ unitRounds (F := F) := hI ▸ ⟨n, List.prefix_refl _⟩
    obtain ⟨k, hk⟩ := hmem
    have hp : ∀ x ∈ i.p n, ∃ c, x = .inr c := fun x hx =>
      mem_sroundsMoves_unit k x (by rw [← streamTake_const]; exact hk.subset hx)
    have := zip_length_le (i.zip n) hp
    have := hK n
    omega

end Silmaril.Proofs.Games.Abstract.SessionHostCex
