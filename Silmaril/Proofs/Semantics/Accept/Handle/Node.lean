module

public import Silmaril.Semantics.Accept.Handle.Defs
public import Mathlib.Logic.Relation

/-! # Proofs: node environments unfold to finite trees only -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle

universe u v w

variable {H : Type u} {N : Type v} {X : Type w} {mk : N → List X → Option X} {ν : NodeEnv H N}

theorem forall₂_eq_of {α β : Type*} {P : α → β → Prop} {P' : α → β → Prop}
    (h : ∀ a b b', P a b → P' a b' → b = b') :
    ∀ {as : List α} {bs bs' : List β}, List.Forall₂ P as bs → List.Forall₂ P' as bs' → bs = bs'
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => by
      rw [h _ _ _ h₁ h₂, forall₂_eq_of h t₁ t₂]

theorem unfoldN_functional :
    ∀ (n k : Nat) {h : H} {x y : X}, UnfoldN mk ν n h x → UnfoldN mk ν k h y → x = y
  | 0, _, _, _, _, hx, _ => hx.elim
  | _ + 1, 0, _, _, _, _, hy => hy.elim
  | n + 1, k + 1, _, _, _, ⟨m, hs, xs, hν, hF, hmk⟩, ⟨m', hs', ys, hν', hF', hmk'⟩ => by
      rw [hν] at hν'
      simp only [Option.some.injEq, Prod.mk.injEq] at hν'
      obtain ⟨rfl, rfl⟩ := hν'
      have : xs = ys := forall₂_eq_of (P := UnfoldN mk ν n) (P' := UnfoldN mk ν k)
        (fun _ _ _ h₁ h₂ => unfoldN_functional n k h₁ h₂) hF hF'
      subst this
      rw [hmk] at hmk'
      exact Option.some.inj hmk'

theorem unfold_functional {h : H} {x y : X} (hx : Unfold mk ν h x) (hy : Unfold mk ν h y) :
    x = y :=
  let ⟨n, hn⟩ := hx
  let ⟨k, hk⟩ := hy
  unfoldN_functional n k hn hk

theorem forall₂_mem_left {α β : Type*} {P : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ P as bs → ∀ a ∈ as, ∃ b ∈ bs, P a b
  | [], [], .nil, _, ha => by simp at ha
  | _ :: _, _ :: _, .cons h₁ t₁, a, ha => by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨_, List.mem_cons_self, h₁⟩
      · obtain ⟨b, hb, hP⟩ := forall₂_mem_left t₁ a ha
        exact ⟨b, List.mem_cons_of_mem _ hb, hP⟩

/-- A child of an unfolded handle unfolds to a strictly smaller tree. -/
theorem unfold_child {size : X → Nat} (hsize : ∀ ⦃m xs x⦄, mk m xs = some x → ∀ c ∈ xs, size c < size x)
    {h h' : H} (hc : ν.Child h' h) {x : X} (hx : Unfold mk ν h x) :
    ∃ x', Unfold mk ν h' x' ∧ size x' < size x := by
  obtain ⟨n, hn⟩ := hx
  cases n with
  | zero => exact hn.elim
  | succ n =>
      obtain ⟨m, hs, xs, hν, hF, hmk⟩ := hn
      obtain ⟨m', hs', hν', hmem⟩ := hc
      rw [hν] at hν'
      simp only [Option.some.injEq, Prod.mk.injEq] at hν'
      obtain ⟨rfl, rfl⟩ := hν'
      obtain ⟨x', hx', hP⟩ := forall₂_mem_left hF h' hmem
      exact ⟨x', ⟨n, hP⟩, hsize hmk x' hx'⟩

theorem unfold_transGen {size : X → Nat}
    (hsize : ∀ ⦃m xs x⦄, mk m xs = some x → ∀ c ∈ xs, size c < size x) {h h' : H}
    (hc : Relation.TransGen ν.Child h' h) :
    ∀ {x : X}, Unfold mk ν h x → ∃ x', Unfold mk ν h' x' ∧ size x' < size x := by
  induction hc with
  | single hc => exact fun hx => unfold_child hsize hc hx
  | tail _ hc ih =>
      intro x hx
      obtain ⟨y, hy, hlt⟩ := unfold_child hsize hc hx
      obtain ⟨z, hz, hlt'⟩ := ih hy
      exact ⟨z, hz, hlt'.trans hlt⟩

/-- **A handle on a cycle unfolds to nothing.** -/
theorem not_unfold_of_cycle {size : X → Nat}
    (hsize : ∀ ⦃m xs x⦄, mk m xs = some x → ∀ c ∈ xs, size c < size x) {h : H}
    (hc : Relation.TransGen ν.Child h h) (x : X) : ¬ Unfold mk ν h x := by
  induction hn : size x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
      intro hx
      obtain ⟨x', hx', hlt⟩ := unfold_transGen hsize hc hx
      exact ih (size x') (hn ▸ hlt) x' rfl hx'


theorem realize_realizes : Realizes mk ν (realize mk ν) := by
  intro h x
  unfold realize
  split
  · rename_i hx
    exact ⟨fun e => Option.some.inj e ▸ hx.choose_spec,
      fun h' => congrArg some (unfold_functional hx.choose_spec h')⟩
  · rename_i hx
    exact ⟨fun e => (by cases e), fun h' => absurd ⟨x, h'⟩ hx⟩

theorem realizes_unique {ρ ρ' : Env H X} (h : Realizes mk ν ρ) (h' : Realizes mk ν ρ') :
    ρ = ρ' := by
  funext k
  rcases hk : ρ k with _ | x
  · rcases hk' : ρ' k with _ | y
    · rfl
    · exact absurd ((h k y).2 ((h' k y).1 hk')) (by simp [hk])
  · exact ((h' k x).2 ((h k x).1 hk)).symm

end Silmaril.Proofs.Semantics.Accept.Handle
