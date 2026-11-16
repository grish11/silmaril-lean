module

public import Silmaril.Proofs.Games.Abstract.IterUniformFin.Basic
public import Silmaril.Proofs.Games.Abstract.IterUniformFin.Konig

/-!
# Uniformity of iteration along silent, finitely branching maps (proofs)

Let `h` be silent, trap-free, defined and finitely branching, and
`h ; F = G ; [inl, inr ∘ h]`.

* **From `F` to `G`** (no finiteness needed). A run of `F` from one return `(x, t)` of `h` at
  `(s, a)` lifts iteration by iteration to a run of `G` from `(s, a)`: each continuation of `F`
  into `(x₁, t₁)` is a continuation of `G` into some `(s₁, a₁)` at which `(x₁, t₁)` is again a
  return of `h` (`iterBeh_lift`, `contChain_lift`, `chain_lift`; infinite chains by dependent
  choice). Where `h` may diverge, `iter G` diverges silently (`div_mem_iter`).
* **From `G` to `F`.** A behaviour of `G` at `(s, a)` is one of `F` at *some* return of `h`, so
  a finite run of `G` maps to one of `F` from its end backwards (`step_map`, `contChain_map`).
  An infinite chain of `G` is where finite branching is used. If `h` may diverge somewhere
  along a silent chain, `h ; iter F` diverges silently by the finite argument
  (`div_of_reach`). Otherwise the returns of `h` along the chain form finite nonempty levels,
  and every return at level `n + 1` has a parent at level `n` (a return of `h` at the `n`-th
  point at which `F` continues into it with the `n`-th log). König's lemma (`konig`) gives an
  infinite path, which is a chain of `F` with the same logs (`chain_map`). A productive chain
  of `G` never reaches a point where `h` never returns (`no_reach_noRet`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniformFin

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A A' B : Type u}
  {h : FullFun E S A' A} {F : FullFun E S A (B ⊕ A)} {G : FullFun E S A' (B ⊕ A')}
  (hh : FullFun.SilentFinNoTrap h) (hFG : FullFun.seq h F = FullFun.seq G (caseK h))
include hh hFG

/-! ## From `F` to `G` -/

/-- Where `h` may diverge, `iter G` diverges silently. -/
theorem div_mem_iter {s : S} {a : A'} (hd : ([], End.div) ∈ h.1 s a) :
    ([], End.div) ∈ AFun.iter G.1 s a := by
  by_contra hn
  let Q : ℕ → S × A' → Prop := fun _ p =>
    ([], End.div) ∈ h.1 p.1 p.2 ∧ ([], End.div) ∉ AFun.iter G.1 p.1 p.2
  have step : ∀ n p, Q n p → ∃ p', ([], End.ret (.inr p'.2) p'.1) ∈ G.1 p.1 p.2 ∧ Q (n + 1) p' := by
    rintro n ⟨s₀, a₀⟩ ⟨hd₀, hn₀⟩
    rcases of_mayDiv hh hFG hd₀ with hc | ⟨a₁, s₁, hc, hd₁⟩
    · exact absurd (AFun.IterBeh.div hc) hn₀
    · exact ⟨(s₁, a₁), hc, hd₁, fun hm₁ => hn₀ (AFun.IterBeh.step (c₂ := []) hc hm₁)⟩
  obtain ⟨σ, hσ0, hσ⟩ := exists_chain Q _ step (p₀ := (s, a)) ⟨hd, hn⟩
  exact hn (AFun.IterBeh.spin σ hσ0 fun n => (hσ n).2)

/-- A finite continuing chain of `F` from a return of `h` at `(s, a)` lifts to one of `G` from
`(s, a)`. -/
theorem contChain_lift {t : S} {x : A} {c : List (Call E)} {t' : S} {x' : A}
    (hc : FullFun.ContChain F.1 t x c t' x') :
    ∀ s a, ([], End.ret x t) ∈ h.1 s a →
      ∃ s' a', FullFun.ContChain G.1 s a c s' a' ∧ ([], End.ret x' t') ∈ h.1 s' a' := by
  induction hc with
  | refl => exact fun s a hr => ⟨s, a, .refl, hr⟩
  | step hm _ ih =>
    intro s a hr
    obtain ⟨a₁, s₁, hm₁, hr₁⟩ := cont_of_F hh hFG hr hm
    obtain ⟨s', a', hc', hr'⟩ := ih s₁ a₁ hr₁
    exact ⟨s', a', .step hm₁ hc', hr'⟩

/-- An infinite continuing chain of `F` from a return of `h` at `(s, a)` lifts to one of `G`
from `(s, a)`, with the same logs. -/
theorem chain_lift {s : S} {a : A'} {τ : ℕ → S × A} {l : ℕ → List (Call E)}
    (h0 : ([], End.ret (τ 0).2 (τ 0).1) ∈ h.1 s a)
    (hτ : ∀ n, (l n, End.ret (.inr (τ (n + 1)).2) (τ (n + 1)).1) ∈ F.1 (τ n).1 (τ n).2) :
    ∃ σ : ℕ → S × A', σ 0 = (s, a) ∧
      ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ G.1 (σ n).1 (σ n).2 := by
  obtain ⟨σ, hσ0, hσ⟩ := exists_chain (fun n p => ([], End.ret (τ n).2 (τ n).1) ∈ h.1 p.1 p.2)
    (fun n p p' => (l n, End.ret (.inr p'.2) p'.1) ∈ G.1 p.1 p.2)
    (fun n p hp => by
      obtain ⟨a₁, s₁, hm₁, hr₁⟩ := cont_of_F hh hFG hp (hτ n)
      exact ⟨(s₁, a₁), hm₁, hr₁⟩) (p₀ := (s, a)) h0
  exact ⟨σ, hσ0, fun n => (hσ n).2⟩

/-- A finite behaviour of `iter F` from a return of `h` at `(s, a)` is one of `iter G` from
`(s, a)`. -/
theorem iterBeh_lift {t : S} {x : A} {y : CallBeh E S B} (hy : AFun.IterBeh F.1 t x y) :
    ∀ s a, ([], End.ret x t) ∈ h.1 s a → AFun.IterBeh G.1 s a y := by
  induction hy with
  | exit hm => exact fun s a hr => .exit (exit_of_F hh hFG hr hm)
  | trap hm => exact fun s a hr => .trap (trap_of_F hh hFG hr hm)
  | div hm =>
    intro s a hr
    rcases div_of_F hh hFG hr hm with hm' | ⟨a₁, s₁, hm₁, hd₁⟩
    · exact .div hm'
    · have := AFun.IterBeh.step hm₁ (div_mem_iter hh hFG hd₁)
      rwa [List.append_nil] at this
  | step hm _ ih =>
    intro s a hr
    obtain ⟨a₁, s₁, hm₁, hr₁⟩ := cont_of_F hh hFG hr hm
    exact .step hm₁ (ih s₁ a₁ hr₁)
  | spin τ h0 hτ =>
    intro s a hr
    obtain ⟨σ, hσ0, hσ⟩ := chain_lift hh hFG (l := fun _ => []) (by rw [h0]; exact hr) hτ
    exact .spin σ hσ0 hσ

/-! ## From `G` to `F` -/

/-- **One step back**: a continuation of `G` followed by a behaviour of `h ; iter F` is a
behaviour of `h ; iter F`. -/
theorem step_map {s : S} {a : A'} {c₁ : List (Call E)} {a₁ : A'} {s₁ : S}
    (hm : (c₁, End.ret (.inr a₁) s₁) ∈ G.1 s a) {c₂ : List (Call E)} {e : End S B}
    (hy : (c₂, e) ∈ (FullFun.seq h (FullFun.iter F)).1 s₁ a₁) :
    (c₁ ++ c₂, e) ∈ (FullFun.seq h (FullFun.iter F)).1 s a := by
  rcases (mem_seq hh).1 hy with ⟨hd₁, he⟩ | ⟨x₁, t₁, hr₁, hy₁⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rw [List.append_nil]
    rcases contDiv_of_G hh hFG hm hd₁ with ⟨hd, rfl⟩ | ⟨x, t, hr, hm'⟩
    · exact (mem_seq hh).2 (.inl ⟨hd, rfl⟩)
    · exact (mem_seq hh).2 (.inr ⟨x, t, hr, AFun.IterBeh.div hm'⟩)
  · obtain ⟨x, t, hr, hm'⟩ := cont_of_G hh hFG hm hr₁
    exact (mem_seq hh).2 (.inr ⟨x, t, hr, AFun.IterBeh.step hm' hy₁⟩)

/-- A finite continuing chain of `G` ending at a return of `h` maps to one of `F`. -/
theorem contChain_map {s : S} {a : A'} {c : List (Call E)} {s' : S} {a' : A'}
    (hc : FullFun.ContChain G.1 s a c s' a') :
    ∀ x' t', ([], End.ret x' t') ∈ h.1 s' a' →
      ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ FullFun.ContChain F.1 t x c t' x' := by
  induction hc with
  | refl => exact fun x' t' hr => ⟨x', t', hr, .refl⟩
  | step hm _ ih =>
    intro x' t' hr'
    obtain ⟨x₁, t₁, hr₁, hc₁⟩ := ih x' t' hr'
    obtain ⟨x, t, hr, hm'⟩ := cont_of_G hh hFG hm hr₁
    exact ⟨x, t, hr, .step hm' hc₁⟩

/-- Along a silent chain of `G`, reaching a point where `h` may diverge gives a silent
divergence of `h ; iter F`. -/
theorem div_of_reach {σ : ℕ → S × A'}
    (hσ : ∀ n, ([], End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ G.1 (σ n).1 (σ n).2) :
    ∀ d n, ([], End.div) ∈ h.1 (σ (n + d)).1 (σ (n + d)).2 →
      ([], End.div) ∈ (FullFun.seq h (FullFun.iter F)).1 (σ n).1 (σ n).2 := by
  intro d
  induction d with
  | zero => exact fun n hd => (mem_seq hh).2 (.inl ⟨hd, rfl⟩)
  | succ d ih =>
    intro n hd
    have := step_map hh hFG (hσ n) (ih (n + 1) (by rw [Nat.add_right_comm]; exact hd))
    rwa [List.append_nil] at this

omit hFG in
/-- The returns of a finitely branching map at one point are finitely many. -/
theorem rets_finite (s : S) (a : A') :
    {q : A × S | ([], End.ret q.1 q.2) ∈ h.1 s a}.Finite :=
  Set.Finite.preimage (f := fun q : A × S => (([] : List (Call E)), End.ret q.1 q.2))
    (fun ⟨x, t⟩ _ ⟨x', t'⟩ _ he => by
      injection he with _ he
      injection he with h₁ h₂
      exact Prod.ext h₁ h₂) (hh.2.2.2 s a)

/-- **König step**: an infinite chain of `G` along which `h` always may return maps to an
infinite chain of `F` with the same logs, starting at a return of `h` at its first point. -/
theorem chain_map {σ : ℕ → S × A'} {l : ℕ → List (Call E)}
    (hσ : ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ G.1 (σ n).1 (σ n).2)
    (hret : ∀ n, ¬ NoRet h (σ n).1 (σ n).2) :
    ∃ τ : ℕ → S × A, ([], End.ret (τ 0).2 (τ 0).1) ∈ h.1 (σ 0).1 (σ 0).2 ∧
      ∀ n, (l n, End.ret (.inr (τ (n + 1)).2) (τ (n + 1)).1) ∈ F.1 (τ n).1 (τ n).2 := by
  obtain ⟨q, hq⟩ := konig (L := fun n => {q : A × S | ([], End.ret q.1 q.2) ∈ h.1 (σ n).1 (σ n).2})
    (R := fun n (q q' : A × S) => (l n, End.ret (.inr q'.1) q'.2) ∈ F.1 q.2 q.1)
    (fun n => rets_finite hh _ _)
    (fun n => by
      have hn := hret n
      simp only [NoRet, not_forall, not_not] at hn
      obtain ⟨x, t, hr⟩ := hn
      exact ⟨(x, t), hr⟩)
    (fun n q hq => by
      obtain ⟨x, t, hr, hm⟩ := cont_of_G hh hFG (hσ n) hq
      exact ⟨(x, t), hr, hm⟩)
  exact ⟨fun n => ((q n).2, (q n).1), (hq 0).1, fun n => (hq n).2⟩

/-- A finite behaviour of `iter G` is one of `h ; iter F`. -/
theorem iterBeh_map {s : S} {a : A'} {y : CallBeh E S B} (hy : AFun.IterBeh G.1 s a y) :
    y ∈ (FullFun.seq h (FullFun.iter F)).1 s a := by
  induction hy with
  | exit hm =>
    obtain ⟨x, t, hr, hm'⟩ := exit_of_G hh hFG hm
    exact (mem_seq hh).2 (.inr ⟨x, t, hr, AFun.IterBeh.exit hm'⟩)
  | trap hm =>
    obtain ⟨x, t, hr, hm'⟩ := trap_of_G hh hFG hm
    exact (mem_seq hh).2 (.inr ⟨x, t, hr, AFun.IterBeh.trap hm'⟩)
  | div hm =>
    rcases div_of_G hh hFG hm with ⟨hd, rfl⟩ | ⟨x, t, hr, hm'⟩
    · exact (mem_seq hh).2 (.inl ⟨hd, rfl⟩)
    · exact (mem_seq hh).2 (.inr ⟨x, t, hr, AFun.IterBeh.div hm'⟩)
  | step hm _ ih => exact step_map hh hFG hm ih
  | @spin s a σ h0 hσ =>
    by_cases hreach : ∃ d, ([], End.div) ∈ h.1 (σ d).1 (σ d).2
    · obtain ⟨d, hd⟩ := hreach
      have := div_of_reach hh hFG hσ d 0 (by rw [Nat.zero_add]; exact hd)
      rwa [h0] at this
    · have hret : ∀ n, ¬ NoRet h (σ n).1 (σ n).2 := fun n hn => by
        obtain ⟨y, hy⟩ := hh.2.2.1 (σ n).1 (σ n).2
        rcases beh_cases hh hy with rfl | ⟨x, t, rfl⟩
        · exact hreach ⟨n, hy⟩
        · exact hn x t hy
      obtain ⟨τ, hτ0, hτ⟩ := chain_map hh hFG hσ hret
      rw [h0] at hτ0
      exact (mem_seq hh).2 (.inr ⟨_, _, hτ0, AFun.IterBeh.spin τ rfl hτ⟩)

/-- **Uniformity of iteration**, finite behaviours. -/
theorem iter_fin_eq (s : S) (a : A') :
    (FullFun.seq h (FullFun.iter F)).1 s a = AFun.iter G.1 s a := by
  ext y
  constructor
  · intro hy
    rcases (mem_seq hh).1 hy with ⟨hd, rfl⟩ | ⟨x, t, hr, hy'⟩
    · exact div_mem_iter hh hFG hd
    · exact iterBeh_lift hh hFG hy' s a hr
  · exact iterBeh_map hh hFG

omit hh hFG in
/-- The total length of the first `n` segments. -/
theorem flatMap_range_length_succ {α : Type u} (l : ℕ → List α) (n : ℕ) :
    ((List.range (n + 1)).flatMap l).length = ((List.range n).flatMap l).length + (l n).length := by
  rw [List.range_succ, List.flatMap_append, List.length_append]
  simp

omit hh hFG in
theorem flatMap_range_length_mono {α : Type u} (l : ℕ → List α) {n m : ℕ} (hnm : n ≤ m) :
    ((List.range n).flatMap l).length ≤ ((List.range m).flatMap l).length := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => rw [flatMap_range_length_succ]; omega

omit hh hFG in
/-- Segments that are eventually empty have bounded total length. -/
theorem flatMap_range_length_le {α : Type u} {l : ℕ → List α} {m : ℕ}
    (hl : ∀ n, m ≤ n → l n = []) (n : ℕ) :
    ((List.range n).flatMap l).length ≤ ((List.range m).flatMap l).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : m ≤ n
    · rw [flatMap_range_length_succ, hl n hn]; simpa using ih
    · exact flatMap_range_length_mono l (by omega)

/-- An infinite productive chain of `G` never reaches a point where `h` never returns. -/
theorem no_reach_noRet {σ : ℕ → S × A'} {l : ℕ → List (Call E)} {ω : ℕ → Call E}
    (hσ : ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ G.1 (σ n).1 (σ n).2)
    (hl : Shape.StreamConcat l ω) (m : ℕ) : ¬ NoRet h (σ m).1 (σ m).2 := by
  intro hn
  have hall : ∀ k, NoRet h (σ (m + k)).1 (σ (m + k)).2 ∧ l (m + k) = [] := by
    intro k
    induction k with
    | zero => exact ⟨hn, (of_noRet hh hFG hn (hσ m)).1⟩
    | succ k ih =>
      have hn₁ : NoRet h (σ (m + k + 1)).1 (σ (m + k + 1)).2 :=
        (of_noRet hh hFG ih.1 (hσ (m + k))).2
      exact ⟨hn₁, (of_noRet hh hFG hn₁ (hσ (m + k + 1))).1⟩
  have hnil : ∀ n, m ≤ n → l n = [] := fun n hn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (hall k).2
  obtain ⟨n, hn⟩ := hl.2 (((List.range m).flatMap l).length + 1)
  have := flatMap_range_length_le hnil n
  omega

/-- **Uniformity of iteration**, productive runs. -/
theorem iter_inf_eq (s : S) (a : A') :
    (FullFun.seq h (FullFun.iter F)).2 s a = (FullFun.iter G).2 s a := by
  ext ω
  constructor
  · intro hω
    obtain ⟨x, t, hr, hω⟩ := (mem_seq_inf hh).1 hω
    rcases hω with ⟨c, t', x', ω', hc, hω', rfl⟩ | ⟨τ, l, h0, hτ, hl⟩
    · obtain ⟨s', a', hc', hr'⟩ := contChain_lift hh hFG hc s a hr
      exact .inl ⟨c, s', a', ω', hc', inf_of_F hh hFG hr' hω', rfl⟩
    · obtain ⟨σ, hσ0, hσ⟩ := chain_lift hh hFG (by rw [h0]; exact hr) hτ
      exact .inr ⟨σ, l, hσ0, hσ, hl⟩
  · rintro (⟨c, s', a', ω', hc, hω', rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · obtain ⟨x', t', hr', hω''⟩ := inf_of_G hh hFG hω'
      obtain ⟨x, t, hr, hc'⟩ := contChain_map hh hFG hc x' t' hr'
      exact (mem_seq_inf hh).2 ⟨x, t, hr, .inl ⟨c, t', x', ω', hc', hω'', rfl⟩⟩
    · obtain ⟨τ, hτ0, hτ⟩ := chain_map hh hFG hσ (no_reach_noRet hh hFG hσ hl)
      rw [h0] at hτ0
      exact (mem_seq_inf hh).2 ⟨_, _, hτ0, .inr ⟨τ, l, rfl, hτ, hl⟩⟩

/-- **Uniformity of iteration** along a silent, trap-free, defined, finitely branching map. -/
theorem iter_uniform : FullFun.seq h (FullFun.iter F) = FullFun.iter G :=
  Prod.ext (funext fun s => funext fun a => iter_fin_eq hh hFG s a)
    (funext fun s => funext fun a => iter_inf_eq hh hFG s a)

end Silmaril.Proofs.Games.Abstract.IterUniformFin
