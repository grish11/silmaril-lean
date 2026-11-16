module

public import Silmaril.Proofs.Games.Abstract.IterUniform.Basic

/-!
# Uniformity of iteration along silent, deterministic, trap-free maps (proofs)

Let `h` be silent, deterministic, trap-free and defined, and `h ; F = G ; [inl, inr ∘ h]`.

* **From `F` to `G`.** Where `h` returns `(x, t)` at `(s, a)`, a run of `F` from `(t, x)` lifts
  iteration by iteration to a run of `G` from `(s, a)` (`iterBeh_lift`, `contChain_lift`,
  `chain_lift`; infinite chains by dependent choice). A divergence of `F` may come from a
  continuation of `G` into a point where `h` diverges; there `G` diverges silently or continues
  silently to such points, so `iter G` diverges silently (`div_mem_iter`).
* **From `G` to `F`.** A run of `G` maps to a run of `F` by applying `h` to every continuing
  point (`iterBeh_map`, `contChain_map`). Where `h` diverges, `h ; iter F` diverges silently
  and every run of `G` stays silent among such points. An infinite silent chain of `G` that
  reaches such a point gives a finite silent chain of `F` ending in a divergence
  (`div_of_reach`). An infinite productive chain of `G` never reaches one (`no_reach_div`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniform

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A A' B : Type u}
  {h : FullFun E S A' A} {F : FullFun E S A (B ⊕ A)} {G : FullFun E S A' (B ⊕ A')}
  (hh : FullFun.SilentDetNoTrap h) (hFG : FullFun.seq h F = FullFun.seq G (caseK h))
include hh hFG

/-- Where `h` diverges, `iter G` diverges silently. -/
theorem div_mem_iter {s : S} {a : A'} (hd : DivAt h s a) : ([], End.div) ∈ AFun.iter G.1 s a := by
  by_contra hn
  let Q : ℕ → S × A' → Prop := fun _ p => DivAt h p.1 p.2 ∧ ([], End.div) ∉ AFun.iter G.1 p.1 p.2
  have step : ∀ n p, Q n p → ∃ p', ([], End.ret (.inr p'.2) p'.1) ∈ G.1 p.1 p.2 ∧ Q (n + 1) p' := by
    rintro n ⟨s₀, a₀⟩ ⟨hd₀, hn₀⟩
    have hm : ([], End.div) ∈ (FullFun.seq G (caseK h)).1 s₀ a₀ :=
      (mem_hyp hFG s₀ a₀ _).1 ((mem_seq_div hd₀ _).2 rfl)
    rcases (mem_seqK hh).1 hm with ⟨_, -, he⟩ | ⟨c, hc, he⟩ | ⟨_, _, _, -, he⟩ |
        ⟨c, a₁, s₁, hc, hd₁, he⟩ | ⟨_, _, _, _, _, -, -, he⟩ <;> cases he
    · exact absurd (AFun.IterBeh.div hc) hn₀
    · refine ⟨(s₁, a₁), hc, hd₁, fun hm₁ => hn₀ ?_⟩
      exact AFun.IterBeh.step (c₂ := []) hc hm₁
  obtain ⟨σ, hσ0, hσ⟩ := exists_chain Q _ step (p₀ := (s, a)) ⟨hd, hn⟩
  exact hn (AFun.IterBeh.spin σ hσ0 fun n => (hσ n).2)

/-- A finite continuing chain of `F` from `h (s, a)` lifts to one of `G` from `(s, a)`. -/
theorem contChain_lift {t : S} {x : A} {c : List (Call E)} {t' : S} {x' : A}
    (hc : FullFun.ContChain F.1 t x c t' x') :
    ∀ s a, RetAt h s a x t → ∃ s' a', FullFun.ContChain G.1 s a c s' a' ∧ RetAt h s' a' x' t' := by
  induction hc with
  | refl => exact fun s a hr => ⟨s, a, .refl, hr⟩
  | step hm _ ih =>
    intro s a hr
    obtain ⟨a₁, s₁, hm₁, hr₁⟩ := (cont_iff hh hFG hr).1 hm
    obtain ⟨s', a', hc', hr'⟩ := ih s₁ a₁ hr₁
    exact ⟨s', a', .step hm₁ hc', hr'⟩

/-- An infinite continuing chain of `F` from `h (s, a)` lifts to one of `G` from `(s, a)`, with
the same logs. -/
theorem chain_lift {s : S} {a : A'} {τ : ℕ → S × A} {l : ℕ → List (Call E)}
    (h0 : RetAt h s a (τ 0).2 (τ 0).1)
    (hτ : ∀ n, (l n, End.ret (.inr (τ (n + 1)).2) (τ (n + 1)).1) ∈ F.1 (τ n).1 (τ n).2) :
    ∃ σ : ℕ → S × A', σ 0 = (s, a) ∧
      ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ G.1 (σ n).1 (σ n).2 := by
  obtain ⟨σ, hσ0, hσ⟩ := exists_chain (fun n p => RetAt h p.1 p.2 (τ n).2 (τ n).1)
    (fun n p p' => (l n, End.ret (.inr p'.2) p'.1) ∈ G.1 p.1 p.2)
    (fun n p hp => by
      obtain ⟨a₁, s₁, hm₁, hr₁⟩ := (cont_iff hh hFG hp).1 (hτ n)
      exact ⟨(s₁, a₁), hm₁, hr₁⟩) (p₀ := (s, a)) h0
  exact ⟨σ, hσ0, fun n => (hσ n).2⟩

/-- A finite behaviour of `iter F` from `h (s, a)` is one of `iter G` from `(s, a)`. -/
theorem iterBeh_lift {t : S} {x : A} {y : CallBeh E S B} (hy : AFun.IterBeh F.1 t x y) :
    ∀ s a, RetAt h s a x t → AFun.IterBeh G.1 s a y := by
  induction hy with
  | exit hm => exact fun s a hr => .exit ((exit_iff hh hFG hr).1 hm)
  | trap hm => exact fun s a hr => .trap ((trap_iff hh hFG hr).1 hm)
  | @div t x c hm =>
    intro s a hr
    rcases (div_iff hh hFG hr).1 hm with hm' | ⟨a₁, s₁, hm₁, hd₁⟩
    · exact .div hm'
    · have := AFun.IterBeh.step hm₁ (div_mem_iter hh hFG hd₁)
      rwa [List.append_nil] at this
  | step hm _ ih =>
    intro s a hr
    obtain ⟨a₁, s₁, hm₁, hr₁⟩ := (cont_iff hh hFG hr).1 hm
    exact .step hm₁ (ih s₁ a₁ hr₁)
  | spin τ h0 hτ =>
    intro s a hr
    obtain ⟨σ, hσ0, hσ⟩ := chain_lift hh hFG (l := fun _ => []) (by rw [h0]; exact hr) hτ
    exact .spin σ hσ0 hσ

/-- A finite continuing chain of `G` ending where `h` returns maps to one of `F`. -/
theorem contChain_map {s : S} {a : A'} {c : List (Call E)} {s' : S} {a' : A'}
    (hc : FullFun.ContChain G.1 s a c s' a') :
    ∀ x' t', RetAt h s' a' x' t' → ∃ x t, RetAt h s a x t ∧ FullFun.ContChain F.1 t x c t' x' := by
  induction hc with
  | refl => exact fun x' t' hr => ⟨x', t', hr, .refl⟩
  | @step s a c₁ s₁ a₁ c₂ s'' a'' hm _ ih =>
    intro x' t' hr'
    obtain ⟨x₁, t₁, hr₁, hc₁⟩ := ih x' t' hr'
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rcases of_div hh hFG hd hm with he | ⟨_, _, he, hd₁⟩
      · cases (Prod.mk.inj he).2
      · obtain ⟨-, he⟩ := Prod.mk.inj he
        cases he
        exact (not_ret_div hr₁ hd₁).elim
    · exact ⟨x, t, hr, .step ((cont_iff hh hFG hr).2 ⟨a₁, s₁, hm, hr₁⟩) hc₁⟩

/-- Along a silent chain of `G` from a point where `h` returns, reaching a point where `h`
diverges gives a silent divergence of `iter F`. -/
theorem div_of_reach {σ : ℕ → S × A'}
    (hσ : ∀ n, ([], End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ G.1 (σ n).1 (σ n).2) :
    ∀ d n x t, RetAt h (σ n).1 (σ n).2 x t → DivAt h (σ (n + d)).1 (σ (n + d)).2 →
      ([], End.div) ∈ AFun.iter F.1 t x := by
  intro d
  induction d with
  | zero => exact fun n x t hr hd => (not_ret_div hr hd).elim
  | succ d ih =>
    intro n x t hr hd
    rcases shape hh (σ (n + 1)).1 (σ (n + 1)).2 with hd₁ | ⟨x₁, t₁, hr₁⟩
    · exact .div ((div_iff hh hFG hr).2 (.inr ⟨_, _, hσ n, hd₁⟩))
    · have hm := (cont_iff hh hFG hr).2 ⟨_, _, hσ n, hr₁⟩
      exact AFun.IterBeh.step (c₂ := []) hm
        (ih (n + 1) x₁ t₁ hr₁ (by rw [Nat.add_right_comm]; exact hd))

/-- A finite behaviour of `iter G` is one of `h ; iter F`. -/
theorem iterBeh_map {s : S} {a : A'} {y : CallBeh E S B} (hy : AFun.IterBeh G.1 s a y) :
    y ∈ (FullFun.seq h (FullFun.iter F)).1 s a := by
  induction hy with
  | @exit s a c b s' hm =>
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rcases of_div hh hFG hd hm with he | ⟨_, _, he, -⟩ <;> cases (Prod.mk.inj he).2
    · exact (mem_seq_ret hr _).2 (.exit ((exit_iff hh hFG hr).2 hm))
  | @trap s a c hm =>
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rcases of_div hh hFG hd hm with he | ⟨_, _, he, -⟩ <;> cases (Prod.mk.inj he).2
    · exact (mem_seq_ret hr _).2 (.trap ((trap_iff hh hFG hr).2 hm))
  | @div s a c hm =>
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rcases of_div hh hFG hd hm with he | ⟨_, _, he, -⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj he
        exact (mem_seq_div hd _).2 rfl
      · cases (Prod.mk.inj he).2
    · exact (mem_seq_ret hr _).2 (.div ((div_iff hh hFG hr).2 (.inl hm)))
  | @step s a c₁ a₁ s₁ c₂ e hm _ ih =>
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rcases of_div hh hFG hd hm with he | ⟨_, _, he, hd₁⟩
      · cases (Prod.mk.inj he).2
      · obtain ⟨rfl, he⟩ := Prod.mk.inj he
        cases he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((mem_seq_div hd₁ _).1 ih)
        exact (mem_seq_div hd _).2 rfl
    · refine (mem_seq_ret hr _).2 ?_
      rcases shape hh s₁ a₁ with hd₁ | ⟨x₁, t₁, hr₁⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((mem_seq_div hd₁ _).1 ih)
        rw [List.append_nil]
        exact .div ((div_iff hh hFG hr).2 (.inr ⟨a₁, s₁, hm, hd₁⟩))
      · exact AFun.IterBeh.step ((cont_iff hh hFG hr).2 ⟨a₁, s₁, hm, hr₁⟩)
          ((mem_seq_ret hr₁ _).1 ih)
  | @spin s a σ h0 hσ =>
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · exact (mem_seq_div hd _).2 rfl
    · refine (mem_seq_ret hr _).2 ?_
      by_cases hreach : ∃ d, DivAt h (σ d).1 (σ d).2
      · obtain ⟨d, hd⟩ := hreach
        exact div_of_reach hh hFG hσ d 0 x t (by rw [h0]; exact hr) (by rw [Nat.zero_add]; exact hd)
      · have hret : ∀ n, ∃ q : A × S, RetAt h (σ n).1 (σ n).2 q.1 q.2 := fun n => by
          rcases shape hh (σ n).1 (σ n).2 with hd | ⟨x', t', hr'⟩
          · exact (hreach ⟨n, hd⟩).elim
          · exact ⟨(x', t'), hr'⟩
        choose q hq using hret
        have hq0 : q 0 = (x, t) := by
          have hr0 : RetAt h (σ 0).1 (σ 0).2 x t := by rw [h0]; exact hr
          obtain ⟨h1, h2⟩ := retAt_unique (hq 0) hr0
          exact Prod.ext h1 h2
        refine .spin (fun n => ((q n).2, (q n).1)) (by rw [hq0]) fun n => ?_
        exact (cont_iff hh hFG (hq n)).2 ⟨_, _, hσ n, hq (n + 1)⟩

/-- **Uniformity of iteration**, finite behaviours. -/
theorem iter_fin_eq (s : S) (a : A') :
    (FullFun.seq h (FullFun.iter F)).1 s a = AFun.iter G.1 s a := by
  ext y
  constructor
  · intro hy
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rw [(mem_seq_div hd y).1 hy]; exact div_mem_iter hh hFG hd
    · exact iterBeh_lift hh hFG ((mem_seq_ret hr y).1 hy) s a hr
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

/-- An infinite productive chain of `G` never reaches a point where `h` diverges. -/
theorem no_reach_div {σ : ℕ → S × A'} {l : ℕ → List (Call E)} {ω : ℕ → Call E}
    (hσ : ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ G.1 (σ n).1 (σ n).2)
    (hl : Shape.StreamConcat l ω) (m : ℕ) : ¬ DivAt h (σ m).1 (σ m).2 := by
  intro hd
  have hall : ∀ k, DivAt h (σ (m + k)).1 (σ (m + k)).2 ∧ l (m + k) = [] := by
    intro k
    induction k with
    | zero =>
      refine ⟨hd, ?_⟩
      rcases of_div hh hFG hd (hσ m) with he | ⟨_, _, he, -⟩
      · cases (Prod.mk.inj he).2
      · exact (Prod.mk.inj he).1
    | succ k ih =>
      have hd₁ : DivAt h (σ (m + k + 1)).1 (σ (m + k + 1)).2 := by
        rcases of_div hh hFG ih.1 (hσ (m + k)) with he | ⟨_, _, he, hd₁⟩
        · cases (Prod.mk.inj he).2
        · obtain ⟨-, he⟩ := Prod.mk.inj he
          cases he
          exact hd₁
      refine ⟨hd₁, ?_⟩
      rcases of_div hh hFG hd₁ (hσ (m + k + 1)) with he | ⟨_, _, he, -⟩
      · cases (Prod.mk.inj he).2
      · exact (Prod.mk.inj he).1
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
    rcases shape hh s a with hd | ⟨x, t, hr⟩
    · rw [seq_inf_div hh hd] at hω; exact hω.elim
    · rw [seq_inf_ret hh hr] at hω
      rcases hω with ⟨c, t', x', ω', hc, hω', rfl⟩ | ⟨τ, l, h0, hτ, hl⟩
      · obtain ⟨s', a', hc', hr'⟩ := contChain_lift hh hFG hc s a hr
        exact .inl ⟨c, s', a', ω', hc', (inf_eq hh hFG hr') ▸ hω', rfl⟩
      · obtain ⟨σ, hσ0, hσ⟩ := chain_lift hh hFG (by rw [h0]; exact hr) hτ
        exact .inr ⟨σ, l, hσ0, hσ, hl⟩
  · rintro (⟨c, s', a', ω', hc, hω', rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · rcases shape hh s' a' with hd' | ⟨x', t', hr'⟩
      · rw [inf_div hh hFG hd'] at hω'; exact hω'.elim
      · obtain ⟨x, t, hr, hc'⟩ := contChain_map hh hFG hc x' t' hr'
        rw [seq_inf_ret hh hr]
        exact .inl ⟨c, t', x', ω', hc', (inf_eq hh hFG hr').symm ▸ hω', rfl⟩
    · have hret : ∀ n, ∃ q : A × S, RetAt h (σ n).1 (σ n).2 q.1 q.2 := fun n => by
        rcases shape hh (σ n).1 (σ n).2 with hd | ⟨x', t', hr'⟩
        · exact (no_reach_div hh hFG hσ hl n hd).elim
        · exact ⟨(x', t'), hr'⟩
      choose q hq using hret
      have hr0 : RetAt h s a (q 0).1 (q 0).2 := by have := hq 0; rw [h0] at this; exact this
      rw [seq_inf_ret hh hr0]
      exact .inr ⟨fun n => ((q n).2, (q n).1), l, rfl,
        fun n => (cont_iff hh hFG (hq n)).2 ⟨_, _, hσ n, hq (n + 1)⟩, hl⟩

/-- **Uniformity of iteration** along a silent, deterministic, trap-free, defined map. -/
theorem iter_uniform :
    FullFun.seq h (FullFun.iter F) = FullFun.iter G :=
  Prod.ext (funext fun s => funext fun a => iter_fin_eq hh hFG s a)
    (funext fun s => funext fun a => iter_inf_eq hh hFG s a)

end Silmaril.Proofs.Games.Abstract.IterUniform
