module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Proofs.Games.Abstract.FullFun.Regroup
import Silmaril.Proofs.Games.Abstract.FullFun.Tensor
import Silmaril.Proofs.Games.Abstract.FullFun.Unfold
import Silmaril.Proofs.Games.Abstract.FullFun.Dinat
import Silmaril.Proofs.Games.Abstract.ModuleInf.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push

/-!
# The codiagonal law of iteration (proofs)

For `F : A → (B ⊕ A) ⊕ A`, **the codiagonal law**:

  `iter (iter F) = iter (F.map [id, inr])`.

The inner loop continues on the outer `inr`; its `inl (inr a')` exit continues the outer loop.
Merging the two continue tags gives one loop. A run of the merged loop is a sequence of *inner*
steps (`F` returns `inr`) and *outer* steps (`F` returns `inl (inr _)`); the runs of the nested
loop group it into blocks, each ending with an outer step.

* **Flattening** (`chain_flatten`): an infinite chain of outer iterations, each a finite nonempty
  chain of merged steps, is one infinite merged chain. Each block is read as a finite sequence
  (`FnChain`, `fnChain_of_chain`) and the blocks are laid end to end; the logs are regrouped
  (`streamConcat_regroup`), and silent blocks give silent steps.
* **Grouping**: a merged chain with infinitely many outer steps groups into an infinite chain of
  outer iterations (`group_inf`), cut after each outer step; with finitely many, a finite chain
  of outer iterations is followed by an infinite chain of inner steps (`prefix_group`).

No hypothesis on `F`: traps, `div` ends, infinite silent chains and productive runs all
correspond.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B B' : Type u}

/-! ## Continuing chains -/

section Chain

variable {g : AFun E S A (B ⊕ A)}

theorem contChain_single {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (h : (c, End.ret (.inr a') s') ∈ g s a) : FullFun.ContChain g s a c s' a' := by
  simpa using FullFun.ContChain.step h .refl

theorem contChain_append {s : S} {a : A} {c₁ : List (Call E)} {s₁ : S} {a₁ : A}
    {c₂ : List (Call E)} {s₂ : S} {a₂ : A} (h₁ : FullFun.ContChain g s a c₁ s₁ a₁)
    (h₂ : FullFun.ContChain g s₁ a₁ c₂ s₂ a₂) : FullFun.ContChain g s a (c₁ ++ c₂) s₂ a₂ := by
  induction h₁ with
  | refl => exact h₂
  | step hm _ ih => rw [List.append_assoc]; exact .step hm (ih h₂)

/-- A chain whose steps are chains of another body. -/
theorem contChain_bind {g' : AFun E S A (B' ⊕ A)}
    (hs : ∀ {s a c s' a'}, (c, End.ret (.inr a') s') ∈ g s a → FullFun.ContChain g' s a c s' a')
    {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (h : FullFun.ContChain g s a c s' a') : FullFun.ContChain g' s a c s' a' := by
  induction h with
  | refl => exact .refl
  | step hm _ ih => exact contChain_append (hs hm) ih

/-- A chain in front of an iterated behaviour. -/
theorem iterBeh_of_chain {s : S} {a : A} {c₁ : List (Call E)} {s₁ : S} {a₁ : A}
    (h : FullFun.ContChain g s a c₁ s₁ a₁) {y : CallBeh E S B} (hy : AFun.IterBeh g s₁ a₁ y) :
    AFun.IterBeh g s a (c₁ ++ y.1, y.2) := by
  induction h with
  | refl => exact hy
  | step hm _ ih => rw [List.append_assoc]; exact .step hm (ih hy)

/-- An iterated return is a chain followed by an exiting iteration. -/
theorem iterBeh_ret_inv {s : S} {a : A} {y : CallBeh E S B} (hy : AFun.IterBeh g s a y) :
    ∀ {c b s'}, y = (c, End.ret b s') → ∃ c₁ s₁ a₁ c₂, FullFun.ContChain g s a c₁ s₁ a₁ ∧
      (c₂, End.ret (.inl b) s') ∈ g s₁ a₁ ∧ c = c₁ ++ c₂ := by
  induction hy with
  | exit hm =>
    intro c b s' h
    obtain ⟨rfl, h'⟩ := Prod.mk.inj h
    cases h'
    exact ⟨[], _, _, _, .refl, hm, rfl⟩
  | trap => intro c b s' h; cases h
  | div => intro c b s' h; cases h
  | step hm _ ih =>
    intro c b s' h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨c₃, s₃, a₃, c₄, hc, hx, rfl⟩ := ih rfl
    exact ⟨_ ++ c₃, s₃, a₃, c₄, .step hm hc, hx, by simp⟩
  | spin => intro c b s' h; cases h

/-- A chain followed by one more step is a first step followed by a chain. -/
theorem plus_of_chain_snoc {s : S} {a : A} {c₁ : List (Call E)} {s₁ : S} {a₁ : A}
    (h : FullFun.ContChain g s a c₁ s₁ a₁) {c₂ : List (Call E)} {a' : A} {s' : S}
    (hm : (c₂, End.ret (.inr a') s') ∈ g s₁ a₁) :
    ∃ c₃ s₃ a₃ c₄, (c₃, End.ret (.inr a₃) s₃) ∈ g s a ∧ FullFun.ContChain g s₃ a₃ c₄ s' a' ∧
      c₁ ++ c₂ = c₃ ++ c₄ := by
  cases h with
  | refl => exact ⟨c₂, s', a', [], hm, .refl, by simp⟩
  | step hm' hc => exact ⟨_, _, _, _, hm', contChain_append hc (contChain_single hm), by simp⟩

/-- The steps `k, …, k + m - 1` of an infinite chain form a finite chain. -/
theorem contChain_segment {σ : Nat → S × A} {l : Nat → List (Call E)} : ∀ (m k : Nat),
    (∀ j < m, (l (k + j), End.ret (.inr (σ (k + j + 1)).2) (σ (k + j + 1)).1) ∈
      g (σ (k + j)).1 (σ (k + j)).2) →
    FullFun.ContChain g (σ k).1 (σ k).2 ((List.range m).flatMap fun j => l (k + j))
      (σ (k + m)).1 (σ (k + m)).2
  | 0, _, _ => .refl
  | m + 1, k, h => by
    rw [flatMap_range_succ]
    have ih := contChain_segment m (k + 1) fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    have e : (fun i => l (k + (i + 1))) = fun j => l (k + 1 + j) :=
      funext fun i => by rw [show k + (i + 1) = k + 1 + i by omega]
    rw [e, show k + (m + 1) = k + 1 + m by omega]
    exact .step (h 0 (Nat.succ_pos m)) ih

/-- Prepend an element to a sequence. -/
def ncons {α : Type u} (x : α) (f : Nat → α) : Nat → α := fun j =>
  match j with
  | 0 => x
  | j + 1 => f j

/-- **A chain of `k` steps as a sequence**: states `p 0 = x, …, p k = y` and logs `lab j`. -/
def FnChain (g : AFun E S A (B ⊕ A)) (x : S × A) (k : Nat) (p : Nat → S × A)
    (lab : Nat → List (Call E)) (y : S × A) : Prop :=
  p 0 = x ∧ p k = y ∧
    ∀ j < k, (lab j, End.ret (.inr (p (j + 1)).2) (p (j + 1)).1) ∈ g (p j).1 (p j).2

theorem fnChain_cons {x x' y : S × A} {c : List (Call E)}
    (hm : (c, End.ret (.inr x'.2) x'.1) ∈ g x.1 x.2) {k : Nat} {p : Nat → S × A}
    {lab : Nat → List (Call E)} (h : FnChain g x' k p lab y) :
    FnChain g x (k + 1) (ncons x p) (ncons c lab) y :=
  ⟨rfl, h.2.1, fun j hj => by
    cases j with
    | zero =>
      show (c, End.ret (.inr (p 0).2) (p 0).1) ∈ g x.1 x.2
      rw [h.1]
      exact hm
    | succ j => exact h.2.2 j (by omega)⟩

theorem flatMap_ncons {α : Type u} (c : List α) (lab : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap (ncons c lab) = c ++ (List.range k).flatMap lab :=
  flatMap_range_succ _ _

theorem fnChain_of_chain {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (h : FullFun.ContChain g s a c s' a') :
    ∃ k p lab, FnChain g (s, a) k p lab (s', a') ∧ c = (List.range k).flatMap lab := by
  induction h with
  | refl =>
    exact ⟨0, fun _ => (_, _), fun _ => [], ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      rfl⟩
  | step hm _ ih =>
    obtain ⟨k, p, lab, hp, rfl⟩ := ih
    exact ⟨k + 1, _, _, fnChain_cons (x' := (_, _)) hm hp, (flatMap_ncons _ _ _).symm⟩

/-- **Flattening**: an infinite sequence of finite nonempty chains, laid end to end, is one
infinite chain. Concatenations of the logs carry over, and silent blocks give silent steps. -/
theorem chain_flatten {τ : Nat → S × A} {L : Nat → List (Call E)}
    (h : ∀ n, ∃ c₁ s₁ a₁ c₂, (c₁, End.ret (.inr a₁) s₁) ∈ g (τ n).1 (τ n).2 ∧
      FullFun.ContChain g s₁ a₁ c₂ (τ (n + 1)).1 (τ (n + 1)).2 ∧ L n = c₁ ++ c₂) :
    ∃ (σ : Nat → S × A) (l : Nat → List (Call E)), σ 0 = τ 0 ∧
      (∀ i, (l i, End.ret (.inr (σ (i + 1)).2) (σ (i + 1)).1) ∈ g (σ i).1 (σ i).2) ∧
      (∀ ω, Shape.StreamConcat L ω → Shape.StreamConcat l ω) ∧
      ((∀ n, L n = []) → ∀ i, l i = []) := by
  classical
  have h' : ∀ n, ∃ k p lab, 0 < k ∧ FnChain g (τ n) k p lab (τ (n + 1)) ∧
      L n = (List.range k).flatMap lab := by
    intro n
    obtain ⟨c₁, s₁, a₁, c₂, hm, hc, hL⟩ := h n
    obtain ⟨k, p, lab, hp, rfl⟩ := fnChain_of_chain hc
    exact ⟨k + 1, _, _, Nat.succ_pos k, fnChain_cons (x' := (s₁, a₁)) hm hp,
      by rw [hL, flatMap_ncons]⟩
  choose k p lab hk hp hL using h'
  obtain ⟨K, hK0, hKs⟩ : ∃ K : Nat → Nat, K 0 = 0 ∧ ∀ n, K (n + 1) = K n + k n :=
    ⟨fun n => ((List.range n).map k).sum, rfl, fun n => by simp [List.range_succ]⟩
  have hKm : StrictMono K := strictMono_nat_of_lt_succ fun n => by
    rw [hKs]; have := hk n; omega
  have hex : ∀ i, ∃ n, i < K (n + 1) := fun i =>
    ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (hKm.id_le (i + 1))⟩
  obtain ⟨seg, hseg1, hseg0⟩ : ∃ seg : Nat → Nat, (∀ i, i < K (seg i + 1)) ∧
      ∀ i, K (seg i) ≤ i := by
    refine ⟨fun i => Nat.find (hex i), fun i => Nat.find_spec (hex i), fun i => ?_⟩
    show K (Nat.find (hex i)) ≤ i
    rcases hs : Nat.find (hex i) with _ | m
    · rw [hK0]; exact Nat.zero_le _
    · exact Nat.le_of_not_lt (Nat.find_min (hex i) (show m < Nat.find (hex i) by omega))
  have hseg : ∀ i n, K n ≤ i → i < K (n + 1) → seg i = n := fun i n h1 h2 => by
    have a1 := hseg0 i
    have a2 := hseg1 i
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hKm.monotone (show seg i + 1 ≤ n by omega); omega
    · have := hKm.monotone (show n + 1 ≤ seg i by omega); omega
  have hsegK : ∀ n j, j < k n → seg (K n + j) = n := fun n j hj =>
    hseg (K n + j) n (Nat.le_add_right _ _) (by rw [hKs]; omega)
  refine ⟨fun i => p (seg i) (i - K (seg i)), fun i => lab (seg i) (i - K (seg i)), ?_, ?_, ?_, ?_⟩
  · have h0 : seg 0 = 0 := by have := hsegK 0 0 (hk 0); rwa [hK0] at this
    show p (seg 0) (0 - K (seg 0)) = τ 0
    rw [h0, hK0]
    exact (hp 0).1
  · intro i
    have h1 := hseg0 i
    have h2 := hseg1 i
    have h3 := hKs (seg i)
    have hj : i - K (seg i) < k (seg i) := by omega
    have hstep := (hp (seg i)).2.2 _ hj
    have he : p (seg (i + 1)) (i + 1 - K (seg (i + 1))) = p (seg i) (i - K (seg i) + 1) := by
      by_cases hlast : i + 1 < K (seg i + 1)
      · rw [hseg (i + 1) (seg i) (by omega) hlast]
        congr 1
        omega
      · have hK1 : K (seg i + 1) = i + 1 := by omega
        have := hk (seg i + 1)
        have h4 := hKs (seg i + 1)
        rw [hseg (i + 1) (seg i + 1) (by omega) (by omega), hK1, Nat.sub_self,
          (hp (seg i + 1)).1, ← (hp (seg i)).2.1]
        congr 1
        omega
    show (lab (seg i) (i - K (seg i)), End.ret (.inr (p (seg (i + 1)) (i + 1 - K (seg (i + 1)))).2)
      (p (seg (i + 1)) (i + 1 - K (seg (i + 1)))).1) ∈
        g (p (seg i) (i - K (seg i))).1 (p (seg i) (i - K (seg i))).2
    rw [he]
    exact hstep
  · intro ω hω
    have hgrp : L = regroup (fun i => lab (seg i) (i - K (seg i))) K := funext fun n => by
      rw [hL n, regroup, hKs, Nat.add_sub_cancel_left, List.flatMap_def, List.flatMap_def]
      congr 1
      refine List.map_congr_left fun j hj => ?_
      have hj' := List.mem_range.1 hj
      simp only [hsegK n j hj', Nat.add_sub_cancel_left]
    rw [hgrp] at hω
    exact (streamConcat_regroup hK0 hKm ω).1 hω
  · intro hnil i
    have := hL (seg i)
    rw [hnil, eq_comm, List.flatMap_eq_nil_iff] at this
    have h1 := hseg0 i
    have h2 := hseg1 i
    have h3 := hKs (seg i)
    exact this _ (List.mem_range.2 (by omega))

/-- Prepending a finite chain to a productive run of the iteration. -/
theorem iter_inf_chain (F : FullFun E S A (B ⊕ A)) {s : S} {a : A} {c : List (Call E)}
    {s' : S} {a' : A} (h : FullFun.ContChain F.1 s a c s' a') {ω : Nat → Call E}
    (hω : ω ∈ (FullFun.iter F).2 s' a') : c ++ₛ ω ∈ (FullFun.iter F).2 s a := by
  induction h with
  | refl => exact hω
  | step hm _ ih => rw [append_appendStream]; exact iter_inf_cons F hm (ih hω)

end Chain

/-! ## The codiagonal -/

section Codiag

variable {F : FullFun E S A ((B ⊕ A) ⊕ A)}

/-- The merged body `F ; [id, inr]`. -/
abbrev codiagBody (F : FullFun E S A ((B ⊕ A) ⊕ A)) : FullFun E S A (B ⊕ A) :=
  F.map (Sum.elim id Sum.inr)

theorem codiag_cont {s : S} {a : A} {c : List (Call E)} {a' : A} {s' : S} :
    (c, End.ret (.inr a') s') ∈ (codiagBody F).1 s a ↔
      (c, End.ret (.inl (.inr a')) s') ∈ F.1 s a ∨ (c, End.ret (.inr a') s') ∈ F.1 s a := by
  rw [codiagBody, mem_map_ret]
  constructor
  · rintro ⟨(b | x) | x, hb, he⟩
    · cases he
    · cases he; exact .inl hb
    · cases he; exact .inr hb
  · rintro (h | h)
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩

theorem codiag_exit {s : S} {a : A} {c : List (Call E)} {b : B} {s' : S} :
    (c, End.ret (.inl b) s') ∈ (codiagBody F).1 s a ↔
      (c, End.ret (.inl (.inl b)) s') ∈ F.1 s a := by
  rw [codiagBody, mem_map_ret]
  constructor
  · rintro ⟨(b' | x) | x, hb, he⟩
    · cases he; exact hb
    · cases he
    · cases he
  · exact fun h => ⟨_, h, rfl⟩

/-- An inner continuing chain is a merged chain. -/
theorem codiag_inner_chain {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (h : FullFun.ContChain F.1 s a c s' a') : FullFun.ContChain (codiagBody F).1 s a c s' a' :=
  contChain_bind (fun hm => contChain_single (codiag_cont.2 (.inr hm))) h

/-- An outer continuing iteration is a nonempty merged chain. -/
theorem codiag_outer_plus {s : S} {a : A} {c : List (Call E)} {a' : A} {s' : S}
    (hm : (c, End.ret (.inr a') s') ∈ AFun.iter F.1 s a) :
    ∃ c₁ s₁ a₁ c₂, (c₁, End.ret (.inr a₁) s₁) ∈ (codiagBody F).1 s a ∧
      FullFun.ContChain (codiagBody F).1 s₁ a₁ c₂ s' a' ∧ c = c₁ ++ c₂ := by
  obtain ⟨c₁, s₁, a₁, c₂, hc, hx, rfl⟩ := iterBeh_ret_inv hm rfl
  exact plus_of_chain_snoc (codiag_inner_chain hc) (codiag_cont.2 (.inl hx))

theorem codiag_outer_step {s : S} {a : A} {c : List (Call E)} {a' : A} {s' : S}
    (hm : (c, End.ret (.inr a') s') ∈ AFun.iter F.1 s a) :
    FullFun.ContChain (codiagBody F).1 s a c s' a' := by
  obtain ⟨c₁, s₁, a₁, c₂, hm', hc, rfl⟩ := codiag_outer_plus hm
  exact .step hm' hc

/-- An outer continuing chain is a merged chain. -/
theorem codiag_outer_chain {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (h : FullFun.ContChain (AFun.iter F.1) s a c s' a') :
    FullFun.ContChain (codiagBody F).1 s a c s' a' :=
  contChain_bind codiag_outer_step h

/-- A trap or divergence of the inner loop is one of the merged loop. -/
theorem codiag_inner_abort {s : S} {a : A} {y : CallBeh E S (B ⊕ A)}
    (hy : AFun.IterBeh F.1 s a y) :
    (y.2 = .trap → AFun.IterBeh (codiagBody F).1 s a (y.1, .trap)) ∧
      (y.2 = .div → AFun.IterBeh (codiagBody F).1 s a (y.1, .div)) := by
  induction hy with
  | exit => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | trap hm => exact ⟨fun _ => .trap ((mem_map_trap F _ _ _ _).2 hm), fun h => (by cases h)⟩
  | div hm => exact ⟨fun h => (by cases h), fun _ => .div ((mem_map_div F _ _ _ _).2 hm)⟩
  | step hm _ ih =>
    exact ⟨fun h => .step (codiag_cont.2 (.inr hm)) (ih.1 h),
      fun h => .step (codiag_cont.2 (.inr hm)) (ih.2 h)⟩
  | spin σ h0 hσ =>
    exact ⟨fun h => (by cases h), fun _ => .spin σ h0 fun n => codiag_cont.2 (.inr (hσ n))⟩

/-- **The codiagonal**, left to right, finite behaviours. -/
theorem codiag_fin_lr {s : S} {a : A} {y : CallBeh E S B}
    (hy : AFun.IterBeh (AFun.iter F.1) s a y) : AFun.IterBeh (codiagBody F).1 s a y := by
  induction hy with
  | exit hm =>
    obtain ⟨c₁, s₁, a₁, c₂, hc, hx, rfl⟩ := iterBeh_ret_inv hm rfl
    exact iterBeh_of_chain (codiag_inner_chain hc) (.exit (codiag_exit.2 hx))
  | trap hm => exact (codiag_inner_abort hm).1 rfl
  | div hm => exact (codiag_inner_abort hm).2 rfl
  | step hm _ ih => exact iterBeh_of_chain (codiag_outer_step hm) ih
  | spin σ h0 hσ =>
    obtain ⟨σ', l, h0', hσ', -, hl⟩ := chain_flatten (g := (codiagBody F).1) (τ := σ)
      (L := fun _ => []) fun n => codiag_outer_plus (hσ n)
    refine .spin σ' (h0'.trans h0) fun i => ?_
    have := hσ' i
    rwa [hl (fun _ => rfl) i] at this

/-- An inner continuing step in front of an outer iterated behaviour. -/
theorem codiag_outer_cons_inner {s : S} {a : A} {c₁ : List (Call E)} {a₀ : A} {s₀ : S}
    (hI : (c₁, End.ret (.inr a₀) s₀) ∈ F.1 s a) {y : CallBeh E S B}
    (hy : AFun.IterBeh (AFun.iter F.1) s₀ a₀ y) :
    AFun.IterBeh (AFun.iter F.1) s a (c₁ ++ y.1, y.2) := by
  cases hy with
  | exit hm => exact .exit (AFun.IterBeh.step hI hm)
  | trap hm => exact .trap (AFun.IterBeh.step hI hm)
  | div hm => exact .div (AFun.IterBeh.step hI hm)
  | step hm hr =>
    rw [← List.append_assoc]
    exact .step (AFun.IterBeh.step hI hm) hr
  | spin τ h0 hτ =>
    have h1 := hτ 0
    rw [h0] at h1
    have := AFun.IterBeh.step (f := AFun.iter F.1) (AFun.IterBeh.step hI h1)
      (.spin (fun n => τ (n + 1)) rfl fun n => hτ (n + 1))
    simpa using this

/-- An outer step of a merged chain. -/
def OStep (F : FullFun E S A ((B ⊕ A) ⊕ A)) (σ : Nat → S × A) (l : Nat → List (Call E))
    (i : Nat) : Prop :=
  (l i, End.ret (.inl (.inr (σ (i + 1)).2)) (σ (i + 1)).1) ∈ F.1 (σ i).1 (σ i).2

/-- An inner step of a merged chain. -/
def IStep (F : FullFun E S A ((B ⊕ A) ⊕ A)) (σ : Nat → S × A) (l : Nat → List (Call E))
    (i : Nat) : Prop :=
  (l i, End.ret (.inr (σ (i + 1)).2) (σ (i + 1)).1) ∈ F.1 (σ i).1 (σ i).2

/-- **Grouping a finite prefix**: the first `K` steps of a merged chain are a chain of outer
iterations up to some `M ≤ K`, followed by inner steps. -/
theorem prefix_group (σ : Nat → S × A) (l : Nat → List (Call E))
    (hσ : ∀ i, OStep F σ l i ∨ IStep F σ l i) : ∀ K, ∃ M ≤ K,
      FullFun.ContChain (AFun.iter F.1) (σ 0).1 (σ 0).2 ((List.range M).flatMap l)
        (σ M).1 (σ M).2 ∧ ∀ j, M ≤ j → j < K → IStep F σ l j
  | 0 => ⟨0, le_refl _, .refl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | K + 1 => by
    obtain ⟨M, hMK, hc, hI⟩ := prefix_group σ l hσ K
    rcases hσ K with hO | hIK
    · refine ⟨K + 1, le_refl _, ?_, fun _ h1 h2 => absurd h2 (by omega)⟩
      have hseg := contChain_segment (g := F.1) (σ := σ) (l := l) (K - M) M
        fun j hj => hI (M + j) (by omega) (by omega)
      rw [show M + (K - M) = K by omega] at hseg
      have hout : ((List.range (K - M)).flatMap (fun j => l (M + j)) ++ l K,
          End.ret (.inr (σ (K + 1)).2) (σ (K + 1)).1) ∈ AFun.iter F.1 (σ M).1 (σ M).2 :=
        iterBeh_of_chain hseg (AFun.IterBeh.exit hO)
      have e : (List.range (K + 1)).flatMap l = (List.range M).flatMap l ++
          ((List.range (K - M)).flatMap (fun j => l (M + j)) ++ l K) := by
        rw [ModuleInf.range_flatMap_succ, ← List.append_assoc, ← flatMap_range_add,
          show M + (K - M) = K by omega]
      rw [e]
      exact contChain_append hc (contChain_single hout)
    · refine ⟨M, by omega, hc, fun j h1 h2 => ?_⟩
      by_cases h : j < K
      · exact hI j h1 h
      · obtain rfl : j = K := by omega
        exact hIK

/-- **Grouping**: a merged chain with infinitely many outer steps is an infinite chain of outer
iterations, cut after each outer step. -/
theorem group_inf (σ : Nat → S × A) (l : Nat → List (Call E))
    (hσ : ∀ i, OStep F σ l i ∨ IStep F σ l i) (hinf : ∀ N, ∃ j, N ≤ j ∧ OStep F σ l j) :
    ∃ k : Nat → Nat, k 0 = 0 ∧ StrictMono k ∧ ∀ n,
      (regroup l k n, End.ret (.inr (σ (k (n + 1))).2) (σ (k (n + 1))).1) ∈
        AFun.iter F.1 (σ (k n)).1 (σ (k n)).2 := by
  classical
  obtain ⟨nx, hnx1, hnx2, hnx3⟩ : ∃ nx : Nat → Nat, (∀ m, m ≤ nx m) ∧
      (∀ m, OStep F σ l (nx m)) ∧ ∀ m j, m ≤ j → j < nx m → IStep F σ l j :=
    ⟨fun m => Nat.find (hinf m), fun m => (Nat.find_spec (hinf m)).1,
      fun m => (Nat.find_spec (hinf m)).2, fun m j h1 h2 =>
        (hσ j).resolve_left fun hO => Nat.find_min (hinf m) h2 ⟨h1, hO⟩⟩
  obtain ⟨k, hk0, hks⟩ : ∃ k : Nat → Nat, k 0 = 0 ∧ ∀ n, k (n + 1) = nx (k n) + 1 :=
    ⟨fun n => Nat.rec 0 (fun _ km => nx km + 1) n, rfl, fun _ => rfl⟩
  refine ⟨k, hk0, strictMono_nat_of_lt_succ fun n => by rw [hks]; have := hnx1 (k n); omega,
    fun n => ?_⟩
  have h1 := hnx1 (k n)
  have hseg := contChain_segment (g := F.1) (σ := σ) (l := l) (nx (k n) - k n) (k n)
    fun j hj => hnx3 (k n) (k n + j) (by omega) (by omega)
  rw [show k n + (nx (k n) - k n) = nx (k n) by omega] at hseg
  have := iterBeh_of_chain hseg (AFun.IterBeh.exit (hnx2 (k n)))
  have e : regroup l k n =
      (List.range (nx (k n) - k n)).flatMap (fun j => l (k n + j)) ++ l (nx (k n)) := by
    rw [regroup, hks, show nx (k n) + 1 - k n = (nx (k n) - k n) + 1 by omega,
      ModuleInf.range_flatMap_succ, show k n + (nx (k n) - k n) = nx (k n) by omega]
  rw [e, hks]
  exact this

/-- **The codiagonal**, right to left, finite behaviours. -/
theorem codiag_fin_rl {s : S} {a : A} {y : CallBeh E S B}
    (hy : AFun.IterBeh (codiagBody F).1 s a y) : AFun.IterBeh (AFun.iter F.1) s a y := by
  induction hy with
  | exit hm => exact .exit (AFun.IterBeh.exit (codiag_exit.1 hm))
  | trap hm => exact .trap (AFun.IterBeh.trap ((mem_map_trap F _ _ _ _).1 hm))
  | div hm => exact .div (AFun.IterBeh.div ((mem_map_div F _ _ _ _).1 hm))
  | step hm _ ih =>
    rcases codiag_cont.1 hm with hO | hI
    · exact .step (AFun.IterBeh.exit hO) ih
    · exact codiag_outer_cons_inner hI ih
  | spin σ h0 hσ =>
    have hcls : ∀ i, OStep F σ (fun _ => []) i ∨ IStep F σ (fun _ => []) i :=
      fun i => codiag_cont.1 (hσ i)
    by_cases hinf : ∀ N, ∃ j, N ≤ j ∧ OStep F σ (fun _ => []) j
    · obtain ⟨k, hk0, -, hk⟩ := group_inf σ _ hcls hinf
      refine .spin (fun n => σ (k n)) (by simp only [hk0, h0]) fun n => ?_
      have := hk n
      have e : regroup (fun _ => ([] : List (Call E))) k n = [] := by
        simp [regroup, List.flatMap_eq_nil_iff]
      rwa [e] at this
    · push Not at hinf
      obtain ⟨N, hN⟩ := hinf
      obtain ⟨M, -, hc, hI⟩ := prefix_group σ _ hcls N
      have hIall : ∀ j, M ≤ j → IStep F σ (fun _ => []) j := fun j hj => by
        by_cases h : j < N
        · exact hI j hj h
        · exact (hcls j).resolve_left (hN j (by omega))
      have hdiv : AFun.IterBeh (AFun.iter F.1) (σ M).1 (σ M).2 ([], .div) :=
        .div (AFun.IterBeh.spin (fun n => σ (M + n)) (by simp) fun n => hIall (M + n) (by omega))
      have := iterBeh_of_chain hc hdiv
      have e : (List.range M).flatMap (fun _ => ([] : List (Call E))) = [] := by simp
      rw [e, h0] at this
      exact this

/-- **The codiagonal**, finite behaviours. -/
theorem iter_codiag_fin (F : FullFun E S A ((B ⊕ A) ⊕ A)) :
    AFun.iter (AFun.iter F.1) = AFun.iter (codiagBody F).1 := by
  funext s a
  ext y
  exact ⟨codiag_fin_lr, codiag_fin_rl⟩

/-- A merged chain is a chain of outer iterations followed by a chain of inner steps. -/
theorem codiag_chain_split {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (h : FullFun.ContChain (codiagBody F).1 s a c s' a') :
    ∃ c₁ s₁ a₁ c₂, FullFun.ContChain (AFun.iter F.1) s a c₁ s₁ a₁ ∧
      FullFun.ContChain F.1 s₁ a₁ c₂ s' a' ∧ c = c₁ ++ c₂ := by
  induction h with
  | refl => exact ⟨[], _, _, [], .refl, .refl, rfl⟩
  | step hm _ ih =>
    obtain ⟨c₁, s₁, a₁, c₂, ho, hi, rfl⟩ := ih
    rcases codiag_cont.1 hm with hO | hI
    · exact ⟨_ ++ c₁, s₁, a₁, c₂, .step (AFun.IterBeh.exit hO) ho, hi, by simp⟩
    · cases ho with
      | refl => exact ⟨[], _, _, _ ++ c₂, .refl, .step hI hi, by simp⟩
      | step hO' ho' => exact ⟨_, s₁, a₁, c₂, .step (AFun.IterBeh.step hI hO') ho', hi, by simp⟩

/-- **The codiagonal**, left to right, productive runs. -/
theorem codiag_inf_lr {s : S} {a : A} {ω : Nat → Call E}
    (h : ω ∈ (FullFun.iter (FullFun.iter F)).2 s a) :
    ω ∈ (FullFun.iter (codiagBody F)).2 s a := by
  rcases h with ⟨c, s', a', ω', hc, hω', rfl⟩ | ⟨τ, L, h0, hτ, hL⟩
  · rcases hω' with ⟨c', s'', a'', ω'', hc', hF, rfl⟩ | ⟨σ, l, h0', hσ, hl⟩
    · exact .inl ⟨c ++ c', s'', a'', ω'',
        contChain_append (codiag_outer_chain hc) (codiag_inner_chain hc'), hF,
        (append_appendStream c c' ω'').symm⟩
    · exact iter_inf_chain _ (codiag_outer_chain hc)
        (.inr ⟨σ, l, h0', fun n => codiag_cont.2 (.inr (hσ n)), hl⟩)
  · obtain ⟨σ, l, h0', hσ, hS, -⟩ := chain_flatten (g := (codiagBody F).1) (τ := τ) (L := L)
      fun n => codiag_outer_plus (hτ n)
    exact .inr ⟨σ, l, h0'.trans h0, hσ, hS ω hL⟩

/-- **The codiagonal**, right to left, productive runs. -/
theorem codiag_inf_rl {s : S} {a : A} {ω : Nat → Call E}
    (h : ω ∈ (FullFun.iter (codiagBody F)).2 s a) :
    ω ∈ (FullFun.iter (FullFun.iter F)).2 s a := by
  rcases h with ⟨c, s', a', ω', hc, hω', rfl⟩ | ⟨σ, l, h0, hσ, hl⟩
  · obtain ⟨c₁, s₁, a₁, c₂, ho, hi, rfl⟩ := codiag_chain_split hc
    exact .inl ⟨c₁, s₁, a₁, c₂ ++ₛ ω', ho, .inl ⟨c₂, s', a', ω', hi, hω', rfl⟩,
      append_appendStream c₁ c₂ ω'⟩
  · have hcls : ∀ i, OStep F σ l i ∨ IStep F σ l i := fun i => codiag_cont.1 (hσ i)
    by_cases hinf : ∀ N, ∃ j, N ≤ j ∧ OStep F σ l j
    · obtain ⟨k, hk0, hkm, hk⟩ := group_inf σ l hcls hinf
      exact .inr ⟨fun n => σ (k n), regroup l k, by simp only [hk0, h0], hk,
        (streamConcat_regroup hk0 hkm ω).2 hl⟩
    · push Not at hinf
      obtain ⟨N, hN⟩ := hinf
      obtain ⟨M, -, hc, hI⟩ := prefix_group σ l hcls N
      have hIall : ∀ j, M ≤ j → IStep F σ l j := fun j hj => by
        by_cases h : j < N
        · exact hI j hj h
        · exact (hcls j).resolve_left (hN j (by omega))
      obtain ⟨ω', rfl, hω'⟩ := streamConcat_drop hl M
      have hin : ω' ∈ (FullFun.iter F).2 (σ M).1 (σ M).2 :=
        .inr ⟨fun n => σ (M + n), fun n => l (M + n), by simp,
          fun n => hIall (M + n) (by omega), hω'⟩
      rw [h0] at hc
      exact .inl ⟨_, _, _, ω', hc, hin, rfl⟩

/-- **The codiagonal law**: `iter (iter F) = iter (F.map [id, inr])`. -/
theorem iter_codiag (F : FullFun E S A ((B ⊕ A) ⊕ A)) :
    FullFun.iter (FullFun.iter F) = FullFun.iter (codiagBody F) :=
  Prod.ext (iter_codiag_fin F) (funext fun _ => funext fun _ => Set.ext fun _ =>
    ⟨codiag_inf_lr, codiag_inf_rl⟩)

end Codiag

end Silmaril.Proofs.Games.Abstract.FullFun
