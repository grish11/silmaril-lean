module

public import Silmaril.Games.Abstract.FullFun.Defs
import Silmaril.Proofs.Games.Abstract.FullFun.Tensor
import Silmaril.Proofs.Games.Abstract.FullFun.Unfold
import Silmaril.Proofs.Games.Abstract.FullFun.Regroup

/-!
# Dinaturality of iteration (proofs)

For `f : A → B ⊕ C` and `g : C → B ⊕ A`, write `body f g = f ; [inl, g]`. **Dinaturality**:

  `iter (body f g) = f ; [id, iter (body g f)]`.

Both sides run `f, g, f, g, …` until one of them exits with `inl b`; the right-hand side
groups the runs as `f, (g, f), (g, f), …`. With no hypothesis on `f`, `g`:

* finite behaviours: a trap or divergence of any run ends both loops the same way, and an
  infinite chain of silent continuing iterations of `body f g` is a silent first run of `f`
  followed by a chain of silent iterations of `body g f`, and conversely
  (`AFun.IterBeh.spin`);
* productive runs: a finite chain followed by a productive run of `f` or of `g`, or an infinite
  chain, whose logs `cf 0 ++ cg 0, cf 1 ++ cg 1, …` concatenate to the stream exactly when
  `cg 0 ++ cf 1, cg 1 ++ cf 2, …` concatenate to the stream after `cf 0`
  (`streamConcat_interleave`).

`body_inv`, `body_cont`, `mem_body_inf`, `body_of_g` read the behaviours of `body f g`;
`mem_seq_case_pure` and `mem_seq_case_pure_inf` those of `f ; [id, h]`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B C X : Type u}

/-- The loop body `f ; [inl, g]`: run `f`, exit on `inl`, run `g` on `inr`. -/
def body (f : FullFun E S A (B ⊕ C)) (g : FullFun E S C (B ⊕ X)) : FullFun E S A (B ⊕ X) :=
  FullFun.seq f (FullFun.case (FullFun.pure.map Sum.inl) g)

/-! ## Reading `f ; [inl, g]` and `f ; [id, h]` -/

section Body

variable {f : FullFun E S A (B ⊕ C)} {g : FullFun E S C (B ⊕ X)} {s : S} {a : A}

theorem mem_body {x : CallBeh E S (B ⊕ X)} :
    x ∈ (body f g).1 s a ↔
      (∃ c, (c, End.trap) ∈ f.1 s a ∧ x = (c, End.trap)) ∨
      (∃ c, (c, End.div) ∈ f.1 s a ∧ x = (c, End.div)) ∨
      (∃ c b s', (c, End.ret (.inl b) s') ∈ f.1 s a ∧ x = (c, End.ret (.inl b) s')) ∨
      ∃ c₁ s₁ y c₂ e, (c₁, End.ret (.inr y) s₁) ∈ f.1 s a ∧ (c₂, e) ∈ g.1 s₁ y ∧
        x = (c₁ ++ c₂, e) := by
  constructor
  · rintro (h | h | ⟨c₁, b | y, s₁, c₂, e, hf, hg, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · have hg' : (c₂, e) ∈ ((FullFun.pure : FullFun E S B B).map Sum.inl).1 s₁ b := hg
      rw [pure_map_fst, Set.mem_singleton_iff, Prod.mk.injEq] at hg'
      obtain ⟨rfl, rfl⟩ := hg'
      exact .inr (.inr (.inl ⟨c₁, b, s₁, hf, by simp⟩))
    · exact .inr (.inr (.inr ⟨c₁, s₁, y, c₂, e, hf, hg, rfl⟩))
  · rintro (h | h | ⟨c, b, s', hf, rfl⟩ | ⟨c₁, s₁, y, c₂, e, hf, hg, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · refine .inr (.inr ⟨c, .inl b, s', [], End.ret (.inl b) s', hf, ?_, by simp⟩)
      show _ ∈ ((FullFun.pure : FullFun E S B B).map Sum.inl).1 s' b
      rw [pure_map_fst]
      rfl
    · exact .inr (.inr ⟨c₁, .inr y, s₁, c₂, e, hf, hg, rfl⟩)

/-- A trap of `body f g` is one of `f`, or one of `g` after a continuing return of `f`. -/
theorem body_trap {c : List (Call E)} :
    (c, End.trap) ∈ (body f g).1 s a ↔ (c, End.trap) ∈ f.1 s a ∨
      ∃ c₁ s₁ y c₂, (c₁, End.ret (.inr y) s₁) ∈ f.1 s a ∧ (c₂, End.trap) ∈ g.1 s₁ y ∧
        c = c₁ ++ c₂ := by
  rw [mem_body]
  constructor
  · rintro (⟨c', hf, h⟩ | ⟨c', hf, h⟩ | ⟨c', b, s', hf, h⟩ | ⟨c₁, s₁, y, c₂, e', hf, hg, h⟩)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj h; exact .inl hf
    · cases h
    · cases h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact .inr ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩
  · rintro (hf | ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩)
    · exact .inl ⟨c, hf, rfl⟩
    · exact .inr (.inr (.inr ⟨c₁, s₁, y, c₂, _, hf, hg, rfl⟩))

/-- A divergence of `body f g` is one of `f`, or one of `g` after a continuing return of
`f`. -/
theorem body_div {c : List (Call E)} :
    (c, End.div) ∈ (body f g).1 s a ↔ (c, End.div) ∈ f.1 s a ∨
      ∃ c₁ s₁ y c₂, (c₁, End.ret (.inr y) s₁) ∈ f.1 s a ∧ (c₂, End.div) ∈ g.1 s₁ y ∧
        c = c₁ ++ c₂ := by
  rw [mem_body]
  constructor
  · rintro (⟨c', hf, h⟩ | ⟨c', hf, h⟩ | ⟨c', b, s', hf, h⟩ | ⟨c₁, s₁, y, c₂, e', hf, hg, h⟩)
    · cases h
    · obtain ⟨rfl, -⟩ := Prod.mk.inj h; exact .inl hf
    · cases h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact .inr ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩
  · rintro (hf | ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩)
    · exact .inr (.inl ⟨c, hf, rfl⟩)
    · exact .inr (.inr (.inr ⟨c₁, s₁, y, c₂, _, hf, hg, rfl⟩))

/-- An exit of `body f g` is one of `f`, or one of `g` after a continuing return of `f`. -/
theorem body_exit {c : List (Call E)} {b : B} {s' : S} :
    (c, End.ret (.inl b) s') ∈ (body f g).1 s a ↔ (c, End.ret (.inl b) s') ∈ f.1 s a ∨
      ∃ c₁ s₁ y c₂, (c₁, End.ret (.inr y) s₁) ∈ f.1 s a ∧
        (c₂, End.ret (.inl b) s') ∈ g.1 s₁ y ∧ c = c₁ ++ c₂ := by
  rw [mem_body]
  constructor
  · rintro (⟨c', hf, h⟩ | ⟨c', hf, h⟩ | ⟨c', b', s'', hf, h⟩ | ⟨c₁, s₁, y, c₂, e', hf, hg, h⟩)
    · cases h
    · cases h
    · cases h; exact .inl hf
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact .inr ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩
  · rintro (hf | ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩)
    · exact .inr (.inr (.inl ⟨c, b, s', hf, rfl⟩))
    · exact .inr (.inr (.inr ⟨c₁, s₁, y, c₂, _, hf, hg, rfl⟩))

/-- A continuing return of `body f g` is a continuing return of `f` followed by a continuing
return of `g`. -/
theorem body_cont {c : List (Call E)} {x' : X} {s' : S} :
    (c, End.ret (.inr x') s') ∈ (body f g).1 s a ↔
      ∃ c₁ s₁ y c₂, (c₁, End.ret (.inr y) s₁) ∈ f.1 s a ∧
        (c₂, End.ret (.inr x') s') ∈ g.1 s₁ y ∧ c = c₁ ++ c₂ := by
  rw [mem_body]
  constructor
  · rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨c₁, s₁, y, c₂, e, hf, hg, h⟩)
    · cases h
    · cases h
    · cases h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩
  · rintro ⟨c₁, s₁, y, c₂, hf, hg, rfl⟩
    exact .inr (.inr (.inr ⟨c₁, s₁, y, c₂, _, hf, hg, rfl⟩))

theorem body_of_g {c₁ : List (Call E)} {s₁ : S} {y : C} {c₂ : List (Call E)}
    {e : End S (B ⊕ X)} (hf : (c₁, End.ret (.inr y) s₁) ∈ f.1 s a) (hg : (c₂, e) ∈ g.1 s₁ y) :
    (c₁ ++ c₂, e) ∈ (body f g).1 s a :=
  mem_body.2 (.inr (.inr (.inr ⟨_, _, _, _, _, hf, hg, rfl⟩)))

theorem mem_body_inf {ω : Nat → Call E} :
    ω ∈ (body f g).2 s a ↔ ω ∈ f.2 s a ∨
      ∃ c s₁ y ω', (c, End.ret (.inr y) s₁) ∈ f.1 s a ∧ ω' ∈ g.2 s₁ y ∧ ω = c ++ₛ ω' := by
  constructor
  · rintro (h | ⟨c, b | y, s₁, ω', hf, hω, rfl⟩)
    · exact .inl h
    · exact hω.elim
    · exact .inr ⟨c, s₁, y, ω', hf, hω, rfl⟩
  · rintro (h | ⟨c, s₁, y, ω', hf, hω, rfl⟩)
    · exact .inl h
    · exact .inr ⟨c, .inr y, s₁, ω', hf, hω, rfl⟩

variable {h : FullFun E S C B}

theorem mem_seq_case_pure {x : CallBeh E S B} :
    x ∈ (FullFun.seq f (FullFun.case FullFun.pure h)).1 s a ↔
      (∃ c, (c, End.trap) ∈ f.1 s a ∧ x = (c, End.trap)) ∨
      (∃ c, (c, End.div) ∈ f.1 s a ∧ x = (c, End.div)) ∨
      (∃ c b s', (c, End.ret (.inl b) s') ∈ f.1 s a ∧ x = (c, End.ret b s')) ∨
      ∃ c₁ s₁ y c₂ e, (c₁, End.ret (.inr y) s₁) ∈ f.1 s a ∧ (c₂, e) ∈ h.1 s₁ y ∧
        x = (c₁ ++ c₂, e) := by
  constructor
  · rintro (h | h | ⟨c₁, b | y, s₁, c₂, e, hf, hg, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (c₂, e) = ([], End.ret b s₁) from hg)
      exact .inr (.inr (.inl ⟨c₁, b, s₁, hf, by simp⟩))
    · exact .inr (.inr (.inr ⟨c₁, s₁, y, c₂, e, hf, hg, rfl⟩))
  · rintro (h | h | ⟨c, b, s', hf, rfl⟩ | ⟨c₁, s₁, y, c₂, e, hf, hg, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨c, .inl b, s', [], _, hf, rfl, by simp⟩)
    · exact .inr (.inr ⟨c₁, .inr y, s₁, c₂, e, hf, hg, rfl⟩)

theorem mem_seq_case_pure_inf {ω : Nat → Call E} :
    ω ∈ (FullFun.seq f (FullFun.case FullFun.pure h)).2 s a ↔ ω ∈ f.2 s a ∨
      ∃ c s₁ y ω', (c, End.ret (.inr y) s₁) ∈ f.1 s a ∧ ω' ∈ h.2 s₁ y ∧ ω = c ++ₛ ω' := by
  constructor
  · rintro (h | ⟨c, b | y, s₁, ω', hf, hω, rfl⟩)
    · exact .inl h
    · exact hω.elim
    · exact .inr ⟨c, s₁, y, ω', hf, hω, rfl⟩
  · rintro (h | ⟨c, s₁, y, ω', hf, hω, rfl⟩)
    · exact .inl h
    · exact .inr ⟨c, .inr y, s₁, ω', hf, hω, rfl⟩

end Body

/-! ## Productive runs of an iteration -/

/-- A productive run of the body is one of the iteration. -/
theorem iter_inf_of_body (F : FullFun E S A (B ⊕ A)) {s : S} {a : A} {ω : Nat → Call E}
    (h : ω ∈ F.2 s a) : ω ∈ (FullFun.iter F).2 s a :=
  .inl ⟨[], s, a, ω, .refl, h, rfl⟩

/-- A continuing iteration in front of a productive run of the iteration. -/
theorem iter_inf_cons (F : FullFun E S A (B ⊕ A)) {s : S} {a : A} {c : List (Call E)} {a' : A}
    {s' : S} (hm : (c, End.ret (.inr a') s') ∈ F.1 s a) {ω : Nat → Call E}
    (hω : ω ∈ (FullFun.iter F).2 s' a') : c ++ₛ ω ∈ (FullFun.iter F).2 s a := by
  rw [iter_unfold_inf]
  exact .inr ⟨c, .inr a', s', ω, hm, hω, rfl⟩

/-! ## Dinaturality -/

section Dinat

variable {f : FullFun E S A (B ⊕ C)} {g : FullFun E S C (B ⊕ A)}

/-- The right-hand side of dinaturality. -/
abbrev dinatR (f : FullFun E S A (B ⊕ C)) (g : FullFun E S C (B ⊕ A)) : FullFun E S A B :=
  FullFun.seq f (FullFun.case FullFun.pure (FullFun.iter (body g f)))

/-- A continuing return of `g` in front of a behaviour of the right-hand side. -/
theorem iterBeh_psi_cons {s₁ : S} {x : C} {c₂ : List (Call E)} {a' : A} {s' : S}
    (hg : (c₂, End.ret (.inr a') s') ∈ g.1 s₁ x) {y : CallBeh E S B}
    (hy : y ∈ (dinatR f g).1 s' a') : AFun.IterBeh (body g f).1 s₁ x (c₂ ++ y.1, y.2) := by
  rcases mem_seq_case_pure.1 hy with ⟨c, hf, rfl⟩ | ⟨c, hf, rfl⟩ | ⟨c, b, s'', hf, rfl⟩ |
      ⟨c₁, s₂, x', c₃, e, hf, hi, rfl⟩
  · exact .trap (body_of_g hg hf)
  · exact .div (body_of_g hg hf)
  · exact .exit (body_of_g hg hf)
  · have := AFun.IterBeh.step (body_of_g hg hf) hi
    rwa [List.append_assoc] at this

/-- **Dinaturality**, left to right, finite behaviours. -/
theorem dinat_fin_lr {s : S} {a : A} {y : CallBeh E S B}
    (hy : AFun.IterBeh (body f g).1 s a y) : y ∈ (dinatR f g).1 s a := by
  induction hy with
  | exit hm =>
    rcases body_exit.1 hm with hf | ⟨c₁, s₁, x, c₂, hf, hg, rfl⟩
    · exact mem_seq_case_pure.2 (.inr (.inr (.inl ⟨_, _, _, hf, rfl⟩)))
    · exact mem_seq_case_pure.2 (.inr (.inr (.inr ⟨c₁, s₁, x, c₂, _, hf,
        AFun.IterBeh.exit (body_exit.2 (.inl hg)), rfl⟩)))
  | trap hm =>
    rcases body_trap.1 hm with hf | ⟨c₁, s₁, x, c₂, hf, hg, rfl⟩
    · exact mem_seq_case_pure.2 (.inl ⟨_, hf, rfl⟩)
    · exact mem_seq_case_pure.2 (.inr (.inr (.inr ⟨c₁, s₁, x, c₂, _, hf,
        AFun.IterBeh.trap (body_trap.2 (.inl hg)), rfl⟩)))
  | div hm =>
    rcases body_div.1 hm with hf | ⟨c₁, s₁, x, c₂, hf, hg, rfl⟩
    · exact mem_seq_case_pure.2 (.inr (.inl ⟨_, hf, rfl⟩))
    · exact mem_seq_case_pure.2 (.inr (.inr (.inr ⟨c₁, s₁, x, c₂, _, hf,
        AFun.IterBeh.div (body_div.2 (.inl hg)), rfl⟩)))
  | step hm _ ih =>
    obtain ⟨c₁, s₁, x, c₂, hf, hg, rfl⟩ := body_cont.1 hm
    have := iterBeh_psi_cons hg ih
    rw [List.append_assoc]
    exact mem_seq_case_pure.2 (.inr (.inr (.inr ⟨c₁, s₁, x, _, _, hf, this, rfl⟩)))
  | spin σ h0 hσ =>
    choose c₁ s₁ x c₂ hf hg hc using fun n => body_cont.1 (hσ n)
    have h1 : ∀ n, c₁ n = [] := fun n => (List.append_eq_nil_iff.1 (hc n).symm).1
    have h2 : ∀ n, c₂ n = [] := fun n => (List.append_eq_nil_iff.1 (hc n).symm).2
    have hf0 := hf 0
    rw [h0, h1 0] at hf0
    refine mem_seq_case_pure.2 (.inr (.inr (.inr ⟨[], s₁ 0, x 0, [], .div, hf0, ?_, rfl⟩)))
    refine AFun.IterBeh.spin (fun n => (s₁ n, x n)) rfl fun n => ?_
    have := body_of_g (hg n) (hf (n + 1))
    rw [h2 n, h1 (n + 1)] at this
    exact this

/-- **Dinaturality**, right to left, finite behaviours: a continuing return of `f` in front of
a behaviour of `iter (body g f)`. -/
theorem iterBeh_phi_of_psi {s₁ : S} {x : C} {y : CallBeh E S B}
    (hy : AFun.IterBeh (body g f).1 s₁ x y) :
    ∀ {s : S} {a : A} {c₁ : List (Call E)}, (c₁, End.ret (.inr x) s₁) ∈ f.1 s a →
      AFun.IterBeh (body f g).1 s a (c₁ ++ y.1, y.2) := by
  induction hy with
  | exit hm =>
    intro s a c₁ hf
    rcases body_exit.1 hm with hg | ⟨c₂, s₂, a', c₃, hg, hf', rfl⟩
    · exact .exit (body_of_g hf hg)
    · have := AFun.IterBeh.step (body_of_g hf hg) (.exit (body_exit.2 (.inl hf')))
      rwa [List.append_assoc] at this
  | trap hm =>
    intro s a c₁ hf
    rcases body_trap.1 hm with hg | ⟨c₂, s₂, a', c₃, hg, hf', rfl⟩
    · exact .trap (body_of_g hf hg)
    · have := AFun.IterBeh.step (body_of_g hf hg) (.trap (body_trap.2 (.inl hf')))
      rwa [List.append_assoc] at this
  | div hm =>
    intro s a c₁ hf
    rcases body_div.1 hm with hg | ⟨c₂, s₂, a', c₃, hg, hf', rfl⟩
    · exact .div (body_of_g hf hg)
    · have := AFun.IterBeh.step (body_of_g hf hg) (.div (body_div.2 (.inl hf')))
      rwa [List.append_assoc] at this
  | step hm _ ih =>
    intro s a c₁ hf
    obtain ⟨c₂, s₂, a', c₃, hg, hf', rfl⟩ := body_cont.1 hm
    have := AFun.IterBeh.step (body_of_g hf hg) (ih hf')
    simpa only [List.append_assoc] using this
  | spin τ h0 hτ =>
    intro s a c₁ hf
    choose cg s₂ a' cf hg hf' hc using fun n => body_cont.1 (hτ n)
    have h1 : ∀ n, cg n = [] := fun n => (List.append_eq_nil_iff.1 (hc n).symm).1
    have h2 : ∀ n, cf n = [] := fun n => (List.append_eq_nil_iff.1 (hc n).symm).2
    have hg0 := hg 0
    rw [h0, h1 0] at hg0
    have := AFun.IterBeh.step (body_of_g hf hg0)
      (AFun.IterBeh.spin (fun n => (s₂ n, a' n)) rfl fun n => by
        have := body_of_g (hf' n) (hg (n + 1))
        rw [h2 n, h1 (n + 1)] at this
        exact this)
    simpa using this

theorem dinat_fin_rl {s : S} {a : A} {y : CallBeh E S B} (hy : y ∈ (dinatR f g).1 s a) :
    AFun.IterBeh (body f g).1 s a y := by
  rcases mem_seq_case_pure.1 hy with ⟨c, hf, rfl⟩ | ⟨c, hf, rfl⟩ | ⟨c, b, s', hf, rfl⟩ |
      ⟨c₁, s₁, x, c₂, e, hf, hi, rfl⟩
  · exact .trap (body_trap.2 (.inl hf))
  · exact .div (body_div.2 (.inl hf))
  · exact .exit (body_exit.2 (.inl hf))
  · exact iterBeh_phi_of_psi hi hf

/-- **Dinaturality**, finite behaviours. -/
theorem iter_dinat_fin (f : FullFun E S A (B ⊕ C)) (g : FullFun E S C (B ⊕ A)) :
    (FullFun.iter (body f g)).1 = (dinatR f g).1 := by
  funext s a
  ext y
  exact ⟨dinat_fin_lr, dinat_fin_rl⟩

/-- A continuing return of `g` in front of a productive run of the right-hand side. -/
theorem inf_psi_cons {s₁ : S} {x : C} {c₂ : List (Call E)} {a' : A} {s' : S}
    (hg : (c₂, End.ret (.inr a') s') ∈ g.1 s₁ x) {ζ : Nat → Call E}
    (hζ : ζ ∈ (dinatR f g).2 s' a') : c₂ ++ₛ ζ ∈ (FullFun.iter (body g f)).2 s₁ x := by
  rcases mem_seq_case_pure_inf.1 hζ with hf | ⟨c₃, s₂, x', ζ', hf, hζ', rfl⟩
  · exact iter_inf_of_body _ (mem_body_inf.2 (.inr ⟨c₂, s', a', ζ, hg, hf, rfl⟩))
  · have := iter_inf_cons (body g f) (body_of_g hg hf) hζ'
    rwa [append_appendStream] at this

theorem dinat_inf_lr_chain {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (hc : FullFun.ContChain (body f g).1 s a c s' a') :
    ∀ {ω : Nat → Call E}, ω ∈ (body f g).2 s' a' → c ++ₛ ω ∈ (dinatR f g).2 s a := by
  induction hc with
  | refl =>
    intro ω hω
    rcases mem_body_inf.1 hω with h | ⟨c, s₁, x, ω', hf, hg, rfl⟩
    · exact mem_seq_case_pure_inf.2 (.inl h)
    · exact mem_seq_case_pure_inf.2
        (.inr ⟨c, s₁, x, ω', hf, iter_inf_of_body _ (mem_body_inf.2 (.inl hg)), rfl⟩)
  | step hm _ ih =>
    intro ω hω
    obtain ⟨c₁, s₁, x, c₂, hf, hg, rfl⟩ := body_cont.1 hm
    exact mem_seq_case_pure_inf.2 (.inr ⟨c₁, s₁, x, _, hf, inf_psi_cons hg (ih hω),
      (append_appendStream (c₁ ++ c₂) _ ω).trans (append_appendStream c₁ c₂ _)⟩)

theorem dinat_inf_lr {s : S} {a : A} {ω : Nat → Call E}
    (hω : ω ∈ (FullFun.iter (body f g)).2 s a) : ω ∈ (dinatR f g).2 s a := by
  rcases hω with ⟨c, s', a', ω', hc, hω', rfl⟩ | ⟨σ, l, h0, hσ, hl⟩
  · exact dinat_inf_lr_chain hc hω'
  · choose c₁ s₁ x c₂ hf hg hc using fun n => body_cont.1 (hσ n)
    obtain rfl : l = fun n => c₁ n ++ c₂ n := funext hc
    obtain ⟨ζ, rfl, hζ⟩ := streamConcat_interleave_tail hl
    have hf0 := hf 0
    rw [h0] at hf0
    exact mem_seq_case_pure_inf.2 (.inr ⟨c₁ 0, s₁ 0, x 0, ζ, hf0,
      .inr ⟨fun n => (s₁ n, x n), fun n => c₂ n ++ c₁ (n + 1), rfl,
        fun n => body_of_g (hg n) (hf (n + 1)), hζ⟩, rfl⟩)

theorem dinat_inf_rl_chain {s₁ : S} {x : C} {c : List (Call E)} {s' : S} {x' : C}
    (hc : FullFun.ContChain (body g f).1 s₁ x c s' x') :
    ∀ {s : S} {a : A} {c₁ : List (Call E)}, (c₁, End.ret (.inr x) s₁) ∈ f.1 s a →
      ∀ {ζ : Nat → Call E}, ζ ∈ (body g f).2 s' x' →
        c₁ ++ₛ (c ++ₛ ζ) ∈ (FullFun.iter (body f g)).2 s a := by
  induction hc with
  | refl =>
    intro s a c₁ hf ζ hζ
    rcases mem_body_inf.1 hζ with hg | ⟨c₂, s₂, a', ζ', hg, hf', rfl⟩
    · exact iter_inf_of_body _ (mem_body_inf.2 (.inr ⟨c₁, _, _, ζ, hf, hg, rfl⟩))
    · have := iter_inf_cons (body f g) (body_of_g hf hg)
        (iter_inf_of_body _ (mem_body_inf.2 (.inl hf')))
      rw [append_appendStream] at this
      exact this
  | @step _ _ _ _ _ c' _ _ hm _ ih =>
    intro s a c₁ hf ζ hζ
    obtain ⟨c₂, s₂, a', c₃, hg, hf', rfl⟩ := body_cont.1 hm
    have := iter_inf_cons (body f g) (body_of_g hf hg) (ih hf' hζ)
    have e : c₁ ++ₛ ((c₂ ++ c₃ ++ c') ++ₛ ζ) = (c₁ ++ c₂) ++ₛ (c₃ ++ₛ (c' ++ₛ ζ)) :=
      (congrArg (c₁ ++ₛ ·) ((append_appendStream (c₂ ++ c₃) c' ζ).trans
        (append_appendStream c₂ c₃ _))).trans (append_appendStream c₁ c₂ _).symm
    rw [e]
    exact this

theorem dinat_inf_rl {s : S} {a : A} {ω : Nat → Call E} (hω : ω ∈ (dinatR f g).2 s a) :
    ω ∈ (FullFun.iter (body f g)).2 s a := by
  rcases mem_seq_case_pure_inf.1 hω with hf | ⟨c₁, s₁, x, ζ, hf, hζ, rfl⟩
  · exact iter_inf_of_body _ (mem_body_inf.2 (.inl hf))
  · rcases hζ with ⟨c, s', x', ζ', hc, hζ', rfl⟩ | ⟨τ, m, h0, hτ, hm⟩
    · exact dinat_inf_rl_chain hc hf hζ'
    · choose cg s₂ a' cf hg hf' hc using fun n => body_cont.1 (hτ n)
      obtain rfl : m = fun n => cg n ++ cf n := funext hc
      refine .inr ⟨fun n => match n with | 0 => (s, a) | n + 1 => (s₂ n, a' n),
        fun n => (match n with | 0 => c₁ | n + 1 => cf n) ++ cg n, rfl, fun n => ?_,
        streamConcat_interleave (a := fun n => match n with | 0 => c₁ | n + 1 => cf n)
          (b := cg) hm⟩
      cases n with
      | zero =>
        have hg0 := hg 0
        rw [h0] at hg0
        exact body_of_g hf hg0
      | succ n => exact body_of_g (hf' n) (hg (n + 1))

/-- **Dinaturality**, productive runs. -/
theorem iter_dinat_inf (f : FullFun E S A (B ⊕ C)) (g : FullFun E S C (B ⊕ A)) :
    (FullFun.iter (body f g)).2 = (dinatR f g).2 := by
  funext s a
  ext ω
  exact ⟨dinat_inf_lr, dinat_inf_rl⟩

/-- **Dinaturality of iteration**: `iter (f ; [inl, g]) = f ; [id, iter (g ; [inl, f])]`. -/
theorem iter_dinat (f : FullFun E S A (B ⊕ C)) (g : FullFun E S C (B ⊕ A)) :
    FullFun.iter (body f g) = dinatR f g :=
  Prod.ext (iter_dinat_fin f g) (iter_dinat_inf f g)

end Dinat

end Silmaril.Proofs.Games.Abstract.FullFun
