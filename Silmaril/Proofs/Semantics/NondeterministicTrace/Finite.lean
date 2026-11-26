module

public import Silmaril.Semantics.NondeterministicTrace.Defs

public section

namespace Silmaril.Proofs.Semantics.NondeterministicTrace.Finite

open Silmaril.Elgot
open scoped Silmaril.Elgot.Nondet
open Silmaril.Semantics.NondeterministicTrace Finite

universe u

variable {W A B : Type u} [Monoid W]

omit [Monoid W] in
theorem outcomes_injective : Function.Injective (outcomes : Finite W A → Set (A × W)) :=
  fun {_ _} h => WriterT.ext _ _ (Nondet.ext (fun x => Set.ext_iff.mp h x))

theorem mem_bind {p : Finite W A} {k : A → Finite W B} {b : B} {w : W} :
    (b, w) ∈ outcomes (p >>= k) ↔
      ∃ a u v, (a, u) ∈ p.outcomes ∧ (b, v) ∈ (k a).outcomes ∧ u * v = w := by
  change (b, w) ∈ₘ (p.run >>= fun (a, u) => (fun (c, v) => (c, u * v)) <$> (k a).run) ↔ _
  simp only [Nondet.mem_bind_iff, ← bind_pure_comp, Nondet.mem_pure_iff]
  constructor
  · rintro ⟨⟨a, u⟩, hp, ⟨c, v⟩, hk, h⟩
    cases h
    exact ⟨a, u, v, hp, hk, rfl⟩
  · rintro ⟨a, u, v, hp, hk, rfl⟩
    exact ⟨(a, u), hp, (b, v), hk, rfl⟩

theorem outcomes_bind_pure (p : Finite W A) (f : A → B) :
    outcomes (p >>= pure ∘ f) = Prod.map f id '' p.outcomes := by
  ext ⟨b, w⟩
  rw [mem_bind]
  change (∃ a u v, (a, u) ∈ p.outcomes ∧ (b, v) ∈ₘ (pure (f a, 1) : SetM (B × W)) ∧
    u * v = w) ↔ _
  simp only [Nondet.mem_pure_iff]
  constructor
  · rintro ⟨a, u, v, hp, eq, he⟩
    cases eq
    exact ⟨(a, u), hp, Prod.ext rfl (by simpa using he)⟩
  · rintro ⟨⟨a, u⟩, hp, eq⟩
    cases eq
    exact ⟨a, u, 1, hp, rfl, mul_one _⟩

private theorem body_mem (f : A → Finite W (B ⊕ A)) (a : A) (prefixLog : W)
    (s : (B × W) ⊕ (A × W)) :
    s ∈ₘ Elgot.WriterT.body f (a, prefixLog) ↔
      ∃ p ∈ (f a).outcomes, Elgot.StateT.distribute (p.1, prefixLog * p.2) = s := by
  simp only [Elgot.WriterT.body, Elgot.StateT.body, Elgot.WriterT.toState, StateT.run,
    bind_assoc, pure_bind, Function.comp_apply, Nondet.mem_bind_iff, Nondet.mem_pure_iff]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

private theorem runs_to_state {f : A → Finite W (B ⊕ A)} {a : A} {b : B} {w : W}
    (hr : Runs f a b w) (prefixLog : W) :
    Nondet.Runs (Elgot.WriterT.body f) (a, prefixLog) (b, prefixLog * w) := by
  induction hr generalizing prefixLog with
  | done h =>
    apply Nondet.Runs.done
    exact (body_mem _ _ _ _).2 ⟨_, h, rfl⟩
  | @more a next b u v edge tail ih =>
    rw [← mul_assoc]
    exact .more ((body_mem _ _ _ _).2 ⟨_, edge, rfl⟩) (ih (prefixLog * u))

private theorem runs_from_state {f : A → Finite W (B ⊕ A)} {start : A × W} {finish : B × W}
    (hr : Nondet.Runs (Elgot.WriterT.body f) start finish) :
    ∃ w, Runs f start.1 finish.1 w ∧ start.2 * w = finish.2 := by
  induction hr with
  | @done start finish edge =>
    obtain ⟨⟨s, w⟩, hs, eq⟩ := (body_mem f start.1 start.2 _).1 edge
    cases s with
    | inl b =>
      simp only [Elgot.StateT.distribute, Sum.inl.injEq] at eq
      rw [← eq]
      exact ⟨w, .done hs, rfl⟩
    | inr a => cases eq
  | @more start next finish edge tail ih =>
    obtain ⟨⟨s, u⟩, hs, eq⟩ := (body_mem f start.1 start.2 _).1 edge
    cases s with
    | inl b => cases eq
    | inr a =>
      simp only [Elgot.StateT.distribute, Sum.inr.injEq] at eq
      subst next
      obtain ⟨v, hv, hlog⟩ := ih
      exact ⟨u * v, .more hs hv, (mul_assoc _ _ _).symm.trans hlog⟩

theorem mem_iter (f : A → Finite W (B ⊕ A)) (a : A) (b : B) (w : W) :
    (b, w) ∈ outcomes (iter f a) ↔ Runs f a b w := by
  change (b, w) ∈ₘ (iter f a).run ↔ _
  rw [Elgot.WriterT.run_iter, Nondet.mem_iter_iff]
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := runs_from_state h
    simp only [one_mul] at he
    exact he ▸ hv
  · intro h
    simpa only [one_mul] using runs_to_state h 1

theorem unfold_eq_bind (f : A → Finite W (B ⊕ A)) (k : A → Set (B × W)) (a : A) :
    unfoldLoop f k a = outcomes (f a >>= Sum.elim pure (fun next => ofOutcomes (k next))) := by
  ext ⟨b, w⟩
  rw [mem_bind]
  constructor
  · rintro (done | ⟨next, u, v, edge, tail, he⟩)
    · exact ⟨.inl b, w, 1, done, rfl, mul_one _⟩
    · exact ⟨.inr next, u, v, edge, tail, he⟩
  · rintro ⟨s, u, v, edge, tail, he⟩
    cases s with
    | inl r =>
      change (b, v) ∈ₘ (pure (r, 1) : SetM (B × W)) at tail
      have eq := Nondet.mem_pure_iff.mp tail
      cases eq
      rw [mul_one] at he
      exact Or.inl (he ▸ edge)
    | inr next => exact Or.inr ⟨next, u, v, edge, tail, he⟩

theorem iter_eq_lfp (f : A → Finite W (B ⊕ A)) :
    (fun a => outcomes (iter f a)) = (unfoldLoop f).lfp := by
  apply le_antisymm
  · apply (unfoldLoop f).le_lfp
    intro k closed a
    rintro ⟨b, w⟩ h
    have run := (mem_iter f a b w).1 h
    clear h
    induction run with
    | done edge => exact closed _ (Or.inl edge)
    | more edge tail ih => exact closed _ (Or.inr ⟨_, _, _, edge, ih, rfl⟩)
  · apply (unfoldLoop f).lfp_le_fixed
    funext a
    rw [unfold_eq_bind]
    exact congrArg outcomes (congrFun (LawfulElgotMonad.fixpoint f) a).symm

end Silmaril.Proofs.Semantics.NondeterministicTrace.Finite
