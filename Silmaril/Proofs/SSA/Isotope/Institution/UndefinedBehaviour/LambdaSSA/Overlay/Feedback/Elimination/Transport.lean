module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Transport.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Thms

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.Transport

open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

variable {P Q O U : Type*} {g : Graph P O} {h : Graph Q U}
  {point : P → Q} {output : O → U} (rel : Graph.Transport g h point output)

include rel

private theorem map_reach {p q : P} (path : g.Reaches p q) :
    h.Reaches (point p) (point q) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail ((rel.step _ _).mpr ⟨_, step, rfl⟩)

private theorem lift_reach {p : P} {q : Q} (path : h.Reaches (point p) q) :
    ∃ t, g.Reaches p t ∧ point t = q := by
  induction path with
  | refl => exact ⟨p, .refl, rfl⟩
  | tail _ step ih =>
    obtain ⟨t, path, rfl⟩ := ih
    obtain ⟨next, move, rfl⟩ := (rel.step _ _).mp step
    exact ⟨next, path.tail move, rfl⟩

private theorem infinite (p : P) : h.Infinite (point p) ↔ g.Infinite p := by
  constructor
  · rintro ⟨path, start, edge⟩
    let Lift (n : Nat) := {q : P // point q = path n}
    have next (n : Nat) (a : Lift n) : ∃ b, g.step a.val b ∧ point b = path (n + 1) :=
      (rel.step _ _).mp (a.property.symm ▸ edge n)
    let lifted : (n : Nat) → Lift n := Nat.rec ⟨p, start.symm⟩ fun n a =>
      ⟨(next n a).choose, (next n a).choose_spec.2⟩
    exact ⟨fun n => (lifted n).val, rfl, fun n => (next n (lifted n)).choose_spec.1⟩
  · rintro ⟨path, start, edge⟩
    exact ⟨point ∘ path, congrArg point start, fun n => (rel.step _ _).mpr ⟨_, edge n, rfl⟩⟩

theorem close_eq (p : P) : h.close (point p) = (g.close p).map (Set.image output) := by
  have ub : h.ReachesUB (point p) ↔ g.ReachesUB p := by
    constructor
    · rintro ⟨q, path, top⟩
      obtain ⟨t, reached, rfl⟩ := lift_reach rel path
      exact ⟨t, reached, (rel.ub _).mp top⟩
    · rintro ⟨q, path, top⟩
      exact ⟨_, map_reach rel path, (rel.ub _).mpr top⟩
  by_cases top : g.ReachesUB p
  · rw [Graph.close_top_iff.mpr top, Graph.close_top_iff.mpr (ub.mpr top)]
    rfl
  · have noTop : ¬ h.ReachesUB (point p) := fun bad => top (ub.mp bad)
    simp only [Graph.close, top, noTop, ite_false, WithTop.map_coe, WithTop.coe_inj]
    ext u
    constructor
    · rintro (⟨q, path, finish⟩ | ⟨rfl, inf⟩)
      · obtain ⟨t, reached, rfl⟩ := lift_reach rel path
        obtain ⟨o, fin, rfl⟩ := (rel.finish _ _).mp finish
        exact ⟨o, Or.inl ⟨t, reached, fin⟩, rfl⟩
      · exact ⟨g.divergence, Or.inr ⟨rfl, (infinite rel p).mp inf⟩, rel.divergence⟩
    · rintro ⟨o, fin | ⟨rfl, inf⟩, rfl⟩
      · obtain ⟨q, path, finish⟩ := fin
        exact Or.inl ⟨_, map_reach rel path, (rel.finish _ _).mpr ⟨o, finish, rfl⟩⟩
      · exact Or.inr ⟨rel.divergence, (infinite rel p).mpr inf⟩

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope (Value)

omit rel

section Transitions

universe u v w x y

variable {κ : Type u} {R L : List (Silmaril.Ty κ)}
  {α : Type v} {σ : Type w} {P : Type x} {O : Type y}

private theorem finish_eq (a b : Outcome L.length α σ) :
    Behaviour.Ordinary (WithTop.some {Feedback.external R L a}) (Feedback.external R L b) ↔ a = b := by
  cases a <;> cases b <;> simp [Behaviour.Ordinary, Behaviour.possible, Feedback.external, Fin.ext_iff, eq_comm]

private theorem branch_no_finish (i : Fin R.length) (a : Value α) (s : σ)
    (o : Outcome L.length α σ) :
    ¬ Behaviour.Ordinary (WithTop.some {Outcome.ret (Feedback.internal R L i) a s}) (Feedback.external R L o) := by
  cases o <;> simp [Behaviour.Ordinary, Behaviour.possible, Feedback.internal, Feedback.external, Fin.ext_iff]
  omega

theorem transitions_run (next : P → P ⊕ O) (diverge : O)
    (invoke : P → Fin R.length × Value α × σ) (output : O → Outcome L.length α σ)
    (f : Feedback.Run R L α σ) (div : output diverge = .diverge)
    (localRow : ∀ p, f (.block (invoke p).1 (invoke p).2.1 (invoke p).2.2) =
      match next p with
      | .inl q => WithTop.some {Outcome.ret (Feedback.internal R L (invoke q).1) (invoke q).2.1 (invoke q).2.2}
      | .inr o => WithTop.some {Feedback.external R L (output o)}) :
    Graph.Transport (Graph.transitions next diverge) (Graph.ofRun f)
      (fun p => .block (invoke p).1 (invoke p).2.1 (invoke p).2.2) output := by
  refine ⟨?_, ?_, ?_, div⟩
  · intro p q
    have atPoint := localRow p
    cases edge : next p with
    | inl n =>
      rw [edge] at atPoint
      change Feedback.Step f _ q ↔ _
      rw [step_of_branch_iff atPoint]
      simp [Graph.transitions, edge, eq_comm]
    | inr o =>
      rw [edge] at atPoint
      change Feedback.Step f _ q ↔ _
      simp [Graph.transitions, edge, no_step_of_terminal (q := q) atPoint]
  · intro p
    change f _ = ⊤ ↔ False
    rw [localRow]
    cases next p <;> simp
  · intro p u
    change Behaviour.Ordinary (f _) (Feedback.external R L u) ↔ _
    rw [localRow]
    cases edge : next p with
    | inl n =>
      simp only [Graph.transitions, edge, Sum.inl_ne_inr, false_and, exists_false, iff_false]
      exact branch_no_finish (R := R) (L := L) (invoke n).1 (invoke n).2.1 (invoke n).2.2 u
    | inr o =>
      rw [finish_eq (R := R) (L := L)]
      simp [Graph.transitions, edge]

end Transitions

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.Transport
