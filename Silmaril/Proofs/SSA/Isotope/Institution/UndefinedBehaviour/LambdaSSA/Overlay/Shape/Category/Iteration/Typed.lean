module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration

open Silmaril Silmaril.Isotope CategoryTheory
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape (ReturnsTyped ValueTyped)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B : Ty κ}
variable (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType))
variable (a : singlePayload (atomType := atomType) A)

set_option backward.isDefEq.respectTransparency false

local notation "Invocation" => singlePayload (atomType := atomType) A × σ

private def point (p : Invocation) : Feedback.Point ([A] : List (Ty κ)).length α σ :=
  .block 0 p.1.val p.2

private theorem block_top (p : Invocation) :
    iterationGraph f a (point p) = ⊤ ↔ f.run 0 p.1 p.2 = ⊤ := by
  change (f.total 0 p.1.val p.2).map _ = ⊤ ↔ _
  rw [Arrow.total_typed f 0 p.1 p.2, WithTop.map_eq_top_iff]

theorem block_ordinary (p : Invocation) (o : Outcome 2 α σ) :
    (iterationGraph f a (.block 0 p.1.val p.2)).Ordinary o ↔
      (f.run 0 p.1 p.2).Ordinary (tagIterationOutcome o) := by
  change Behaviour.Ordinary ((f.total 0 p.1.val p.2).map (Set.preimage tagIterationOutcome)) o ↔ _
  rw [Arrow.total_typed f 0 p.1 p.2]
  cases f.run 0 p.1 p.2 using WithTop.recTopCoe with
  | top => simp [Behaviour.Ordinary]
  | coe os => simp [Behaviour.Ordinary, Behaviour.possible]

private theorem entry_edge (s : σ) : Feedback.Step (R := [A]) (L := [B]) (iterationGraph f a) (.entry s) (point (a, s)) :=
  .branch ⟨WithTop.coe_ne_top, rfl⟩

private theorem entry_edge_eq {s : σ} {q : Feedback.Point ([A] : List (Ty κ)).length α σ}
    (step : Feedback.Step (R := [A]) (L := [B]) (iterationGraph f a) (.entry s) q) : q = point (a, s) := by
  cases step with
  | @branch i b t reached =>
    have h : Outcome.ret (Feedback.internal [A] [B] i) b t = .ret (0 : Fin 2) a.val s := reached.2
    obtain ⟨_, rfl, rfl⟩ := Outcome.ret.inj h
    rw [Fin.eq_zero i]
    rfl

private theorem repeat_edge {p q : Invocation} (transfer : Repeat f p q) :
    Feedback.Step (R := [A]) (L := [B]) (iterationGraph f a) (point p) (point q) :=
  .branch ((block_ordinary f a p (.ret 0 q.1.val q.2)).mpr transfer)

private theorem edge_repeat {p : Invocation} {q : Feedback.Point ([A] : List (Ty κ)).length α σ}
    (step : Feedback.Step (R := [A]) (L := [B]) (iterationGraph f a) (point p) q) :
    ∃ next, point (A := A) next = q ∧ Repeat f p next := by
  cases step with
  | @branch i b t reached =>
    have hi := Fin.eq_zero i
    subst i
    have ret : (f.run 0 p.1 p.2).Ordinary (.ret 0 (.inr b) t) :=
      (block_ordinary f a p (.ret 0 b t)).mp reached
    have typed := f.returnsTyped 0 p.1 p.2 ret
    cases typed with
    | inr typed => exact ⟨(⟨b, typed⟩, t), rfl, ret⟩

private theorem reached_invocation {p : Invocation} {q : Feedback.Point ([A] : List (Ty κ)).length α σ}
    (path : Feedback.Reaches (R := [A]) (L := [B]) (iterationGraph f a) (point p) q) :
    ∃ next, point (A := A) next = q ∧ Relation.ReflTransGen (Repeat f) p next := by
  induction path with
  | refl => exact ⟨p, rfl, .refl⟩
  | tail _ edge ih =>
    obtain ⟨current, rfl, first⟩ := ih
    obtain ⟨next, rfl, transfer⟩ := edge_repeat f a edge
    exact ⟨next, rfl, first.tail transfer⟩

private theorem reaches_from_entry {s : σ} {q : Feedback.Point ([A] : List (Ty κ)).length α σ}
    (path : Feedback.Reaches (R := [A]) (L := [B]) (iterationGraph f a) (.entry s) q) :
    q = .entry s ∨ ∃ p, point (A := A) p = q ∧ Relation.ReflTransGen (Repeat f) (a, s) p := by
  rcases path.cases_head with rfl | ⟨first, edge, rest⟩
  · exact .inl rfl
  · exact .inr (reached_invocation f a (entry_edge_eq f a edge ▸ rest))

private theorem typed_path_in_graph {s : σ} {p : Invocation}
    (path : Relation.ReflTransGen (Repeat f) (a, s) p) :
    Feedback.Reaches (R := [A]) (L := [B]) (iterationGraph f a) (.entry s) (point p) := by
  induction path with
  | refl => exact .single (entry_edge f a s)
  | tail _ transfer ih => exact ih.tail (repeat_edge f a transfer)

theorem iterateObservations_top_iff (s : σ) :
    iterateObservations f a s = ⊤ ↔
      ∃ p, Relation.ReflTransGen (Repeat f) (a, s) p ∧ f.run 0 p.1 p.2 = ⊤ := by
  change Feedback.close (iterationGraph f a) (.entry s) = ⊤ ↔ _
  rw [Feedback.close_eq_top_iff]
  constructor
  · rintro ⟨q, reach, top⟩
    rcases reaches_from_entry f a reach with rfl | ⟨p, rfl, path⟩
    · exact (WithTop.coe_ne_top top).elim
    · exact ⟨p, path, (block_top f a p).mp top⟩
  · rintro ⟨p, path, top⟩
    exact ⟨point p, typed_path_in_graph f a path, (block_top f a p).mpr top⟩

theorem iterateObservations_typed (s : σ) :
    ReturnsTyped atomType (L := [B]) (iterateObservations f a s) := by
  intro i b t result
  have hi := Fin.eq_zero i
  subst i
  rcases (Feedback.ordinary_close_iff.mp result).2 with ⟨q, reach, finish⟩ | ⟨impossible, _⟩
  · rcases reaches_from_entry f a reach with rfl | ⟨p, rfl, _⟩
    · have eq : Outcome.ret (1 : Fin 2) b t = .ret 0 a.val s := finish.2
      cases eq
    · have ret : (f.run 0 p.1 p.2).Ordinary (.ret 0 (.inl b) t) :=
        (block_ordinary f a p (.ret 1 b t)).mp finish
      have typed := f.returnsTyped 0 p.1 p.2 ret
      cases typed
      assumption
  · cases impossible

theorem iterateObservations_no_repeat (s : σ) (noRepeat : ∀ p, ¬ Repeat f (a, s) p)
    (os : Set (Outcome 1 α σ)) (run : f.run 0 a s = ↑os) :
    iterateObservations f a s =
      WithTop.some (Set.preimage (tagIterationOutcome ∘ Feedback.external [A] [B]) os) := by
  let graph := iterationGraph f a
  let start : Feedback.Point ([A] : List (Ty κ)).length α σ := .entry s
  have reached {q} (path : Feedback.Reaches (R := [A]) (L := [B]) graph start q) :
      q = start ∨ q = point (a, s) := by
    rcases reaches_from_entry f a path with eq | ⟨p, eq, trail⟩
    · exact .inl eq
    · obtain rfl := (Relation.reflTransGen_iff_eq noRepeat).mp trail
      exact .inr eq.symm
  have noUB : ¬ Feedback.ReachesUB (R := [A]) (L := [B]) graph start := by
    rintro ⟨q, path, top⟩
    rcases reached path with rfl | rfl
    · exact WithTop.coe_ne_top top
    · exact WithTop.coe_ne_top (run ▸ (block_top f a (a, s)).mp top)
  have noInfinite : ¬ Feedback.Infinite (R := [A]) (L := [B]) graph start := by
    rintro ⟨path, first, edges⟩
    have second := entry_edge_eq f a (first ▸ edges 0)
    obtain ⟨next, _, transfer⟩ := edge_repeat f a (second ▸ edges 1)
    exact noRepeat next transfer
  change Feedback.close graph start = _
  rw [Feedback.close_of_noUB noUB]
  apply congrArg WithTop.some
  ext o
  have last : (graph (point (a, s))).Ordinary (Feedback.external [A] [B] o) ↔
      o ∈ Set.preimage (tagIterationOutcome ∘ Feedback.external [A] [B]) os := by
    have step := block_ordinary f a (a, s) (Feedback.external [A] [B] o)
    rw [run] at step
    exact step.trans ⟨fun h => h.2, fun h => ⟨WithTop.coe_ne_top, h⟩⟩
  change (Feedback.Finite graph start o ∨ o = .diverge ∧ Feedback.Infinite graph start) ↔ _
  constructor
  · rintro (⟨q, path, obs⟩ | ⟨_, inf⟩)
    · rcases reached path with rfl | rfl
      · cases o with
        | ret i b t =>
          have eq : Feedback.external [A] [B] (.ret i b t) = .ret (0 : Fin 2) a.val s := obs.2
          have label := congrArg Fin.val (Outcome.ret.inj eq).1
          change 1 + i.val = 0 at label
          omega
        | fault | diverge => cases obs.2
      · exact last.mp obs
    · exact (noInfinite inf).elim
  · intro h
    exact .inl ⟨point (a, s), .single (entry_edge f a s), last.mpr h⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration
