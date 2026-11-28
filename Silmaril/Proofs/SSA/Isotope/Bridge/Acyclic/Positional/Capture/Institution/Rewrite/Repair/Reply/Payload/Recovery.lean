module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

open Kleisli (value)

private theorem emit_path_inj {R : Type} {es fs : List Bool} {x y : R}
    (h : es.foldr Reply.Normal.emit (.ret x) = fs.foldr Reply.Normal.emit (.ret y)) :
    es = fs ∧ x = y := by
  induction es generalizing fs with
  | nil =>
    cases fs with
    | nil => exact ⟨rfl, Reply.Normal.ret.inj h⟩
    | cons f fs => cases h
  | cons e es ih =>
    cases fs with
    | nil => cases h
    | cons f fs =>
      obtain ⟨rfl, tail⟩ := Reply.Normal.emit.inj h
      obtain ⟨rfl, rfl⟩ := ih tail
      exact ⟨rfl, rfl⟩

theorem position_result_inj_proof {L : List Sorts} {p q : Position L} {x y : Bool}
    (h : p.result x = q.result y) : p = q ∧ x = y := by
  have pos : p = q := Subtype.ext (congrArg Sigma.fst h)
  subst q
  have payload := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have transport_inj (A : Sorts) (e : Bit = A) : Function.Injective (fun v : value Bit => (e ▸ v : value A)) := by
    cases e
    exact fun _ _ eq => eq
  have bits := transport_inj _ p.2.symm payload
  refine ⟨rfl, ?_⟩
  cases x <;> cases y <;> first | rfl | cases bits

theorem arm_traceTree_inj_proof {L : List Sorts} (p q : ArmNormal L)
    (left : p.traceTree false = q.traceTree false) (right : p.traceTree true = q.traceTree true) :
    p = q := by
  obtain ⟨effects, resultFalse⟩ := emit_path_inj left
  obtain ⟨_, resultTrue⟩ := emit_path_inj right
  obtain ⟨position, whenFalse⟩ := position_result_inj_proof resultFalse
  obtain ⟨_, whenTrue⟩ := position_result_inj_proof resultTrue
  cases p
  cases q
  cases effects
  cases position
  cases whenFalse
  cases whenTrue
  rfl

theorem requestTree_inj_proof {R : Type} {req req' : Bool}
    {l r l' r' : Bool → Reply.Normal R}
    (h : requestTree req l r = requestTree req' l' r') :
    req = req' ∧ (∀ b, l b = l' b) ∧ (∀ b, r b = r' b) := by
  obtain ⟨request, left, right⟩ := Reply.Normal.ask.inj h
  obtain ⟨_, lowLeft, highLeft⟩ := Reply.Normal.ask.inj left
  obtain ⟨_, lowRight, highRight⟩ := Reply.Normal.ask.inj right
  exact ⟨request, fun b => match b with | false => lowLeft | true => highLeft,
    fun b => match b with | false => lowRight | true => highRight⟩

theorem outcomes_injective_proof (L : List Sorts) : Function.Injective (@Normal.outcomes L) := by
  intro p q h
  have tracks : p.traceTree = q.traceTree :=
    Reply.Normal.outcomesWith_injective _ (Exits.Exit.packed_injective L) h
  obtain ⟨request, left, right⟩ := Reply.Normal.ask.inj tracks
  obtain ⟨_, leftFalse, leftTrue⟩ := Reply.Normal.ask.inj left
  obtain ⟨_, rightFalse, rightTrue⟩ := Reply.Normal.ask.inj right
  have lhs := arm_traceTree_inj_proof p.left q.left leftFalse leftTrue
  have rhs := arm_traceTree_inj_proof p.right q.right rightFalse rightTrue
  cases p
  cases q
  cases request
  cases lhs
  cases rhs
  rfl

theorem afterRequest_proof {R A : Type} (success : R → A) (req : Bool)
    (l r : Bool → Reply.Normal R) (right b : Bool) :
    afterPayload req right b ((requestTree req l r).outcomesWith success) =
      ((if right then r else l) b).outcomesWith success := by
  cases right <;> cases b <;>
    simp only [afterPayload, requestTree, Reply.Normal.afterReply_outcomesWith,
      Bool.false_eq_true, ite_false, ite_true]

theorem afterPayload_proof {L : List Sorts} (p : Normal L) (right b : Bool) :
    afterPayload p.request right b p.outcomes =
      ((if right then p.right else p.left).traceTree b).outcomesWith Exits.Exit.packed := by
  cases right <;> exact afterRequest_proof Exits.Exit.packed p.request p.left.traceTree p.right.traceTree _ b

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
