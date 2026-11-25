module

public import Silmaril.SSA.RVSDG.Theta.Defs
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.Theta.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

private theorem map_iterations {X : Type w} {a b : X → Bool → X → Prop}
    (imp : ∀ i p o, a i p o → b i p o) {input output : X} (execution : Iterate a input output) :
    Iterate b input output := by
  induction execution with
  | stop step => exact .stop (imp _ _ _ step)
  | again step _ ih => exact .again (imp _ _ _ step) ih

theorem returns_toGraph (term : Term Op carried sigs) (m : Model.{u, v, w} Op)
    (input output : Tuple m.Val carried) : term.toGraph.Returns m input output ↔
      term.Returns m input output := by
  constructor
  · apply map_iterations
    intro start again finish step
    exact (RVSDG.Term.run_toGraph term.body m start).symm.trans step
  · apply map_iterations
    intro start again finish step
    exact (RVSDG.Term.run_toGraph term.body m start).trans step

private theorem distinct_exit {X : Type w} {body : X → Bool → X → Prop}
    (det : ∀ {i a b x y}, body i a x → body i b y → a = b ∧ x = y)
    {input output : X} (execution : Iterate body input output) (states : Nat → X)
    (each : ∀ n, body (states n) true (states (n + 1))) (n : Nat) (same : states n = input) : False := by
  induction execution generalizing n with
  | stop step =>
    have continuing := each n
    rw [same] at continuing
    cases (det step continuing).1
  | again step _ ih =>
    have continuing := each n
    rw [same] at continuing
    exact ih (n + 1) (det step continuing).2.symm

private theorem bodyResult_injective (m : Model.{u, v, w} Op)
    {a b : Bool} {x y : Tuple m.Val carried} (eq : bodyResult m a x = bodyResult m b y) :
    a = b ∧ x = y := by
  have pred := congrArg (fun ports : Tuple m.Val (BodyResults carried) =>
    ((ports.get .head : ULift (Fin 2))).down.val) eq
  have values : x = y :=
    congrArg (fun ports => match ports with | Tuple.cons _ tail => tail) eq
  refine ⟨?_, values⟩
  cases a <;> cases b
  · rfl
  · exact False.elim (Nat.zero_ne_one pred)
  · exact False.elim (Nat.one_ne_zero pred)
  · rfl

theorem not_diverges_of_returns (graph : Graph Op carried sigs) (m : Model.{u, v, w} Op)
    {input output : Tuple m.Val carried} (execution : graph.Returns m input output) :
    ¬ graph.Diverges m input := by
  rintro ⟨states, first, each⟩
  exact distinct_exit (fun left right => bodyResult_injective m (left.symm.trans right))
    execution states each 0 first

end Silmaril.SSA.RVSDG.Theta.Proofs
