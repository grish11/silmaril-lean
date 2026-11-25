module

import Silmaril.Logic.Temporal.TLA.Kernel.Thms

/-! Hand-built semantic fixtures for the bounded graphs in
`tests/semantics/tla-quint/oracle.json`. -/

namespace Silmaril.Logic.Temporal.TLA.Kernel

private abbrev intScope (count : Nat) : Scope where
  rigid _ := Empty
  flex
    | .int => Fin count
    | .bool => Empty

private def noRigid {count : Nat} : RigidEnv (intScope count) :=
  fun _ name => nomatch name

private def intState {count : Nat} (values : Fin count → Int) : State (intScope count)
  | .int, name => values name
  | .bool, name => nomatch name

namespace BoundedCounter

private def n : StateExpr (intScope 1) Int := Term.flex (a := .int) 0

private def domain : Bounded (intScope 1) Int :=
  ⟨[0, 1, 2], fun value => intState fun _ => value⟩

private def init : StatePredicate (intScope 1) := Predicate.eq n (Term.literal 0)

private def step : StepPredicate (intScope 1) :=
  (Predicate.lt n (Term.literal 2)).current.and
    (Predicate.eq n.next (n.current.add (Term.literal 1)))

example : domain.initials noRigid init = [0] := by decide

example : domain.transitions noRigid step = [(0, 1), (1, 2)] := by decide

example (t : State (intScope 1)) : ¬ step.toAction noRigid (domain.valuation 2) t :=
  fun h => (by decide : ¬ (2 : Int) < 2) h.1

-- This projection observes the entire single-variable state.
example (s t : State (intScope 1)) :
    (step.bracket n).toAction noRigid s t ↔ step.toAction noRigid s t ∨ s = t := by
  apply step.bracket_full
  intro s t equal
  funext sort name
  cases sort with
  | int =>
    have same : name = 0 := Subsingleton.elim _ _
    subst name
    exact equal
  | bool => exact nomatch name

example : domain.transitions noRigid (step.bracket n) =
    [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2)] := by decide

-- The graph's finite domain does not restrict the action's integer carriers.
example : step.check noRigid (domain.valuation (-1), domain.valuation 0) = true := by decide

private def belowBound : StatePredicate (intScope 1) :=
  let upper := n.mul (Term.literal 2)
  let bound := Term.rigid (a := .int) ((intScope 1).rigid.fresh .int)
  Predicate.forallIn (a := .int) (Term.enumeration [n, n.add (Term.literal 1)])
    (Predicate.lt bound (upper.weakenRigid .int))

example : belowBound.check noRigid (domain.valuation 2) = true := by decide

example : belowBound.check noRigid (domain.valuation 1) = false := by decide

private def emptyBound : StatePredicate (intScope 1) :=
  Predicate.existsIn (a := .int) (Term.enumeration [])
    ((Predicate.eq n n).weakenRigid .int)

example : emptyBound.check noRigid (domain.valuation 0) = false := by decide

end BoundedCounter

namespace BitPair

private def domain : Bounded (intScope 2) (Int × Int) :=
  ⟨[(0, 0), (0, 1), (1, 0), (1, 1)],
    fun (x, y) => intState fun i => if i = 0 then x else y⟩

private def x : StateExpr (intScope 2) Int := Term.flex (a := .int) 0
private def y : StateExpr (intScope 2) Int := Term.flex (a := .int) 1

private def init : StatePredicate (intScope 2) :=
  (Predicate.eq x (Term.literal 0)).and (Predicate.eq y (Term.literal 1))

private def step : StepPredicate (intScope 2) :=
  let flip := Term.rigid (a := .bool) ((intScope 2).rigid.fresh .bool)
  let oldX := x.current.weakenRigid .bool
  let newX := Predicate.eq (x.next.weakenRigid .bool) (y.current.weakenRigid .bool)
  let newY := Predicate.eq (y.next.weakenRigid .bool)
    (Term.ite (Predicate.ofBool flip) ((Term.literal 1).sub oldX) oldX)
  Predicate.existsIn (a := .bool) (Term.literal [false, true]) (newX.and newY)

example : domain.initials noRigid init = [(0, 1)] := by decide

example : domain.transitions noRigid step =
    [((0, 0), (0, 0)), ((0, 0), (0, 1)),
     ((0, 1), (1, 0)), ((0, 1), (1, 1)),
     ((1, 0), (0, 0)), ((1, 0), (0, 1)),
     ((1, 1), (1, 0)), ((1, 1), (1, 1))] := by decide

-- A constraint on x' leaves y' free.
example : (Predicate.eq x.next y.current).check noRigid
    (domain.valuation (1, 0), domain.valuation (0, 1)) = true := by decide

end BitPair
end Silmaril.Logic.Temporal.TLA.Kernel
