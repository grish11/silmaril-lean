module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree

open Category.FiniteIteration.Syntax (emptyBindings)

private def ub : Tree := .stop .ub
private def delayedUB : Tree := .ask .ask ub ub
private def stopped : Prefix 0 := .stop none
private def faulted : Prefix 0 := .stop (some .ask)

example : Shape.denote ub.region stopped.handler.model 0 = ⊤ :=
  finite_observe ub stopped.handler emptyBindings 0

example : Shape.denote delayedUB.region stopped.handler.model 0 =
    WithTop.some {Outcome.diverge} :=
  finite_observe delayedUB stopped.handler emptyBindings 0

example : Shape.denote delayedUB.region faulted.handler.model 0 =
    WithTop.some {Outcome.fault (0 : Fin 1)} :=
  finite_observe delayedUB faulted.handler emptyBindings 0

example : Shape.denote delayedUB.region (Prefix.step .ask 0 stopped).handler.model 0 = ⊤ :=
  finite_observe delayedUB (Prefix.step .ask 0 stopped).handler emptyBindings 0

example : ¬ Overlay.Refines.{0,0,0,0} (ub.region (Γ := [])) (delayedUB.region (Γ := [])) :=
  fun h => (raw_refines_iff ub delayedUB).mp h

private def done : Tree := .stop (.ret 1)
private def pending : Tree := .ask .other done done

/-- The right branch of the second request is reached only after the same
key replies left and then right at distinct states. Its continuation may
stop immediately or still have a request to run. -/
private def repeated (tail : Tree) : Tree := .ask .ask (.ask .ask ub tail) ub

private def unequal : Prefix 2 := .step .ask 0 (.step .ask 1 (.stop (some .other)))

example : Shape.denote (repeated done).region unequal.handler.model 0 =
    WithTop.some {Outcome.ret (1 : Fin 2) Value.unit (2 : Fin 3)} :=
  finite_observe (repeated done) unequal.handler emptyBindings 0

example : Shape.denote (repeated pending).region unequal.handler.model 0 =
    WithTop.some {Outcome.fault (2 : Fin 3)} :=
  finite_observe (repeated pending) unequal.handler emptyBindings 0

example : ¬ Shape.denote (repeated done).region unequal.handler.model 0 ≤
    Shape.denote (repeated pending).region unequal.handler.model 0 := by
  rw [finite_observe _ _ emptyBindings 0, finite_observe _ _ emptyBindings 0, TwoRequest.result_order]
  decide

private def prependLeft : Nat → Tree → Tree
  | 0, tail => tail
  | n + 1, tail => .ask .ask (prependLeft n tail) ub

private theorem prependLeft_fails (n : Nat) (p q : Tree) (bad : ¬ p.Refines q) :
    ¬ (prependLeft n p).Refines (prependLeft n q) := by
  induction n with
  | zero => exact bad
  | succ n ih => exact fun le => ih le.2.1

example (n : Nat) :
    ∃ (k : Nat) (probe : Prefix k),
      k ≤ min (prependLeft n done).depth (prependLeft n pending).depth ∧
        ¬ Shape.denote (prependLeft n done).region probe.handler.model 0 ≤
          Shape.denote (prependLeft n pending).region probe.handler.model 0 :=
  exists_prefix_countermodel (prependLeft_fails n done pending id)

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree.raw_refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_refines_iff

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree
