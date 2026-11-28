module

public import Silmaril.Logic.BrookesSC.Concrete.Observation.Defs
import Silmaril.Proofs.Logic.BrookesSC.Concrete.Observation

public section

namespace Silmaril.Logic.BrookesSC.Concrete.Observation

open CategoryTheory Silmaril.Semantics.Brookes

universe u

variable {W : World.{u}} {A B : Type u}

theorem observe_ret_iff (a : A) (s t : Store W) (r : A) :
    observe (Behavior.ret a) s t r ↔ s = t ∧ r = a :=
  Proofs.Logic.BrookesSC.Concrete.Observation.observe_ret a s t r

theorem observe_bind_iff (first : Behavior (Store W) A) (next : A → Behavior (Store W) B)
    (s t : Store W) (r : B) :
    observe (first.bind next) s t r ↔ ∃ m a, observe first s m a ∧ observe (next a) m t r :=
  Proofs.Logic.BrookesSC.Concrete.Observation.observe_bind_iff first next s t r

variable [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread]
variable {S T : Signature W}

theorem observe_eval (M : TraceModel S) (p : Program S A) :
    observe (M.eval p) = (observeModel M).eval p :=
  Proofs.Logic.BrookesSC.Concrete.Observation.observe_eval M p

theorem observe_reduct (f : S ⟶ T) (M : TraceModel T) :
    observeModel (M.reduct f) = (observeModel M).reduct f := rfl

theorem observeModelFunctor_reduct (f : S ⟶ T) :
    Model.reductFunctor (target W) f ⋙ observeModelFunctor S =
      observeModelFunctor T ⋙ Model.reductFunctor (stateTarget W) f := rfl

theorem observe_satisfaction (M : TraceModel S) (e : Sentence S) (h : e.Satisfies M) :
    e.Satisfies (observeModel M) :=
  Proofs.Logic.BrookesSC.Concrete.Observation.observe_satisfaction M e h

end Silmaril.Logic.BrookesSC.Concrete.Observation
