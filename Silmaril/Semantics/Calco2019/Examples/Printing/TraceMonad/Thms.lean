module

public import Silmaril.Semantics.Calco2019.Examples.Printing.TraceMonad.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.TraceMonad

/-! # Kleisli substitution for traces -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing

variable {A X Y : Type u}

instance : LawfulMonad (TraceSet A) := MonadProofs.lawfulTraceSet

instance : LawfulMonad (NonemptyTrace A) := MonadProofs.lawfulNonemptyTrace

@[simp] theorem prepend_nil (t : Trace A X) : prepend [] t = t := MonadProofs.prepend_nil t

theorem prepend_append (w v : List A) (t : Trace A X) :
    prepend (w ++ v) t = prepend w (prepend v t) :=
  MonadProofs.prepend_append w v t

theorem extend_prepend (k : X → TraceSet A Y) (w : List A) (t : Trace A X) :
    extendTrace k (prepend w t) = prepend w '' extendTrace k t :=
  MonadProofs.extend_prepend k w t

theorem bind_prepend (p : TraceSet A X) (k : X → TraceSet A Y) (w : List A) :
    bindTraces (prepend w '' p) k = prepend w '' bindTraces p k :=
  MonadProofs.bind_prepend p k w

theorem traceStep_eq_bind (f : X → TraceSet A (Y ⊕ X)) (g : X → TraceSet A Y) (x : X) :
    traceStep f g x = bindTraces (f x) (Sum.elim pureTrace g) :=
  MonadProofs.traceStep_eq_bind f g x

theorem bind_pureMap (p : TraceSet A X) (h : X → Y) :
    bindTraces p (pureTrace ∘ h) = mapResult h '' p :=
  MonadProofs.bind_pureMap p h

end Silmaril.Calco2019.Examples.Printing
