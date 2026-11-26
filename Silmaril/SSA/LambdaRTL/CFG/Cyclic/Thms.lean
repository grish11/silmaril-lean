module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M] [DecidableEq V] [DecidableEq K]

/-- If full-table and suffix lookup agree on every block's outgoing targets,
cyclic and forward execution agree, including on the final store and effects.
The proof uses the iteration fixpoint law. -/
theorem run_eq_forward (model : Model F M α) (graph : CFG V K F)
    (forward : IsForward graph) (store : V → α) :
    Cyclic.run model graph store = graph.run model store :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.run_eq_forward model graph forward store

/-- Transport iteration through a pure encoding of pending transfers and a
separate observation of completed transfers. Both are checked by the step map. -/
theorem iter_project_of_step_encoding {Output Target : Type w} (model : Model F M α)
    (table : List (K × Block V K F)) (project : Transfer V K α → Output)
    (encode : Transfer V K α → Target)
    (targetStep : Target → M (Output ⊕ Target))
    (commutes : ∀ transfer,
      Sum.map project encode <$> step model table transfer = targetStep (encode transfer))
    (initial : Transfer V K α) :
    project <$> iter (step model table) initial = iter targetStep (encode initial) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.iter_project_of_step_encoding model table project encode targetStep
    commutes initial

/-- A pure encoding of transfers transports the observed iteration when it
commutes with every step. For versioning, the encoding must carry the
destination's live-ins and the step equation must cover every edge. -/
theorem iter_obs_of_step_encoding {Target : Type w} (model : Model F M α)
    (table : List (K × Block V K F)) (encode : Transfer V K α → Target)
    (targetStep : Target → M ((K × α) ⊕ Target))
    (commutes : ∀ transfer,
      Sum.map obs encode <$> step model table transfer = targetStep (encode transfer))
    (initial : Transfer V K α) :
    obs <$> iter (step model table) initial = iter targetStep (encode initial) :=
  iter_project_of_step_encoding model table obs encode targetStep commutes initial

end Silmaril.SSA.LambdaRTL.CFG.Cyclic
