module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement.Thms

/-! # Exit continuations for named cyclic refinement

A continuation on observational classes receives the exit label and packet.
It can also use a common external store chosen before plugging. A continuation
on raw mutable graphs may instead receive the final store. Store independence
is the exact condition for that continuation to factor through the observed
transfer, for every incoming store.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement

open Silmaril.Elgot
open Comparison

variable {V K F α β : Type}

/-- An exit handler has the same observation for all carried stores at a fixed
label and packet. -/
def StoreIndependent (next : Transfer V K α → Part β) : Prop :=
  ∀ label packet (left right : V → α), next (label, packet, left) = next (label, packet, right)

/-- Run a store-taking continuation from a chosen external store. -/
def withExternalStore (external : V → α) (next : Transfer V K α → Part β)
    (transfer : K × α) : Part β :=
  next (transfer.1, transfer.2, external)

variable [DecidableEq V] [DecidableEq K]

/-- Plug a continuation after the observation of a mutable class. -/
noncomputable def plugRTL (model : PairModel F Part α) (program : RTLClass V K F Part α)
    (store : V → α) (next : K × α → Part β) : Part β :=
  rtlClassObserve model program store >>= next

/-- Plug a continuation after the observation of a lexical class. -/
noncomputable def plugSSA (model : PairModel F Part α) (program : SSAClass V K F Part α)
    (store : V → α) (next : K × α → Part β) : Part β :=
  ssaClassObserve model program store >>= next

/-- Plug into a raw mutable execution, passing its final store to the continuation. -/
noncomputable def plugRTLWithStore (model : PairModel F Part α) (graph : CFG V K F)
    (store : V → α) (next : Transfer V K α → Part β) : Part β :=
  Cyclic.run model.val graph store >>= next

/-- Start a named mutable continuation table at the incoming label and packet.
The whole table is searched at every jump and a missing label exits. -/
noncomputable def resumeRTL (model : Model F Part α) (table : List (K × Block V K F))
    (transfer : Transfer V K α) : Part (K × α) :=
  obs <$> iter (Cyclic.step model table) transfer

/-- Start a lexical continuation table with a common external environment. -/
noncomputable def resumeSSA (model : Model F Part α) (table : List (K × Block V K F))
    (external : V → α) (transfer : K × α) : Part (K × α) :=
  iter (Cyclic.stepSSA model table external) transfer

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement
