module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K]

/-- An accepted predecessor column is the sequence of successful incoming lookups.
Its length is the number of destination rows. -/
theorem arguments_exact (graph : Graph V K F) (checked : graph.check = true)
    {label : K} {block : Block V K F} (member : (label, block) ∈ graph.blocks)
    {source : Option K} (predecessor : source ∈ graph.predecessors label) :
    block.rows.mapM (fun row => row.incoming.lookup source) = some (arguments source block.rows) :=
  Proofs.SSA.LambdaRTL.CFG.CyclicPhi.arguments_exact graph checked member predecessor

omit [DecidableEq V] in
@[simp] theorem arguments_length (source : Option K) (rows : List (Row V K)) :
    (arguments source rows).length = rows.length := by simp [arguments]

theorem compile_eq_some_iff (graph : Graph V K F) (target : CFG (Option V × Nat) (Option K) F) :
    compile graph = some target ↔ graph.check = true ∧ Versioning.compile (lower graph) = target := by
  simp [compile]

variable [Monad M] [LawfulMonad M]

omit [DecidableEq V] [DecidableEq K] [Monad M] [LawfulMonad M] in
theorem eval_liftVal (model : Model F M α) (packet : α) (store : V → α) (value : Val V) :
    (liftVal value).eval model (liftStore packet store) = value.eval model store :=
  Proofs.SSA.LambdaRTL.CFG.CyclicPhi.eval_liftVal model packet store value

omit [DecidableEq K] [LawfulMonad M] in
theorem liftBody_exec (model : Model F M α)
    (branchValue : Option K → Val V → Val (Option V))
    (payload : Option K → α → (V → α) → α)
    (agrees : ∀ key value store, (branchValue key value).eval model (liftStore model.unit store) =
      payload key (value.eval model store) store)
    {R : Type w} (jump : Transfer (Option V) (Option K) α → M R)
    (body : Body V (Option K) F) (store : V → α) :
    (liftBody branchValue body).exec model (fun dest value env => jump (dest, value, env))
        (liftStore model.unit store) =
      body.exec model (fun dest value env => jump (dest, payload dest value env, liftStore model.unit env))
        store :=
  Proofs.SSA.LambdaRTL.CFG.CyclicPhi.liftBody_exec model branchValue payload agrees jump body store

/-- The λRTL packet decoder performs the simultaneous assignments before the body runs. -/
theorem decode_entry (model : Model F M α) (pairs : model.PairLawful)
    (source : Option K) (rows : List (Row V K)) (snapshot store : V → α)
    (body : Body (Option V) (Option K) F) {R : Type w}
    (jump : Option K → α → (Option V → α) → M R) :
    (decode rows body).exec model jump
        (liftStore ((pack (arguments source rows)).eval model (liftStore model.unit snapshot)) store) =
      body.exec model jump (liftStore model.unit (assign model source snapshot rows store)) :=
  Proofs.SSA.LambdaRTL.CFG.CyclicPhi.decode_entry model pairs source rows snapshot store body jump

variable {graph : Graph V K F} {target : CFG (Option V × Nat) (Option K) F}

/-- Entry yields the same pending transfer after encoding it as a lexical packet. -/
theorem entry_commutes (compiled : compile graph = some target)
    (model : Model F M α) (pairs : model.PairLawful) (input : V → α) :
    encode model graph <$> execute model none graph.entry input =
      target.entry.evalJump model (inputEnv model input) := by
  obtain rfl := ((compile_eq_some_iff graph target).1 compiled).2
  exact Proofs.SSA.LambdaRTL.CFG.CyclicPhi.entry_commutes model pairs graph input

/-- A simultaneous φ entry and its outgoing transfer commute with the actual
cyclic lexical step, preserving both effects and the explicit return. -/
theorem step_commutes (compiled : compile graph = some target)
    (model : Model F M α) (pairs : model.PairLawful) (input : V → α) (pending : Pending V K α) :
    Sum.map id (encode model graph) <$> step model graph pending =
      Cyclic.stepSSA model target.blocks (inputEnv model input) (encode model graph pending) := by
  obtain rfl := ((compile_eq_some_iff graph target).1 compiled).2
  exact Proofs.SSA.LambdaRTL.CFG.CyclicPhi.step_commutes model pairs graph input pending

/-- The checked transpose preserves whole-run complete-Elgot denotation, including
cycles and primitive effects, using the same model on both sides. -/
theorem run_commutes [Iterate M] [LawfulElgotMonad M] (compiled : compile graph = some target)
    (model : Model F M α) (pairs : model.PairLawful) (input : V → α) :
    run model graph input = Cyclic.runSSA model target (inputEnv model input) := by
  obtain rfl := ((compile_eq_some_iff graph target).1 compiled).2
  exact Proofs.SSA.LambdaRTL.CFG.CyclicPhi.run_commutes model pairs graph input

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
