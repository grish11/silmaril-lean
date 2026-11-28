module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Correctness

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block arguments pack liftStore assign
  inputEnv eval_liftVal liftBody_exec decode_entry)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K] [Monad M] [LawfulMonad M]

private def payload (model : Model F M α) (graph : Graph V K F)
    (pred target : Option K) (value : α) (store : V → α) : α :=
  (lookup graph target).elim value (fun block =>
    (pack (arguments pred block.rows)).eval model (liftStore model.unit store))

private def encode (model : Model F M α) (graph : Graph V K F)
    (pending : Pending V K α) : Transfer (Option V) (Option K) α :=
  let (pred, target, value, store) := pending
  (target, payload model graph pred target value store, liftStore model.unit store)

omit [LawfulMonad M] in
private theorem exec_lower (model : Model F M α) (graph : Graph V K F) (pred : Option K)
    {R : Type w} (next : Transfer (Option V) (Option K) α → M R)
    (body : Body V (Option K) F) (store : V → α) :
    (Phi.liftBody (branchValue graph pred) body).exec model (fun t a s => next (t, a, s))
        (liftStore model.unit store) =
      body.exec model (fun t a s => next (encode model graph (pred, t, a, s))) store :=
  liftBody_exec model (branchValue graph pred) (payload model graph pred)
    (fun key value env => by simp [branchValue, payload]; cases lookup graph key <;> simp [eval_liftVal])
    next body store

omit [DecidableEq V] [Monad M] [LawfulMonad M] in
private theorem lower_lookup (graph : Graph V K F) (target : Option K) :
    @List.lookup _ _ instBEqOfDecidableEq target (lower graph).blocks =
      target.bind (fun k => (graph.blocks.lookup k).map (lowerBlock graph k)) := by
  unfold lower
  dsimp
  induction graph.blocks with
  | nil => cases target <;> rfl
  | cons item blocks ih =>
    rcases item with ⟨key, block⟩
    cases target with
    | none => simpa using ih
    | some target =>
      by_cases same : target = key
      · subst key
        simp
      · have other : (target == key) = false := by simpa using same
        have otherOption : @BEq.beq (Option K) instBEqOfDecidableEq (some target) (some key) = false := by
          change decide ((some target : Option K) = some key) = false
          simp [same]
        simpa [List.lookup_cons, other, otherOption] using ih

private theorem step_lower (model : Model F M α) (pairs : model.PairLawful)
    (graph : Graph V K F) (pending : Pending V K α) :
    Sum.map id (encode model graph) <$> Phi.OrderedExits.step model graph pending =
      Sum.map obs id <$> Cyclic.step model (lower graph).blocks (encode model graph pending) := by
  obtain ⟨pred, target, value, store⟩ := pending
  cases target with
  | none => simp [Phi.OrderedExits.step, lookup, encode, payload, Cyclic.step, lower_lookup, obs]
  | some key =>
    cases found : graph.blocks.lookup key with
    | none =>
      simp [Phi.OrderedExits.step, lookup, encode, payload, Cyclic.step, lower_lookup, found, obs]
    | some block =>
      have packetStore (a : α) :
          upd (liftStore model.unit store) none a = liftStore a store := by
        funext name
        cases name <;> simp [liftStore, upd]
      simp only [Phi.OrderedExits.step, lookup, Option.bind_some, found, encode, payload, Option.elim_some,
        Cyclic.step, lower_lookup, Option.map_some, lowerBlock]
      rw [packetStore, decode_entry model pairs]
      simp only [← Body.exec_map, map_pure, Sum.map_inr, id_eq, execute]
      exact (exec_lower model graph (some key)
        (fun t => pure (Sum.inr t : (Option K × α) ⊕ Transfer (Option V) (Option K) α)) block.body
        (assign model pred store block.rows store)).symm

private theorem run_lower [Iterate M] [LawfulElgotMonad M]
    (model : Model F M α) (pairs : model.PairLawful) (graph : Graph V K F) (input : V → α) :
    Phi.OrderedExits.run model graph input =
      obs <$> Cyclic.run model (lower graph) (liftStore model.unit input) := by
  let target := fun p => Sum.map obs id <$> Cyclic.step model (lower graph).blocks p
  have comm : (Phi.OrderedExits.step model graph >=> liftPure (Sum.map id (encode model graph))) =
      (liftPure (encode model graph) >=> target) := by
    funext p
    change (Phi.OrderedExits.step model graph p >>= fun s => pure (Sum.map id (encode model graph) s)) =
      (pure (encode model graph p) >>= target)
    rw [bind_pure_comp, pure_bind]
    exact step_lower model pairs graph p
  have uniform := LawfulElgotMonad.uniformity (Phi.OrderedExits.step model graph) target (encode model graph) comm
  have projected (p : Transfer (Option V) (Option K) α) :
      obs <$> iter (Cyclic.step model (lower graph).blocks) p = iter target p :=
    Cyclic.iter_obs_of_step_encoding model (lower graph).blocks id target
      (by intro t; exact congrArg (fun f => f <$> Cyclic.step model (lower graph).blocks t)
            (funext fun s => by cases s <;> rfl)) p
  rw [Phi.OrderedExits.run, Cyclic.run, ← Body.exec_map]
  change (_ >>= _) = (Phi.liftBody (branchValue graph none) graph.entry).exec model _ _
  rw [exec_lower model graph none (fun p => obs <$> iter (Cyclic.step model (lower graph).blocks) p)]
  simp only [execute, CFG.Body.exec_eq_evalRTL, bind_assoc, pure_bind, projected]
  apply bind_congr
  intro p
  rw [uniform]
  exact pure_bind _ _

theorem run_commutes [Iterate M] [LawfulElgotMonad M]
    (model : Model F M α) (pairs : model.PairLawful) (graph : Graph V K F) (input : V → α) :
    Phi.OrderedExits.run model graph input =
      Cyclic.runSSA model (Versioning.compile (lower graph)) (inputEnv model input) :=
  (run_lower model pairs graph input).trans
    (Versioning.run_commutes model pairs (lower graph) (inputEnv model input))

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits
