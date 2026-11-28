module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Correctness

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K]

theorem arguments_exact (graph : Graph V K F) (checked : graph.check = true)
    {label : K} {block : Phi.Block V K F} (member : (label, block) ∈ graph.blocks)
    {source : Option K} (predecessor : source ∈ graph.predecessors label) :
    block.rows.mapM (fun row => row.incoming.lookup source) = some (arguments source block.rows) := by
  simp only [Graph.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  have keys := (checked.2 (label, block) member).2
  have present (row : Row V K) (mem : row ∈ block.rows) :
      (row.incoming.lookup source).isSome :=
    List.lookup_isSome_iff.mpr (by
      have rowMember : source ∈ row.incoming.map Prod.fst := (keys row mem).symm ▸ predecessor
      obtain ⟨incoming, inRow, key⟩ := List.mem_map.mp rowMember
      exact ⟨incoming, inRow, beq_iff_eq.mpr key.symm⟩)
  clear keys checked member predecessor
  revert present
  induction block.rows with
  | nil => intro _; rfl
  | cons row rows ih =>
      intro present
      have here := present row List.mem_cons_self
      have tail := ih (fun other mem => present other (List.mem_cons_of_mem _ mem))
      cases found : row.incoming.lookup source with
      | none => simp [found] at here
      | some value =>
          simp [List.mapM_cons, arguments, Row.operand, found, tail]

variable [Monad M] [LawfulMonad M]

private theorem update_user (packet : α) (store : V → α) (x : V) (value : α) :
    upd (liftStore packet store) (some x) value = liftStore packet (upd store x value) := by
  funext name
  cases name <;> simp [upd, liftStore]

private theorem update_packet (packet : α) (store : V → α) (value : α) :
    upd (liftStore packet store) none value = liftStore value store := by
  funext name
  cases name <;> simp [upd, liftStore]

omit [DecidableEq V] [DecidableEq K] [Monad M] [LawfulMonad M] in
theorem eval_liftVal (model : Model F M α) (packet : α) (store : V → α) (value : Val V) :
    (liftVal value).eval model (liftStore packet store) = value.eval model store := by
  induction value with
  | var | unit => rfl
  | pair left right ihLeft ihRight => simp [liftVal, Val.eval, ihLeft, ihRight]

omit [DecidableEq V] [DecidableEq K] [LawfulMonad M] in
private theorem eval_liftOp (model : Model F M α) (packet : α) (store : V → α) (op : Op V F) :
    (liftOp op).eval model (liftStore packet store) = op.eval model store := by
  cases op <;> simp [liftOp, Op.eval, eval_liftVal]

omit [DecidableEq K] [LawfulMonad M] in
private theorem liftTerm_exec (model : Model F M α)
    (branchValue : Option K → Val V → Val (Option V))
    (payload : Option K → α → (V → α) → α)
    (agrees : ∀ key value store, (branchValue key value).eval model (liftStore model.unit store) =
      payload key (value.eval model store) store)
    {R : Type w} (jump : Transfer (Option V) (Option K) α → M R)
    (term : Term V (Option K) F) (store : V → α) :
    (liftTerm branchValue term).exec model (fun dest value env => jump (dest, value, env))
        (liftStore model.unit store) =
      term.exec model (fun dest value env => jump (dest, payload dest value env, liftStore model.unit env))
        store := by
  induction term generalizing store with
  | br => simp [liftTerm, Term.exec, agrees]
  | case op x left y right ihLeft ihRight =>
    simp only [liftTerm, Term.exec, eval_liftOp]
    congr 1
    funext payload
    cases payload <;> simp [update_user, ihLeft, ihRight]

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
        store := by
  induction body generalizing store with
  | term term => exact liftTerm_exec model branchValue payload agrees jump term store
  | let1 x op body ih => simp [liftBody, Body.exec, eval_liftOp, update_user, ih]
  | let2 x y op body ih => simp [liftBody, Body.exec, eval_liftOp, update_user, ih]

theorem decode_entry (model : Model F M α) (pairs : model.PairLawful)
    (source : Option K) (rows : List (Row V K)) (snapshot store : V → α)
    (body : Body (Option V) (Option K) F) {R : Type w}
    (jump : Option K → α → (Option V → α) → M R) :
    (decode rows body).exec model jump
        (liftStore ((pack (arguments source rows)).eval model (liftStore model.unit snapshot)) store) =
      body.exec model jump (liftStore model.unit (assign model source snapshot rows store)) := by
  induction rows generalizing store with
  | nil => rfl
  | cons row rows ih =>
      have packet_read (value : α) (env : V → α) : liftStore value env none = value := rfl
      simp only [decode, Body.exec, Op.eval, Val.eval, packet_read, arguments,
        List.map_cons, pack, eval_liftVal, pairs.unpair_pair, pure_bind, assign, update_user,
        update_packet]
      exact ih _

private def next (source target : Option K) (value : α) (store : V → α) : Pending V K α :=
  (target.elim (.returned value) (.jump source), store)

omit [LawfulMonad M] in
private theorem exec_body (model : Model F M α) (graph : Graph V K F) (source : Option K)
    {R : Type w} (jump : Transfer (Option V) (Option K) α → M R)
    (body : Body V (Option K) F) (store : V → α) :
    (lowerBody graph source body).exec model (fun dest value env => jump (dest, value, env))
        (liftStore model.unit store) =
      body.exec model (fun dest value env => jump (lowerPending model graph (next source dest value env)))
        store := by
  let payload := fun (dest : Option K) (value : α) (env : V → α) =>
    dest.elim value (fun key => (edgePacket graph source key).eval model (liftStore model.unit env))
  have provenance (dest : Option K) (value : α) (env : V → α) :
      lowerPending model graph (next source dest value env) =
        (dest, payload dest value env, liftStore model.unit env) := by
    cases dest <;> rfl
  simp only [provenance]
  exact liftBody_exec model _ payload
    (fun dest value env => by cases dest <;> simp [payload, eval_liftVal]) jump body store

omit [DecidableEq K] in
private theorem map_execute (model : Model F M α) (source : Option K)
    (body : Body V (Option K) F) (store : V → α) {R : Type w} (f : Pending V K α → R) :
    f <$> execute model source body store =
      body.exec model (fun dest value env => pure (f (next source dest value env))) store := by
  simp only [execute, ← Body.exec_map, map_pure, next]

omit [DecidableEq V] in
private theorem lookup_lower (graph : Graph V K F) (target : Option K) :
    @List.lookup _ _ (instBEqOfDecidableEq) target (lower graph).blocks =
      target.bind (fun label => (graph.blocks.lookup label).map (lowerBlock graph label)) := by
  unfold lower
  dsimp
  induction graph.blocks with
  | nil => cases target <;> rfl
  | cons item blocks ih =>
      obtain ⟨label, block⟩ := item
      cases target with
      | none => simpa using ih
      | some target =>
          by_cases same : target = label
          · subst label
            simp [lowerBlock]
          · have different : (target == label) = false := by simpa using same
            have differentOption :
                @BEq.beq (Option K) instBEqOfDecidableEq (some target) (some label) = false :=
              by
                change decide ((some target : Option K) = some label) = false
                simp [same]
            simpa [List.lookup_cons, different, differentOption] using ih

private theorem entry_lower (model : Model F M α) (graph : Graph V K F) (input : V → α) :
    lowerPending model graph <$> execute model none graph.entry input =
      enter model (lower graph) (liftStore model.unit input) := by
  rw [map_execute]
  exact (exec_body model graph none pure graph.entry input).symm

private theorem step_lower (model : Model F M α) (pairs : model.PairLawful)
    (graph : Graph V K F) (pending : Pending V K α) :
    Sum.map id (lowerPending model graph) <$> Phi.step model graph pending =
      Sum.map obs id <$> Cyclic.step model (lower graph).blocks (lowerPending model graph pending) := by
  obtain ⟨control, store⟩ := pending
  cases control with
  | returned value =>
      simp [Phi.step, lowerPending, Cyclic.step, lookup_lower, obs]
  | jump source target =>
      cases found : graph.blocks.lookup target with
      | none =>
          simp [Phi.step, lowerPending, Cyclic.step, lookup_lower, found, edgePacket, pack,
            Val.eval, obs]
      | some block =>
          simp only [Phi.step, lowerPending, Cyclic.step, lookup_lower, found, Option.bind_some,
            Option.map_some, lowerBlock]
          rw [update_packet]
          simp only [edgePacket, found, Option.elim_some]
          rw [decode_entry model pairs]
          simp only [Functor.map_map, ← Body.exec_map, map_pure, Sum.map_inr, id_eq]
          rw [map_execute]
          exact (exec_body model graph (some target) (fun t => pure (Sum.inr t))
            block.body (assign model source store block.rows store)).symm

theorem entry_commutes (model : Model F M α) (pairs : model.PairLawful)
    (graph : Graph V K F) (input : V → α) :
    encode model graph <$> execute model none graph.entry input =
      (Versioning.compile (lower graph)).entry.evalJump model (inputEnv model input) := by
  change (Versioning.encode model (lower graph) ∘ lowerPending model graph) <$> _ = _
  rw [comp_map (lowerPending model graph) (Versioning.encode model (lower graph)), entry_lower]
  exact Versioning.entry_commutes model pairs (lower graph) (inputEnv model input)

theorem step_commutes (model : Model F M α) (pairs : model.PairLawful)
    (graph : Graph V K F) (input : V → α) (pending : Pending V K α) :
    Sum.map id (encode model graph) <$> Phi.step model graph pending =
      Cyclic.stepSSA model (Versioning.compile (lower graph)).blocks (inputEnv model input)
        (encode model graph pending) := by
  have left : Sum.map (id : Option K × α → Option K × α) (encode model graph) =
      Sum.map id (Versioning.encode model (lower graph)) ∘ Sum.map id (lowerPending model graph) := by
    funext result
    cases result <;> rfl
  have right : Sum.map (obs : Transfer (Option V) (Option K) α → Option K × α)
      (Versioning.encode model (lower graph)) =
      Sum.map id (Versioning.encode model (lower graph)) ∘ Sum.map obs id := by
    funext result
    cases result <;> rfl
  rw [left, comp_map (Sum.map (id : Option K × α → Option K × α) (lowerPending model graph)),
    step_lower model pairs, Functor.map_map]
  have commutes := Versioning.step_commutes model pairs (lower graph) (inputEnv model input)
    (lowerPending model graph pending)
  rw [right] at commutes
  exact commutes

theorem run_commutes [Iterate M] [LawfulElgotMonad M]
    (model : Model F M α) (pairs : model.PairLawful) (graph : Graph V K F) (input : V → α) :
    Phi.run model graph input =
      Cyclic.runSSA model (Versioning.compile (lower graph)) (inputEnv model input) := by
  let target := Cyclic.stepSSA model (Versioning.compile (lower graph)).blocks (inputEnv model input)
  have comm : (Phi.step model graph >=> liftPure (Sum.map id (encode model graph))) =
      (liftPure (encode model graph) >=> target) := by
    funext pending
    change (Phi.step model graph pending >>= (fun s => pure (Sum.map id (encode model graph) s))) =
      (pure (encode model graph pending) >>= target)
    rw [bind_pure_comp, pure_bind]
    exact step_commutes model pairs graph input pending
  have uniform := LawfulElgotMonad.uniformity (Phi.step model graph) target (encode model graph) comm
  rw [Phi.run, Cyclic.runSSA, ← entry_commutes model pairs graph input, bind_map_left, uniform]
  apply bind_congr
  intro pending
  change (pure (encode model graph pending) >>= iter target) = iter target (encode model graph pending)
  exact pure_bind _ _

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi
