module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Defs
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms
import Silmaril.SSA.LambdaRTL.RoundTrip.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
import Silmaril.SSA.LambdaRTL.CFG.Lexical.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip
open Silmaril.Elgot

universe v w

variable {V W K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

private theorem term_readback (rename : V → W) (term : Term V K F) :
    (renameTerm rename term).toRegion = term.toRegion.rename rename := by
  induction term <;> simp_all [renameTerm, Term.toRegion, Region.rename]

private theorem body_readback (rename : V → W) (body : Body V K F) :
    (renameBody rename body).toRegion = body.toRegion.rename rename := by
  induction body <;> simp_all [renameBody, Body.toRegion, Region.rename, term_readback]

variable [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq W] [DecidableEq K]

omit [DecidableEq W] in
private theorem body_evalObs (model : Model F M α) (body : Body V K F) (store : V → α) :
    body.evalJump model store = body.toRegion.evalObs model store := by
  rw [Body.evalJump, Body.exec_eq_evalRTL, Region.evalObs, map_eq_pure_bind]
  rfl

private theorem body_rename (model : Model F M α) {rename : V → W} {regs : Finset V}
    (injective : Set.InjOn rename regs) (body : Body V K F) (covered : body.toRegion.vars ⊆ regs)
    (store : W → α) :
    (renameBody rename body).evalJump model store = body.evalJump model (store ∘ rename) := by
  rw [body_evalObs, body_readback, body_evalObs]
  exact Region.evalObs_rename_on model injective _ covered (fun _ _ => rfl)

omit [DecidableEq W] [LawfulMonad M] in
/-- A block that reads only its incoming packet is independent of every
register left behind by earlier mutable steps. -/
private theorem block_input (model : Model F M α) (block : Block V K F)
    (closed : block.body.toRegion.fv ⊆ {block.param}) {store input : V → α}
    (same : store block.param = input block.param) :
    block.body.evalJump model store = block.body.evalJump model input := by
  rw [Body.evalJump_eq_evalSSA, Body.evalJump_eq_evalSSA]
  apply Region.evalSSA_congr
  intro reg free
  obtain rfl : reg = block.param := Finset.mem_singleton.mp (closed free)
  exact same

private theorem hit (model : Model F M α) {rename : V → W} {regs : Finset V}
    (injective : Set.InjOn rename regs) (block : Block V K F)
    (covered : block.body.toRegion.vars ⊆ regs) (closed : block.body.toRegion.fv ⊆ {block.param})
    (payload : α) (store : W → α) (input : V → α) :
    (renameBody rename block.body).evalJump model (upd store (rename block.param) payload) =
      block.body.evalJump model (upd input block.param payload) := by
  rw [body_rename model injective _ covered]
  exact block_input model block closed (by simp [upd])

private theorem step_map (model : Model F M α) (mapBlock : Block V K F → Block W K F)
    (table : List (K × Block V K F)) (input : V → α) (label : K) (payload : α) (store : W → α)
    (agrees : ∀ item ∈ table,
      (mapBlock item.2).body.evalJump model (upd store (mapBlock item.2).param payload) =
        item.2.body.evalJump model (upd input item.2.param payload)) :
    Sum.map obs obs <$> Cyclic.step model
      (table.map fun (key, block) => (key, mapBlock block)) (label, payload, store) =
      Cyclic.stepSSA model table input (label, payload) := by
  induction table with
  | nil => simp [Cyclic.step, Cyclic.stepSSA, obs]
  | cons item rest ih =>
    rcases item with ⟨key, block⟩
    by_cases matchKey : label = key
    · subst key
      simp only [List.map_cons, Cyclic.step, Cyclic.stepSSA, List.lookup_cons, beq_self_eq_true]
      rw [← agrees (label, block) List.mem_cons_self, Body.evalJump]
      simp only [Body.exec_eq_evalRTL, map_bind, map_pure, Sum.map_inr, obs]
    · simpa [Cyclic.step, Cyclic.stepSSA, List.lookup_cons, beq_false_of_ne matchKey] using
        ih (fun item member => agrees item (List.mem_cons_of_mem _ member))

omit [DecidableEq W] in
theorem step_packetClosed (model : Model F M α) (table : List (K × Block V K F))
    (closed : PacketClosedTable table) (input : V → α) (transfer : Transfer V K α) :
    Sum.map obs obs <$> Cyclic.step model table transfer =
      Cyclic.stepSSA model table input (obs transfer) := by
  rcases transfer with ⟨label, payload, store⟩
  have square := step_map model id table input label payload store
    (fun item member => block_input model item.2 (closed item member) (by simp [upd]))
  change Sum.map obs obs <$> Cyclic.step model (table.map id) (label, payload, store) = _ at square
  simpa only [List.map_id, obs] using square

theorem step_rename (model : Model F M α) (graph : CFG V K F) {rename : V → W}
    (injective : Set.InjOn rename (support graph))
    (closed : PacketClosed graph) (input : V → α) (transfer : Transfer W K α) :
    Sum.map obs obs <$> Cyclic.step model (renameGraph rename graph).blocks transfer =
      Cyclic.stepSSA model graph.blocks input (obs transfer) := by
  have covered : ∀ item ∈ graph.blocks, item.2.body.toRegion.vars ⊆ support graph := by
    intro item member reg used
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_flatMap.mpr
      ⟨item, member, List.mem_cons_of_mem _ (Finset.mem_toList.mpr used)⟩))
  rcases transfer with ⟨label, payload, store⟩
  exact step_map model (fun block => ⟨rename block.param, renameBody rename block.body⟩)
    graph.blocks input label payload store
    (fun item member => hit model injective item.2 (covered item member) (closed item member) payload store input)

variable [Iterate M] [LawfulElgotMonad M]

theorem run_rename (model : Model F M α) (graph : CFG V K F) {rename : V → W}
    (injective : Set.InjOn rename (support graph)) (closed : PacketClosed graph)
    (input : V → α) (store : W → α)
    (entry_agrees : ∀ reg ∈ graph.entry.toRegion.fv, store (rename reg) = input reg) :
    obs <$> Cyclic.run model (renameGraph rename graph) store =
      Cyclic.runSSA model graph input := by
  have entry : (renameBody rename graph.entry).evalJump model store =
      graph.entry.evalJump model input := by
    rw [body_rename model injective _ (fun _ used => Finset.mem_union_left _ used),
      Body.evalJump_eq_evalSSA, Body.evalJump_eq_evalSSA]
    exact Region.evalSSA_congr model _ entry_agrees
  rw [Cyclic.run, Cyclic.runSSA, ← entry, Body.evalJump]
  simp only [renameGraph, Body.exec_eq_evalRTL, map_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro transfer
  exact iter_obs_of_step_encoding model _ obs _ (step_rename model graph injective closed input) transfer

theorem roundTrip_run_obs [Infinite V] (model : Model F M α) (pairs : model.PairLawful)
    (graph : CFG V K F) (store : V → α) :
    obs <$> Cyclic.run model (Versioning.roundTrip graph) store = obs <$> Cyclic.run model graph store := by
  let rename := Silmaril.SSA.LambdaRTL.RoundTrip.deversion (support (Versioning.compile graph))
  rw [Versioning.roundTrip, deversionGraph, run_rename model _ (deversion_injOn _)
    (fun item member => Region.fv_subset_of_isSSA (Versioning.compile_blocks_areSSA graph item member))
    (store ∘ rename) store (fun _ _ => rfl)]
  simpa [rename, Function.comp_def] using
    (Versioning.run_commutes model pairs graph (store ∘ rename)).symm

theorem runSSA_deversion_reversion [Infinite V] (model : Model F M α) (pairs : model.PairLawful)
    (graph : CFG (V × Nat) K F) (closed : PacketClosed graph)
    (entry_zero : ∀ reg ∈ graph.entry.toRegion.fv, reg.2 = 0) (input : V × Nat → α) :
    Cyclic.runSSA model (Versioning.compile (deversionGraph graph)) input =
      Cyclic.runSSA model graph input := by
  rw [← Versioning.run_commutes model pairs, deversionGraph]
  apply run_rename model graph (deversion_injOn _) closed
  rintro ⟨reg, version⟩ used
  have zero := entry_zero (reg, version) used
  change version = 0 at zero
  subst version
  simp

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip
