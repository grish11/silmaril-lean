module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs
import Silmaril.SSA.LambdaRTL.CFG.Lexical.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison

variable {V F α : Type} [DecidableEq V] {a b n : Nat}

private theorem checkBlock_iff [DecidableEq F] (right : Graph V F a b)
    (route : Label n b → Label right.locals b) (source : Block V (Label n b) F)
    (image : Label right.locals b) :
    Simulation.checkBlock right route source image = true ↔ BlockMatch right route source image := by
  constructor
  · intro passed
    simp only [Simulation.checkBlock, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at passed
    rcases passed with copied | ⟨target, _, body, address⟩
    · cases image with
      | inl index => exact .copy index rfl (of_decide_eq_true copied)
      | inr port => contradiction
    · exact .forward target body address
  · intro matched
    cases matched with
    | copy index address body => simp [Simulation.checkBlock, address, body]
    | forward target body address =>
      simp [Simulation.checkBlock, body, address, Body.targets, Term.targets]

theorem check_iff [DecidableEq F] (left right : Graph V F a b)
    (address : Fin left.locals → Label right.locals b) :
    Simulation.check left right address = true ↔
      (∀ port, Sum.elim address Sum.inr (left.entry port) = right.entry port) ∧
      (∀ i, BlockMatch right (Sum.elim address Sum.inr) (left.block i) (address i)) := by
  simp [Simulation.check, Bool.and_eq_true, List.all_eq_true, checkBlock_iff]

variable {left right : Graph V F a b}

private def transfer (sim : Simulation left right) :
    Label left.locals b × α → Label right.locals b × α :=
  Prod.map sim.route id

private theorem copiedStep (sim : Simulation left right) (model : Model F Part α)
    (i : Fin left.locals) (j : Fin right.locals) (packet : α)
    (address : sim.address i = .inl j)
    (body : (left.block i).relabel sim.route = right.block j) :
    Sum.map id (transfer sim) <$> left.step model (.inl i, packet) =
      right.step model (transfer sim (.inl i, packet)) := by
  simp only [transfer, Prod.map_apply, Simulation.route, Sum.elim_inl, address, id_eq, Graph.step]
  rw [← body]
  simp only [Block.relabel, Body.evalJump_relabel, Functor.map_map]
  rfl

private theorem forwardingStep (model : Model F Part α)
    (i : Fin left.locals) (target : Label left.locals b) (packet : α)
    (body : (left.block i).body = .term (.br target (.var (left.block i).param))) :
    left.step model (.inl i, packet) = Part.some (.inr (target, packet)) := by
  simp [Graph.step, body, Body.evalJump, Body.exec, Term.exec, Val.eval, upd]

private theorem runs (sim : Simulation left right) (model : Model F Part α)
    {start : Label left.locals b × α} {result : Fin b × α}
    (finished : Silmaril.Elgot.Part.Runs (left.step model) start result) :
    Silmaril.Elgot.Part.Runs (right.step model) (transfer sim start) result := by
  induction finished with
  | @done start result returned =>
    rcases start with ⟨index | port, packet⟩
    · simp [Graph.step, Part.mem_map_iff] at returned
    · apply Silmaril.Elgot.Part.Runs.done
      simpa [Graph.step, transfer, Simulation.route, Sum.elim_inr] using returned
  | @more start next result advanced _ ih =>
    rcases start with ⟨index | port, packet⟩
    · cases sim.block index with
      | copy target address body =>
        exact .more (copiedStep sim model index target packet address body ▸
          Part.mem_map (Sum.map id (transfer sim)) advanced) ih
      | forward target body address =>
        rw [forwardingStep model index target packet body] at advanced
        have next_eq : next = (target, packet) := by simpa using advanced
        subst next
        change Silmaril.Elgot.Part.Runs (right.step model) (sim.address index, packet) result
        rw [address]
        exact ih
    · simp [Graph.step] at advanced

theorem denote_le (sim : Simulation left right) (model : Model F Part α) (input : Fin a × α) :
    left.denote model input ≤ right.denote model input := by
  intro result member
  apply (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
  have target := runs sim model ((Silmaril.Elgot.Part.mem_iter_iff _ _ result).mp member)
  change Silmaril.Elgot.Part.Runs (right.step model) (sim.route (left.entry input.1), input.2) result at target
  rwa [Simulation.route, sim.entry input.1] at target

theorem denote_wiring (model : Model F Part α) (wire : Fin a → Fin b) (input : Fin a × α) :
    (Graph.wiring (V := V) (F := F) wire).denote model input = pure (wire input.1, input.2) := by
  unfold Graph.denote
  rw [congrFun (LawfulElgotMonad.fixpoint _) _]
  simp [Graph.wiring, Graph.step]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation
