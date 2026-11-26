module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.PacketCopy
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
    simp only [Simulation.checkBlock, Bool.or_eq_true] at passed
    rcases passed with copied | forwarded
    · cases image with
      | inl index => exact .copy index rfl (of_decide_eq_true copied)
      | inr port => contradiction
    · cases found : PacketCopy.target? {source.param} source.body with
      | none => simp [found] at forwarded
      | some target =>
        exact .forwardCopies target (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.target_iff.mp found)
          (by simpa only [found, decide_eq_true_eq] using forwarded)
  · intro matched
    cases matched with
    | copy index address body => simp [Simulation.checkBlock, address, body]
    | forward target body address =>
      simp [Simulation.checkBlock, body, address, PacketCopy.target?]
    | forwardCopies target copies address =>
      simp [Simulation.checkBlock, Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.target_iff.mpr copies, address]

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

theorem forwardingStep (model : Model F Part α)
    (i : Fin left.locals) (target : Label left.locals b) (packet : α)
    (typed : PacketCopy.Forwards {(left.block i).param} (left.block i).body target) :
    left.step model (.inl i, packet) = Part.some (.inr (target, packet)) := by
  simp [Graph.step, Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.evalJump_packet model (left.block i)
    typed (fun _ => model.unit) packet]

private theorem forwardedRun (sim : Simulation left right) (model : Model F Part α)
    (index : Fin left.locals) (target : Label left.locals b) (packet : α)
    {next : Label left.locals b × α} {result : Fin b × α}
    (advanced : Sum.inr next ∈ left.step model (.inl index, packet))
    (typed : PacketCopy.Forwards {(left.block index).param} (left.block index).body target)
    (address : sim.address index = sim.route target)
    (tail : Silmaril.Elgot.Part.Runs (right.step model) (transfer sim next) result) :
    Silmaril.Elgot.Part.Runs (right.step model) (transfer sim (.inl index, packet)) result := by
  rw [forwardingStep model index target packet typed] at advanced
  have next_eq : next = (target, packet) := by simpa using advanced
  subst next
  change Silmaril.Elgot.Part.Runs (right.step model) (sim.address index, packet) result
  rw [address]
  exact tail

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
        refine forwardedRun sim model index target packet advanced ?_ address ih
        rw [body]
        exact .jump (by simp)
      | forwardCopies target copies address =>
        exact forwardedRun sim model index target packet advanced copies address ih
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

theorem denote_directCopies (model : Model F Part α) (graph : Graph V F a b)
    (exit : Fin graph.locals → Fin b)
    (typed : ∀ i, PacketCopy.Forwards {(graph.block i).param} (graph.block i).body (.inr (exit i)))
    (input : Fin a × α) :
    graph.denote model input = pure (Sum.elim exit id (graph.entry input.1), input.2) := by
  have publicExit (port : Fin b) :
      iter (graph.step model) (.inr port, input.2) = pure (port, input.2) := by
    rw [congrFun (LawfulElgotMonad.fixpoint _) _]
    simp [Graph.step]
  unfold Graph.denote
  cases graph.entry input.1 with
  | inl index =>
    rw [congrFun (LawfulElgotMonad.fixpoint _) _, forwardingStep model index (.inr (exit index)) input.2 (typed index)]
    rw [← Part.pure_eq_some, pure_bind]
    exact publicExit (exit index)
  | inr port => exact publicExit port

theorem directCopies_entry (model : PairModel F Part α) (source : Graph V F a b)
    (exit : Fin source.locals → Fin b)
    (typed : ∀ i, PacketCopy.Forwards {(source.block i).param} (source.block i).body (.inr (exit i)))
    (wire : Fin a → Fin b)
    (included : Refines (Quotient.mk _ source : Arrow V F α a b) (Quotient.mk _ (Graph.wiring wire)))
    (port : Fin a) :
    Sum.elim (fun i => Sum.inr (exit i)) Sum.inr (source.entry port) =
      (Graph.wiring (V := V) (F := F) wire).entry port := by
  have atPort : source.denote model.val (port, model.val.unit) ≤
      (Graph.wiring (V := V) (F := F) wire).denote model.val (port, model.val.unit) :=
    included model (port, model.val.unit)
  rw [denote_directCopies model.val source exit typed, denote_wiring] at atPort
  have equal : (Sum.elim exit id (source.entry port), model.val.unit) = (wire port, model.val.unit) :=
    Part.mem_some_iff.mp (atPort _ (Part.mem_some _))
  refine (show _ = Sum.inr (Sum.elim exit id (source.entry port)) from ?_).trans
    (congrArg (fun result : Fin b × α => Sum.inr result.1) equal)
  cases source.entry port <;> rfl

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation
