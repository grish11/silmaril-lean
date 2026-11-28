module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Proofs

open CategoryTheory
open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.Ordered (Block Cfg runBlock)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution (pullInput pullInput_get reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open TwoAddress.Institution (liftAddresses mapGraph pull_operands)
open TwoAddress.MemRef (decodeAddresses headerTypes Runtime)
open Loop.MLIR.MemRef (runActivation lowerActivation_run)

variable {P Q : EntrySignature} {cells : Nat} {next last : List ValueSort}

set_option backward.isDefEq.respectTransparency false

private theorem run_congr {Left Right : List Width → List Width → Type}
    {Label : List Width → Type} {result : List Width}
    (left : Cfg Left Label [] result) (right : Cfg Right Label [] result)
    (evalLeft : ∀ {ins outs}, Left ins outs → Env ins → Runtime cells (Env outs))
    (evalRight : ∀ {ins outs}, Right ins outs → Env ins → Runtime cells (Env outs))
    (entries : Block.eval evalLeft left.entry .nil = Block.eval evalRight right.entry .nil)
    (blocks : ∀ {args} (label : Label args) (env : Env (args ++ [])),
      Block.eval evalLeft (left.block label) env = Block.eval evalRight (right.block label) env)
    (fuel : Nat) : left.run evalLeft fuel .nil = right.run evalRight fuel .nil := by
  have run {scope : List Width} (a : Block Left Label scope result) (b : Block Right Label scope result)
      (env : Env scope) (step : Block.eval evalLeft a env = Block.eval evalRight b env) :
      runBlock left.block (Block.eval evalLeft) .nil fuel a env =
        runBlock right.block (Block.eval evalRight) .nil fuel b env := by
    induction fuel generalizing scope with
    | zero => rfl
    | succ fuel ih =>
      simp only [runBlock, step]
      congr 1
      funext nextFrame
      cases nextFrame with
      | inl frame => exact ih _ _ _ (blocks frame.label (frame.args.append .nil))
      | inr values => rfl
  exact run left.entry right.entry .nil entries

private theorem entry_eval_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q) (env : Env []) :
    TwoAddress.MemRef.evalBody model.input (.entry (mapGraph h graph).entryFirst (mapGraph h graph).entrySecond) env =
      TwoAddress.MemRef.evalBody (reduct h model).input (.entry graph.entryFirst graph.entrySecond) env := by
  simp only [mapGraph, TwoAddress.MemRef.evalBody, reduct, pullInput_get]

private theorem activation_run_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (first second : Address model.cells) (initial : Buffer model.cells) :
    Loop.MLIR.MemRef.runActivation (mapGraph h graph).activation (.cons first (.cons second model.input)) initial =
      Loop.MLIR.MemRef.runActivation graph.activation (.cons first (.cons second (reduct h model).input)) initial := by
  let header : Header model.cells := ⟨first, second, initial.cell⟩
  change runActivation (Loop.Institution.mapGraph (liftAddresses h) graph.activation)
      (header.operands model.input) initial =
    runActivation graph.activation (header.operands (reduct h model).input) initial
  rw [← pull_operands h model header, lowerActivation_run, lowerActivation_run]
  have body : (Loop.Institution.mapGraph (liftAddresses h) graph.activation).body.denote
        (header.operands model.input) initial.cell =
      graph.activation.body.denote (pullInput (liftAddresses h).port (header.operands model.input)) initial.cell :=
    Memory.Diamond.Institution.denote_mapBody (liftAddresses h).port
      graph.activation.body (header.operands model.input) PUnit.unit initial.cell
  have stop : (Loop.Institution.mapGraph (liftAddresses h) graph.activation).stopWord (header.operands model.input) =
      graph.activation.stopWord (pullInput (liftAddresses h).port (header.operands model.input)) :=
    (pullInput_get (liftAddresses h).port (header.operands model.input) graph.activation.stop).symm
  rw [body, stop]

private theorem activation_eval_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (env : Env (headerTypes model.cells)) :
    TwoAddress.MemRef.evalBody model.input
        (.activation (Loop.MLIR.MemRef.lowerActivation model.cells (mapGraph h graph).activation)
          (mapGraph h graph).feedbackFirst (mapGraph h graph).feedbackSecond) env =
      TwoAddress.MemRef.evalBody (reduct h model).input
        (.activation (Loop.MLIR.MemRef.lowerActivation model.cells graph.activation)
          graph.feedbackFirst graph.feedbackSecond) env := by
  funext initial
  cases decoded : decodeAddresses env with
  | none => simp [TwoAddress.MemRef.evalBody, decoded, Bind.bind]
  | some pair =>
    obtain ⟨first, second⟩ := pair
    have code := activation_run_map h graph model first second initial
    have pulled :
        pullInput (liftAddresses h).port (.cons first (.cons second model.input)) =
          .cons first (.cons second (reduct h model).input) :=
      pull_operands h model ⟨first, second, initial.cell⟩
    unfold Loop.MLIR.MemRef.runActivation at code
    simp only [TwoAddress.MemRef.evalBody, decoded, Bind.bind, Option.bind_some, code]
    simp only [mapGraph]
    rw [← pullInput_get (EntrySignature.Hom.port (liftAddresses h))
      (.cons first (.cons second model.input)) graph.feedbackFirst,
      ← pullInput_get (EntrySignature.Hom.port (liftAddresses h))
      (.cons first (.cons second model.input)) graph.feedbackSecond, pulled]
    rfl

private theorem lower_run_map (h : P ⟶ Q) (first : Graph P.args) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring P.args next) (g : Boundary.Wiring next last) (model : EntryModel Q) (fuel : Nat) :
    (lower model.cells (mapGraph h first) second third).run
        (evalBody (f.map (EntrySignature.Hom.port h)) g model.input) fuel .nil =
      (lower model.cells first second third).run (evalBody f g (reduct h model).input) fuel .nil := by
  apply run_congr
  · simp only [lower, pairBlock, Linked.MemRef.lower, Linked.MemRef.firstBlock, TwoAddress.MemRef.lower,
      Block.eval, evalBody, Linked.MemRef.evalBody, entry_eval_map]
  · intro args label env
    cases label with
    | pair label =>
      cases label with
      | first label =>
        cases label with
        | header =>
          simp only [lower, pairBlock, Linked.MemRef.lower, Linked.MemRef.firstBlock, TwoAddress.MemRef.lower,
            Block.eval, evalBody, Linked.MemRef.evalBody, activation_eval_map]
        | exit => rfl
      | secondEntry =>
        cases env with
        | cons word rest =>
          simp only [lower, pairBlock, Linked.MemRef.lower, Linked.MemRef.secondBlock, TwoAddress.MemRef.lower,
            Block.eval, evalBody, Linked.MemRef.evalBody, Boundary.Wiring.select_map, reduct]
          rfl
      | second label =>
        cases label <;> cases env with
        | cons word rest =>
          simp only [lower, pairBlock, Linked.MemRef.lower, Linked.MemRef.secondBlock, TwoAddress.MemRef.lower,
            Block.eval, evalBody, Linked.MemRef.evalBody, Boundary.Wiring.select_map, reduct]
          rfl
    | thirdEntry =>
      cases env with
      | cons a rest =>
        cases rest with
        | cons b rest =>
          simp only [lower, thirdBlock, TwoAddress.MemRef.lower,
            Block.eval, evalBody, selectThird, Boundary.Wiring.select_map, reduct]
    | third label =>
      cases label <;> cases env with
      | cons a rest =>
        cases rest with
        | cons b rest =>
          simp only [lower, thirdBlock, TwoAddress.MemRef.lower,
            Block.eval, evalBody, selectThird, Boundary.Wiring.select_map, reduct]
          rfl

theorem runFuel_map (h : P ⟶ Q) (first : Graph P.args) (second : Graph next) (third : Graph last)
    (f : Boundary.Wiring P.args next) (g : Boundary.Wiring next last)
    (model : EntryModel Q) (fuel : Nat) (initial : Buffer model.cells) :
    runFuel (mapGraph h first) second third (f.map (EntrySignature.Hom.port h)) g model.input fuel initial =
      runFuel first second third f g (reduct h model).input fuel initial := by
  unfold runFuel
  rw [lower_run_map h first second third f g model fuel]
  rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Proofs
