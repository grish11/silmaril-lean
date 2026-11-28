module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Proofs

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.MLIR.Finite (Profile evalOp)
open Memory.Diamond.MLIR.Finite renaming encodeResult → encodeCFResult
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (runtimePort)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.CF.Ordered (Block)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open RVSDG.NestedTheta.Partial (observe_ofRuntime_eq_some_iff_returns)
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)

variable {P : EntrySignature}

theorem mlir_observation_iff_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      Part.some (.returned (encodeCFResult (Profile.ofCells model.cells) word final)) ↔
      ∃ fuel, (MLIR.lower (Profile.ofCells model.cells) graph).run evalOp fuel
        (MLIR.encodeEntry (Profile.ofCells model.cells) model.input initial) =
          some (encodeCFResult (Profile.ofCells model.cells) word final) := by
  unfold MLIR.Institution.observe
  dsimp only
  erw [Cfg.denotePart_eq_some_iff]
  simp only [Cfg.embed_run, Option.map_eq_some_iff, Outcome.returned.injEq]
  constructor
  · rintro ⟨fuel, output, run, rfl⟩
    exact ⟨fuel, run⟩
  · rintro ⟨fuel, run⟩
    exact ⟨fuel, _, run, rfl⟩

theorem mlir_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial = Part.none ↔ graph.denote model.input initial = Part.none := by
  unfold MLIR.Institution.observe
  erw [Cfg.denotePart_eq_none_iff, Cfg.embed_diverges_iff,
    MLIR.lower_diverges_iff (Profile.ofCells model.cells) graph model.input initial]
  exact Part.eq_none_iff'.symm

theorem mlir_observation_eq_map_theta (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      (thetaObservation graph model initial).map (fun result =>
        Outcome.returned (encodeCFResult (Profile.ofCells model.cells)
          (result.get .head) (result.get (.tail .head)))) := by
  erw [MLIR.Institution.observe_eq graph model initial, theta_observation graph model initial, Part.map_map]
  rfl

theorem memref_run_iff_theta_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    (∃ fuel, (MLIR.MemRef.CF.lower model.cells graph).run (MLIR.MemRef.CF.evalBody model.input)
      fuel .nil ⟨initial⟩ = (some (.cons word .nil), ⟨final⟩)) ↔
    ∃ fuel, graph.lowerTheta.run (thetaRuntime model.cells) fuel (Memory.encodeInput initial model.input) =
      some (Memory.encodeResult word final) := by
  constructor
  · rintro ⟨fuel, emitted⟩
    obtain ⟨count, _, native⟩ :=
      (MLIR.MemRef.CF.cfg_run_eq_some_iff_returnsAfter graph model.input fuel initial word final).mp emitted
    exact ⟨count + 1, ((graph.lowerTheta_returnsAfter_iff model.input initial count word final).mp native).2⟩
  · intro emitted
    obtain ⟨count, native⟩ := (graph.lowerTheta_returns_iff model.input initial word final).mpr emitted
    exact ⟨count + 3, (MLIR.MemRef.CF.cfg_run_eq_some_iff_returnsAfter
      graph model.input (count + 3) initial word final).mpr ⟨count, Nat.le_refl _, native⟩⟩

theorem petri_no_completion_iff_theta (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    (∀ output, ¬ Finishes (thetaRuntime model.cells) graph.lowerTheta
      (Memory.encodeInput initial model.input) output) ↔ thetaObservation graph model initial = Part.none := by
  rw [Part.eq_none_iff]
  exact forall_congr' fun output => not_congr
    ((finishes_iff _ _ _ output).trans ((observe_ofRuntime_eq_some_iff_returns _ _ _ output).symm.trans
      Part.eq_some_iff))

section Activation

variable {args : List ValueSort} {cells : Nat}

private theorem readHeap (input : Tuple (Val cells) args) (heap : Heap cells) :
    (Memory.encodeInput heap input).get (runtimePort (dataPorts args)) = heap := by
  induction input with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem activationTuple_eq (input : Tuple (Val cells) args) (a b : Heap cells)
    (x y : ULift (Fin 2)) :
    Tuple.cons (F := WireVal cells) (t := .control 2) x (Memory.encodeInput a input) =
      Tuple.cons (F := WireVal cells) (t := .control 2) y (Memory.encodeInput b input) ↔
        x = y ∧ a = b := by
  constructor
  · intro same
    have tags := congrArg (fun xs => xs.get .head) same
    have heaps := congrArg (fun xs => xs.get (.tail (runtimePort (dataPorts args)))) same
    change (Memory.encodeInput a input).get (runtimePort (dataPorts args)) =
      (Memory.encodeInput b input).get (runtimePort (dataPorts args)) at heaps
    rw [readHeap, readHeap] at heaps
    exact ⟨tags, heaps⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem successor_eq (x y : Frame MLIR.MemRef.CF.Label) (a b : Heap cells) :
    ((Sum.inl x : Frame MLIR.MemRef.CF.Label ⊕ Env MLIR.MemRef.CF.resultTypes), Buffer.mk a) =
      (.inl y, Buffer.mk b) ↔ x = y ∧ a = b := by
  constructor
  · intro same
    exact ⟨Sum.inl.inj (congrArg Prod.fst same), congrArg (fun result => result.2.cell) same⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem distinctFrames (word : Word) :
    (⟨MLIR.MemRef.CF.Label.header, .nil⟩ : Frame MLIR.MemRef.CF.Label) ≠
      ⟨MLIR.MemRef.CF.Label.exit, .cons word .nil⟩ := by
  intro same
  have scopes := congrArg Frame.argsTy same
  cases scopes

theorem petri_activation_iff_memref_header (graph : Graph args) (input : Tuple (Val cells) args)
    (initial next : Heap cells) (restart : Bool) :
    Finishes (thetaRuntime cells) graph.activation (Memory.encodeInput initial input)
        (.cons ⟨if restart then 1 else 0⟩ (Memory.encodeInput next input)) ↔
      Block.eval (MLIR.MemRef.CF.evalBody input)
          ((MLIR.MemRef.CF.lower cells graph).block MLIR.MemRef.CF.Label.header) .nil ⟨initial⟩ =
        (.inl (if restart then ⟨MLIR.MemRef.CF.Label.header, .nil⟩
          else ⟨MLIR.MemRef.CF.Label.exit, .cons (graph.stopWord input) .nil⟩), ⟨next⟩) := by
  erw [graph.activation_finishes_iff input initial _, MLIR.MemRef.CF.header_transition graph input ⟨initial⟩,
    MLIR.MemRef.observeActivation_eq_step graph input ⟨initial⟩]
  unfold Graph.step
  cases result : graph.body.denote input initial with
  | mk word heap =>
    by_cases stops : word = graph.stopWord input <;> cases restart <;>
      simp [stops, continueTag] <;>
      erw [activationTuple_eq input heap next, successor_eq] <;>
      simp [Ne.symm (distinctFrames (graph.stopWord input))]

end Activation

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Proofs
