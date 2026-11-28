module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Cfg)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Graph MonadicModel)
open Tail.Diamond.MLIR.CF (Widths)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}
variable {execution : Execution regs result} {outcome : Outcome p} {input : Bank (regs := regs) model} {value : Word result}

private theorem env_singleton (env : Env [result]) : env = .cons (env.get .here) .nil := by
  cases env with
  | cons head tail => cases tail; rfl

private theorem tuple_singleton (values : Tuple (Join.model model).Val [.value (.data result)]) :
    values = .cons (values.get .head) .nil := by
  cases values with
  | cons head tail => cases tail; rfl

private theorem cf_return :
    (∃ budget, execution.runCF input budget = some value) ↔
      ∃ fuel, execution.cfTarget.2.run evalOp fuel (encodeValues input) = some (.cons value .nil) := by
  constructor
  · rintro ⟨⟨fuel⟩, returned⟩
    obtain ⟨env, observed, projected⟩ := Option.map_eq_some_iff.mp returned
    exact ⟨fuel, observed.trans (congrArg some ((env_singleton env).trans
      (congrArg (fun v => Env.cons v .nil) projected)))⟩
  · rintro ⟨fuel, observed⟩
    exact ⟨⟨fuel⟩, Option.map_eq_some_iff.mpr ⟨.cons value .nil, observed, rfl⟩⟩

private theorem numbered_return :
    (∃ budget, execution.runNumbered input budget = some value) ↔
      execution.numberedTarget.2.Returns (Join.model model) input (.cons value .nil) := by
  constructor
  · rintro ⟨⟨fuel⟩, returned⟩
    obtain ⟨values, observed, projected⟩ := Option.map_eq_some_iff.mp returned
    exact ⟨fuel, observed.trans (congrArg some ((tuple_singleton values).trans
      (congrArg (fun v : Word result => (Tuple.cons v .nil :
        Tuple (Join.model model).Val [.value (.data result)])) projected)))⟩
  · rintro ⟨fuel, observed⟩
    exact ⟨⟨fuel⟩, Option.map_eq_some_iff.mpr ⟨.cons value .nil, observed, rfl⟩⟩

private theorem source_return :
    (∃ budget, runSource p input budget = some value) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value :=
  ⟨fun ⟨⟨fuel⟩, observed⟩ => ⟨fuel, observed⟩, fun ⟨fuel, observed⟩ => ⟨⟨fuel⟩, observed⟩⟩

private theorem from_emitters
    (bounded : ∀ limit,
      let budgets := execution.budgets limit
      let native := runSource p input budgets.source
      execution.cfTarget.2.run evalOp budgets.cf.blocks (encodeValues input) =
        native.map (fun value => Env.cons value .nil) ∧
      execution.numberedTarget.2.run (Join.model model) budgets.theta.activations input =
        native.map (fun value => (Tuple.cons value .nil : Tuple (Join.model model).Val [.value (.data result)])))
    (returned : ∀ value : Word result,
      let native := ∃ fuel, p.source.runFrom model fuel 0 input = some value
      ((∃ fuel, execution.cfTarget.2.run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔ native) ∧
        (execution.numberedTarget.2.Returns (Join.model model) input (.cons value .nil) ↔ native)) :
    execution.Correct p input := by
  constructor
  · intro limit
    obtain ⟨cf, numbered⟩ := bounded limit
    let readCF (env : Env [result]) : Word result := env.get .here
    let readNumbered (values : Tuple (Join.model model).Val [.value (.data result)]) :
        Word result := values.get .head
    refine ⟨(congrArg (Option.map readCF) cf).trans ?_, (congrArg (Option.map readNumbered) numbered).trans ?_⟩
    all_goals cases runSource p input (execution.budgets limit).source <;> rfl
  · intro value
    exact ⟨cf_return.trans ((returned value).1.trans source_return.symm),
      numbered_return.trans ((returned value).2.trans source_return.symm)⟩

theorem original_correct : (emitOriginal p).execution.Correct p input :=
  from_emitters
    (fun limit => ⟨TwoBackedges.MLIR.CF.lower_run p input (3 * limit + 2),
      TwoBackedges.Numbered.lower_run p model limit input⟩)
    (fun value => ⟨TwoBackedges.MLIR.CF.returns_iff p input value,
      TwoBackedges.Numbered.returns_iff p model input value⟩)

theorem compile_correct [BankDecidableEq Word (dataPorts regs)]
    {facts : Tuple (Fact Word) (dataPorts regs)}
    (compiled : compile p facts = outcome) (compatible : outcome.Compatible facts input) :
    Correct outcome input := by
  suffices view : outcome.execution.Correct p input from ⟨view.bounded, view.returns_iff⟩
  cases outcome with
  | specialized targets =>
    have accepted := (compile_specialized_iff targets).mp compiled
    exact from_emitters (fun limit => Backends.compile_run accepted compatible limit)
      (fun value => Backends.compile_returns_iff accepted compatible value)
  | twoLive targets =>
    exact from_emitters (twoLive_run input compiled) (twoLive_returns_iff input compiled)
  | neitherMarked targets =>
    obtain ⟨rfl, _, _⟩ := (compile_neitherMarked_iff targets).mp compiled
    exact original_correct

private theorem exhaustion_iff {Budget : Type} {run : Budget → Option (Word result)} :
    (∀ budget, run budget = none) ↔ ¬ ∃ value budget, run budget = some value := by
  constructor
  · rintro exhausted ⟨value, budget, observed⟩
    rw [exhausted budget] at observed
    cases observed
  · intro absent budget
    cases observed : run budget with
    | none => rfl
    | some value => exact (absent ⟨value, budget, observed⟩).elim

theorem noReturn_iff (correct : execution.Correct p input) :
    let absent := ¬ ∃ value budget, runSource p input budget = some value
    ((∀ budget, execution.runCF input budget = none) ↔ absent) ∧
      ((∀ budget, execution.runNumbered input budget = none) ↔ absent) := by
  refine ⟨exhaustion_iff.trans ?_, exhaustion_iff.trans ?_⟩
  · exact not_congr (exists_congr fun value => (correct.returns_iff value).1)
  · exact not_congr (exists_congr fun value => (correct.returns_iff value).2)

theorem mem_sourcePart_iff :
    value ∈ sourcePart p input ↔ ∃ budget, runSource p input budget = some value := by
  rw [sourcePart, Part.mem_mk_iff]
  constructor
  · rintro ⟨witness, rfl⟩
    exact Classical.choose_spec witness
  · intro witness
    let dom : ∃ v budget, runSource p input budget = some v := ⟨value, witness⟩
    obtain ⟨budget, returned⟩ := witness
    obtain ⟨other, chosen⟩ := Classical.choose_spec dom
    let common : SourceBudget := ⟨max budget.blocks other.blocks⟩
    have seen : runSource p input common = some value :=
      Tail.Source.runFrom_mono model (Nat.le_max_left ..) returned
    have selected : runSource p input common = some (Classical.choose dom) :=
      Tail.Source.runFrom_mono model (Nat.le_max_right ..) chosen
    exact ⟨dom, Option.some.inj (selected.symm.trans seen)⟩

theorem mem_observeCF_iff {Label : List Width → Type}
    (target : Cfg TargetOp Label (Widths regs) [result]) :
    value ∈ observeCF target input ↔
      ∃ fuel, target.run evalOp fuel (encodeValues input) = some (.cons value .nil) := by
  rw [observeCF, Part.mem_bind_iff]
  constructor
  · rintro ⟨observed, finite, readback⟩
    cases observed with
    | aborted => exact False.elim (Part.notMem_none value readback)
    | returned env =>
      have read : env.get .here = value := (Part.mem_some_iff.mp readback).symm
      obtain ⟨fuel, lifted⟩ := (Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff
        _ evalOp (encodeValues input) (.returned env)).mp finite
      rw [Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run] at lifted
      obtain ⟨actual, run, equal⟩ := Option.map_eq_some_iff.mp lifted
      cases equal
      exact ⟨fuel, run.trans (congrArg some ((env_singleton env).trans
        (congrArg (fun word => Env.cons word .nil) read)))⟩
  · rintro ⟨fuel, run⟩
    refine ⟨.returned (.cons value .nil), ?_, Part.mem_some _⟩
    apply (Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff _ evalOp (encodeValues input) _).mpr
    exact ⟨fuel, by rw [Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, run]; rfl⟩

theorem mem_observeNumbered_iff {sigs}
    (target : Graph (Join.Opcode Op) (dataPorts regs) [] sigs [.value (.data result)]) :
    value ∈ observeNumbered target input ↔
      target.Returns (Join.model model) input (.cons value .nil) := by
  let raw : Part (Tuple (Join.model model).Val [.value (.data result)]) :=
    RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (Join.model model))
      target input
  let readback (values : Tuple (Join.model model).Val [.value (.data result)]) :
      Word result := values.get .head
  change value ∈ raw.map readback ↔ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨values, observed, projected⟩
    have equal : values = .cons value .nil := (tuple_singleton values).trans
      (congrArg (fun word : Word result => (Tuple.cons word .nil :
        Tuple (Join.model model).Val [.value (.data result)])) projected)
    rw [equal] at observed
    exact (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns _ _ _ _).mp
      (Part.eq_some_iff.mpr observed)
  · intro returned
    refine ⟨.cons value .nil, ?_, rfl⟩
    exact Part.eq_some_iff.mp
      ((RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns _ _ _ _).mpr returned)

theorem part_eq (correct : execution.Correct p input) :
    execution.cfPart input = sourcePart p input ∧ execution.numberedPart input = sourcePart p input := by
  refine ⟨Part.ext ?_, Part.ext ?_⟩
  · intro value
    exact (mem_observeCF_iff execution.cfTarget.2).trans
      (cf_return.symm.trans ((correct.returns_iff value).1.trans mem_sourcePart_iff.symm))
  · intro value
    exact (mem_observeNumbered_iff execution.numberedTarget.2).trans
      (numbered_return.symm.trans ((correct.returns_iff value).2.trans mem_sourcePart_iff.symm))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Proofs
