module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (encodeTuple inputEnv instruction)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def capture (slot : Fin 3) := argumentPort 3 slot
private def old (slot : Fin 3) := suffixPort (wordPorts 3) (capture slot)

private def source : Source 3 [[wordPort], [.value .predicate]] where
  preheader := .cons .sub (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil)) .nil
  header :=
    .cons .add (.cons (.arg (old 0)) (.cons (.arg (old 1)) .nil))
      (.cons .slt (.cons (.output (0 : Fin 1) .head) (.cons (.arg (old 2)) .nil)) .nil)
  phiInputs
    | .entry => .cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) (.cons (.arg (capture 2)) .nil))
    | .backedge => .cons (.output (0 : Fin 2) .head) (.cons (.arg (old 1)) (.cons (.arg (old 2)) .nil))
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

private def rawEntry : Source 3 [[wordPort], [.value .predicate]] :=
  { source with
    phiInputs
      | .entry => .cons (.arg (capture 0)) (.cons (.arg (capture 1)) (.cons (.arg (capture 2)) .nil))
      | .backedge => source.phiInputs .backedge }

example : lowerChecked rawEntry = none := by cbv
example : lowerChecked { source with preheader := .cons (.const 1) .nil .nil } = none := by cbv

example : lowerChecked { source with
    phiInputs
      | .entry => source.phiInputs .entry
      | .backedge =>
        .cons (.output (0 : Fin 2) .head)
          (.cons (.arg (prefixPort (capture 1))) (.cons (.arg (old 2)) .nil)) } = none := by cbv

private def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))
private def input := bank 6 2 5
private def mem := Memory.ofList 4 [29, 71, 53, 11]
private def originalInputs : ArgumentColumn 3 3 :=
  .cons (.arg (capture 0)) (.cons (.arg (capture 1)) (.cons (.arg (capture 2)) .nil))

private def plan : Plan 3 where
  initializer := ⟨.sub, .cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil)⟩
  entry := source.phiInputs .entry
  row :=
    { entry := originalInputs
      copies := originalInputs
      updates := [⟨.add, 0, 0, 1⟩]
      guardIndex := 0
      comparison := .slt
      limit := 0
      exitSlot := 0
      exitProducer := some 0
      guardOperand := .bank 2 }
private theorem recognized : recognize source = some plan := by cbv
private def targets : Checked.Phi.Targets := (plan.rtl, Generic.lower source)
private theorem accepted : lowerChecked source = some targets := by cbv

example : Table.lowerChecked source = some targets := by cbv

example : (targets.1.block? 0 0).map (·.ops) =
    some [.binary .sub (.arg 6) (.arg 0) (.arg 2)] := by cbv
example : (targets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 6, .arg 1, .arg 2]) := by cbv
example : (targets.1.block? 0 1).map (·.term) =
    some (.cond (.node 1) 1 [.node 0, .arg 4, .arg 5] 2 [.node 0]) := by cbv

example : source.initial model input = bank 1 2 5 := by cbv
example : source.step model input (source.initial model input) = .inr (bank 3 2 5) := by cbv
example : rawEntry.step model input (rawEntry.initial model input) = .inl (8 : Word) := by cbv

example :
    ArgsMatch
      (bindWords 3 ((bindWords 0 Frame.empty input).set (.arg 6) 1) (bank 1 2 5))
      (appendTuple (bank 1 2 5) input) ∧
    Eval (instruction model) (inputEnv model input) (Generic.entry plan.graph) mem
      0 (encodeTuple model (bank 1 2 5)) mem :=
  (entry_packet plan input _ mem (bindWords_args input)).2

example :
    Eval (instruction model) (extend (inputEnv model input) (encodeTuple model (bank 1 2 5)))
      (Generic.header plan.graph) mem 0 (encodeTuple model (bank 3 2 5)) mem := by
  let fr := (bindWords 0 Frame.empty input).set (.arg 6) 1
  have entered := entry_packet plan input _ mem (bindWords_args input)
  have matching : ArgsMatch (bindWords 3 fr (bank 1 2 5)) (appendTuple (bank 1 2 5) input) :=
    entered.2.1
  have feedback := header_packet plan input (bank 1 2 5) _ mem matching
  have selected : plan.graph.step model input (bank 1 2 5) = .inr (bank 3 2 5) := by cbv
  rw [selected] at feedback
  exact feedback.2.2

private theorem counted : source.ReturnsAfter model input 1 (source.initial model input) (5 : Word) :=
  .backedge (next := bank 3 2 5) (by cbv) (.exit (by cbv))

example : targets.1.runMain 9 0 (words input) mem = .returned [5] mem :=
  (rtl_runMain_fuel_iff recognized accepted _ _ _ _ _).mpr ⟨1, (5 : Word), counted, by decide, rfl, rfl⟩
example : targets.1.runMain 9 0 (words input) mem = .returned [5] mem := by cbv
example : (targets.1.runMain 8 0 (words input) mem).returnedValues? = none := by cbv
example : Generic.Fuel.run model (inputEnv model input) 2 targets.2 =
    some (0, Generic.packResult model (out := word) (5 : Word)) := by cbv
example : Generic.Fuel.run model (inputEnv model input) 1 targets.2 = none := by cbv

example : targets.1.oracle 0 (words input) mem [5] mem :=
  (rtl_return_iff accepted _ _ _ _).mpr ⟨5, ⟨1, counted⟩, rfl, rfl⟩
example : Eval (instruction model) (inputEnv model input) targets.2 mem
    0 (Generic.packResult model (out := word) (5 : Word)) mem :=
  (lambda_return_iff accepted _ _ _ _ _).mpr ⟨5, ⟨1, counted⟩, rfl, rfl, rfl⟩

private def spin := bank 0 0 1
private def fixedBank := bank (-1) 0 1

private theorem spinAbsent : source.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, returned⟩
  exact source.not_returns_of_backedge_invariant model spin value (· = fixedBank) (by cbv)
    (fun old fixed => fixed.symm ▸ ⟨fixedBank, by cbv, rfl⟩)
    ((source.returns_iff_mem_denote model _ _).mpr returned)

example :
    (∀ returned final, ¬ targets.1.oracle 0 (words spin) mem returned final) ∧
    (∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin) targets.2 mem label payload final) :=
  let absence := no_finite_return_iff accepted spin mem
  ⟨absence.1.mpr spinAbsent, absence.2.mpr spinAbsent⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader
