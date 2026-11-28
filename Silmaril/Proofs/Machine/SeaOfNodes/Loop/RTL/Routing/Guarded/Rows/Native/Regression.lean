module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg WordOp model word)
open Silmaril.SSA.RVSDG (Origin)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (encodeTuple inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev scheduleSigs := [[wordPort], [wordPort], [.value .predicate]]

private def oldPort (slot : Fin 4) := suffixPort (wordPorts 4) (argumentPort 4 slot)

private def schedule (addLeft : Origin (bankArgs 4) [] wordPort)
    (compareLeft compareRight : Origin (bankArgs 4) [[wordPort], [wordPort]] wordPort) :
    Dataflow WordOp (bankArgs 4) [] scheduleSigs :=
  .cons .add (.cons addLeft (.cons (.arg (oldPort 1)) .nil))
    (.cons .sub (.cons (.arg (oldPort 2)) (.cons (.arg (oldPort 0)) .nil))
      (.cons .slt (.cons compareLeft (.cons compareRight .nil)) .nil))

-- Isolate Simple chapter 13's continuation test (arg + 79) < (32 - arg)
-- in one native loop. Inputs supply both offsets. The left result updates
-- arg, and the right result is available to both feedback and exit.
private def source : BankGraph 4 scheduleSigs where
  preheader := .nil
  header := schedule (.arg (oldPort 0)) (.output (0 : Fin 2) .head) (.output (1 : Fin 2) .head)
  phiInputs
    | .entry => .cons (.arg (argumentPort 4 0)) (.cons (.arg (argumentPort 4 2))
        (.cons (.arg (argumentPort 4 1)) (.cons (.arg (argumentPort 4 3)) .nil)))
    | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.arg (oldPort 1))
        (.cons (.arg (oldPort 2)) (.cons (.output (1 : Fin 3) .head) .nil)))
  predicate := .output (2 : Fin 3) .head
  result := .output (1 : Fin 3) .head

private def spec : Spec where
  entry := [0, 2, 1, 3]
  copies := [0, 1, 2, 3]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 3, 2, 0⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .slt
  limit := 0
  guardRhs := some (.output 1 0)
  exitSlot := 3
  exitOrigin := some (.output 1 0)

private theorem recognized : recognize source = some spec := by cbv

-- The captured argument equals the old bank value on entry, but not
-- after feedback. A typed external reference is not an old-bank producer input.
example : lowerChecked { source with header := schedule (.arg .head) (.output (0 : Fin 2) .head) (.output (1 : Fin 2) .head) } = none := by cbv

private def duplicateFeedback : BankGraph 4 scheduleSigs :=
  { source with
    phiInputs
      | .entry => source.phiInputs .entry
      | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head)
          (.cons (.arg (oldPort 2)) (.cons (.output (1 : Fin 3) .head) .nil))) }

example : lowerChecked duplicateFeedback = none := by cbv

example : (lowerChecked { source with result := .arg (oldPort 3) }).isSome = true := by cbv

private def targets : Checked.Phi.Targets := (lowerBank source, Generic.lower source)
private theorem accepted : lowerChecked source = some targets := by cbv

example : (targets.1.block? 0 1).map (·.ops) = some
    [.binary .add (.node 0) (.arg 4) (.arg 5), .binary .sub (.node 1) (.arg 6) (.arg 4),
     .binary (.cmp .lts) (.node 2) (.node 0) (.node 1)] := by cbv

example : (targets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 0, .arg 2, .arg 1, .arg 3]) := by cbv
example : (targets.1.block? 0 1).map (·.term) =
    some (.cond (.node 2) 1 [.node 0, .arg 5, .arg 6, .node 1] 2 [.node 1]) := by cbv

private def bank (x a b r : Word) : WordTuple 4 := .cons x (.cons a (.cons b (.cons r .nil)))
private def input := bank (-80) 32 79 0
private def spin := bank (-1) 0 0 1
private def mem := Memory.ofList 4 [29, 71, 53, 11]

-- The first test is -1 < 112. Both unsigned and reversed comparisons
-- would exit with 112 immediately. The next test, 78 < 33, exits with 33.
private theorem returns : source.Returns model input (33 : Word) :=
  ⟨1, .backedge (next := bank (-1) 79 32 112) (by cbv) (.exit (by cbv))⟩

example {p : Plan 4} (checked : Rows.checkPlan 4 spec = some p) (frame : Frame Reg)
    (agree : ArgsMatch frame (appendTuple (source.initial model input) input)) :
    Eval (instruction model)
      (extend (inputEnv model input) (encodeTuple model (source.initial model input)))
      (Generic.header source) mem 0 (encodeTuple model (bank (-1) 79 32 112)) mem := by
  have activation := activation_agrees recognized checked input (source.initial model input) frame mem agree
  have taken : source.step model input (source.initial model input) = .inr (bank (-1) 79 32 112) := by cbv
  rw [taken] at activation
  exact activation.2

example : targets.1.runMain 10 0 (words input) mem = .returned [33] mem := by cbv
example : Generic.Fuel.run model (inputEnv model input) 2 targets.2 =
    some (0, Generic.packResult model (out := word) (33 : Word)) := by cbv

example : targets.1.oracle 0 (words input) mem [33] mem :=
  (rtl_return_iff accepted _ _ _ _).mpr ⟨33, returns, rfl, rfl⟩

example : Eval (instruction model) (inputEnv model input) targets.2 mem 0
    (Generic.packResult model (out := word) (33 : Word)) mem :=
  (lambda_return_iff accepted _ _ _ _ _).mpr ⟨33, returns, rfl, rfl, rfl⟩

private theorem spinAbsent (g : BankGraph 4 scheduleSigs)
    (entry : g.initial model spin = spin) (step : g.step model spin spin = .inr spin) :
    g.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact g.not_returns_of_backedge_invariant model spin value (· = spin) entry
    (fun old fixed => fixed.symm ▸ ⟨spin, step, rfl⟩)
    ((g.returns_iff_mem_denote model _ _).mpr present)

example :
    (∀ returned final, ¬ targets.1.oracle 0 (words spin) mem returned final) ∧
    (∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin)
      targets.2 mem label payload final) :=
  let iff := no_finite_return_iff accepted spin mem
  let absent := spinAbsent source (by cbv) (by cbv)
  ⟨iff.1.mpr absent, iff.2.mpr absent⟩

-- Build the native comparison directly. Slot 3 holds the previous
-- subtraction result, and the same activation computes its replacement.
private def bankSource : BankGraph 4 scheduleSigs :=
  { source with
    header := schedule (.arg (oldPort 0)) (.output (0 : Fin 2) .head) (.arg (oldPort 3)) }

private def bankSpec : Spec := { spec with guardRhs := some (.arg 3) }
private def bankTargets : Checked.Phi.Targets := (lowerBank bankSource, Generic.lower bankSource)
private theorem bankRecognized : recognize bankSource = some bankSpec := by cbv
private theorem bankAccepted : lowerChecked bankSource = some bankTargets := by cbv

-- Absolute header port 3 is the captured input, not bank-local slot 3.
example : lowerChecked { bankSource with
    header := schedule (.arg (oldPort 0)) (.output (0 : Fin 2) .head)
      (.arg (prefixPort (argumentPort 4 3))) } = none := by cbv

example : lowerChecked { bankSource with
    header := schedule (.arg (oldPort 0)) (.arg (oldPort 3)) (.output (0 : Fin 2) .head) } = none := by cbv

example : (bankTargets.1.block? 0 1).bind (fun block => block.ops[2]?) =
    some (.binary (.cmp .lts) (.node 2) (.node 0) (.arg 7)) := by cbv

example : (bankTargets.1.block? 0 1).map (·.term) =
    some (.cond (.node 2) 1 [.node 0, .arg 5, .arg 6, .node 1] 2 [.node 1]) := by cbv

private def afterOne := bank (-1) 79 32 112
private def afterTwo := bank 78 79 32 33

-- Comparing 78 against old 112 takes the second backedge.
-- Comparing against fresh 33 or captured 0 would exit here.
private theorem secondFeedback : bankSource.step model input afterOne = .inr afterTwo := by cbv

private theorem bankReturns : bankSource.Returns model input (-46 : Word) :=
  ⟨2, .backedge (next := afterOne) (by cbv) (.backedge secondFeedback (.exit (by cbv)))⟩

example {p : Plan 4} (checked : Rows.checkPlan 4 bankSpec = some p) (frame : Frame Reg)
    (agree : ArgsMatch frame (appendTuple afterOne input)) :
    Eval (instruction model) (extend (inputEnv model input) (encodeTuple model afterOne))
      (Generic.header bankSource) mem 0 (encodeTuple model afterTwo) mem := by
  have activation := activation_agrees bankRecognized checked input afterOne frame mem agree
  rw [secondFeedback] at activation
  exact activation.2

example : bankTargets.1.runMain 14 0 (words input) mem = .returned [-46] mem := by cbv
example : Generic.Fuel.run model (inputEnv model input) 3 bankTargets.2 =
    some (0, Generic.packResult model (out := word) (-46 : Word)) := by cbv

example : bankTargets.1.oracle 0 (words input) mem [-46] mem :=
  (rtl_return_iff bankAccepted _ _ _ _).mpr ⟨-46, bankReturns, rfl, rfl⟩

example : Eval (instruction model) (inputEnv model input) bankTargets.2 mem 0
    (Generic.packResult model (out := word) (-46 : Word)) mem :=
  (lambda_return_iff bankAccepted _ _ _ _ _).mpr ⟨-46, bankReturns, rfl, rfl, rfl⟩

example :
    (∀ returned final, ¬ bankTargets.1.oracle 0 (words spin) mem returned final) ∧
    (∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin)
      bankTargets.2 mem label payload final) :=
  let iff := no_finite_return_iff bankAccepted spin mem
  let absent := spinAbsent bankSource (by cbv) (by cbv)
  ⟨iff.1.mpr absent, iff.2.mpr absent⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native
