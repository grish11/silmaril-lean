module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Prog StepsNWithin run_returned)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom encode encodeTuple inputEnv instruction terminatorRegion)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def profile : Profile := ⟨.add, 7, .eq⟩
private def native : Native := graph profile
private def targets : Checked.Phi.Targets := (rtl native, Generic.lower native)
private theorem accepted : lowerChecked native = some targets := by cbv
private def mem : Memory := Memory.ofList 4 [29, 71, 53, 11]
private def input : WordTuple 2 := pair 5 2
private def next : WordTuple 2 := pair 7 5

example : targets.1.WellFormed := (lowerChecked_typed accepted).1
example : bankIncoming native .backedge = [.node 0, .arg 2] := rfl

private def frame : Frame Reg := bindBank Frame.empty input

example :
    StepsNWithin targets.1 [] 4 ⟨⟨0, 1, 0⟩, frame, [], mem⟩
      ⟨⟨0, 1, 0⟩, bindBank (profile.headerFrame frame 5 2) next, [], mem⟩ ∧
    Eval (instruction model) (extend (inputEnv model input) (encodeTuple model input))
      (Generic.header native) mem 0 (encodeTuple model next) mem :=
  activation_agrees profile input 5 2 frame mem rfl rfl

private def feedbackSnapshot : Option (List Word) :=
  match targets.1.runMain 5 0 (words input) mem with
  | .running state => state.frame.readAll (paramRegs 2 2)
  | _ => none

example : feedbackSnapshot = some [7, 5] := by cbv

private def entryFirst : Fin 2 ≃ Incoming where
  toFun := Fin.cases .entry (fun _ => .backedge)
  invFun := Incoming.select 0 1
  left_inv := fun i => Fin.cases rfl (fun j => by rw [Fin.fin_one_eq_zero j]; rfl) i
  right_inv := fun arrival => by cases arrival <;> rfl

private def forward : Fin 2 ≃ Generic.HeaderIncoming native :=
  entryFirst.trans (Generic.headerIncomingEquiv native)

private def reversed : Fin 2 ≃ Generic.HeaderIncoming native :=
  (Equiv.swap 0 1).trans forward

example : Generic.slotBranch native forward 1 = Generic.slotBranch native reversed 0 := rfl
example : Generic.slotBranch native forward 0 = Generic.slotBranch native reversed 1 := rfl

example : Eval (instruction model) (inputEnv model input)
    (terminatorRegion (Generic.slotBranch native reversed 1)) mem 0 (encodeTuple model input) mem :=
  (Generic.slot_transfer_iff native model reversed 1 _ mem mem 0 _).mpr ⟨rfl, rfl, rfl⟩

private def edgeEnv : Env (Atom model) :=
  let env := Generic.unpackEnv model input (inputEnv model input)
  let updated := extend env (encode model (sort := word) (7 : Word))
  let limit := extend updated (encode model (sort := word) (7 : Word))
  extend (extend limit (.inl .unit)) .unit

example : Eval (instruction model) edgeEnv
    (terminatorRegion (Generic.slotBranch native reversed 0)) mem 0 (encodeTuple model next) mem :=
  (Generic.slot_transfer_iff native model reversed 0 edgeEnv mem mem 0 _).mpr ⟨rfl, rfl, rfl⟩

-- Sequential copying would incorrectly feed back (7, 7).
example : ¬ Eval (instruction model) (extend (inputEnv model input) (encodeTuple model input))
    (Generic.header native) mem 0 (encodeTuple model (pair 7 7)) mem := by
  intro run
  have source := ((Generic.header_backedge_iff native model input input (pair 7 7) mem mem).mp run).1
  have different : Sum.inr (α := Word) next = Sum.inr (pair 7 7) := source
  have impossible : (5 : Word) = 7 :=
    congrArg (fun xs : WordTuple 2 => xs.get (.tail .head)) (Sum.inr.inj different)
  exact (by decide : (5 : Word) ≠ 7) impossible

private theorem ssa_of_run (values : WordTuple 2) (fuel : Nat) (value : Word)
    (run : targets.1.runMain fuel 0 (words values) mem = .returned [value] mem) :
    Eval (instruction model) (inputEnv model values) targets.2
      mem 0 (Generic.packResult model (out := word) value) mem := by
  have machine : targets.1.oracle 0 (words values) mem [value] mem := by
    unfold Prog.runMain at run
    split at run
    · exact ⟨_, by assumption, run_returned run⟩
    · cases run
  obtain ⟨observed, same, eval⟩ := (returns_iff accepted values mem mem [value]).mp machine
  cases same
  exact eval

example : Eval (instruction model) (inputEnv model input) targets.2
    mem 0 (Generic.packResult model (out := word) (5 : Word)) mem :=
  ssa_of_run input 10 5 (by cbv)

example : Eval (instruction model) (inputEnv model (pair 6 2)) targets.2
    mem 0 (Generic.packResult model (out := word) (2 : Word)) mem :=
  ssa_of_run (pair 6 2) 6 2 (by cbv)

example : Generic.Fuel.run model (inputEnv model input) 2 targets.2 =
    some (0, Generic.packResult model (out := word) (5 : Word)) := by cbv

private def wrongCopy : Native :=
  { native with
    phiInputs
      | .entry => native.phiInputs .entry
      | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head) .nil) }

example : lowerChecked wrongCopy = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded
