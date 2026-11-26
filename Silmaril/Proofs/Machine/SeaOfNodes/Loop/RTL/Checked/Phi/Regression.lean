module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Prog StepsNWithin run_returned)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg entry model word)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom encode inputEnv instruction terminatorRegion)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def profile : Profile := ⟨.add, 7, .eq⟩
private def targets : Targets := (profile.lower, Generic.lower profile.graph)
private theorem admitted : lowerChecked profile.graph = some targets := by cbv
private def mem : Memory := Memory.ofList 4 [29, 71, 53, 11]

example : targets.1.WellFormed := (lowerChecked_typed admitted).1

private def frame (old : Word) : Frame Reg := (Frame.empty.set (.arg 1) 2).set .phi old

private abbrev HeaderEval (seed old : Word) (label : Nat) (value : Word) :=
  Eval (instruction model)
    (extend (inputEnv model (entry seed 2)) (Generic.packResult model (out := word) old))
    (Generic.header profile.graph) mem label (Generic.packResult model (out := word) value) mem

-- 5 + 2 equals the limit, so both headers take feedback carrying 7.
example :
    StepsNWithin profile.lower [] 4 ⟨⟨0, 1, 0⟩, frame 5, [], mem⟩
      ⟨⟨0, 1, 0⟩, (profile.headerFrame (frame 5) 5 2).set .phi 7, [], mem⟩ ∧ HeaderEval 5 5 0 7 :=
  activation_agrees profile 5 2 5 (frame 5) mem rfl rfl

-- 6 + 2 differs from the limit, so both headers exit with old word 6.
example :
    StepsNWithin profile.lower [] 4 ⟨⟨0, 1, 0⟩, frame 6, [], mem⟩
      ⟨⟨0, 2, 0⟩, (profile.headerFrame (frame 6) 6 2).set (.node 3) 6, [], mem⟩ ∧ HeaderEval 6 6 1 6 :=
  activation_agrees profile 6 2 6 (frame 6) mem rfl rfl

private def entryFirst : Fin 2 ≃ Incoming where
  toFun := Fin.cases .entry (fun _ => .backedge)
  invFun := Incoming.select 0 1
  left_inv := fun i => Fin.cases rfl (fun j => by rw [Fin.fin_one_eq_zero j]; rfl) i
  right_inv := fun arrival => by cases arrival <;> rfl

private def forward : Fin 2 ≃ Generic.HeaderIncoming profile.graph :=
  entryFirst.trans (Generic.headerIncomingEquiv profile.graph)

private def reversed : Fin 2 ≃ Generic.HeaderIncoming profile.graph :=
  (Equiv.swap 0 1).trans forward

example : Generic.slotBranch profile.graph forward 1 = Generic.slotBranch profile.graph reversed 0 := rfl
example : Generic.slotBranch profile.graph forward 0 = Generic.slotBranch profile.graph reversed 1 := rfl

example : Eval (instruction model) (inputEnv model (entry 5 2))
    (terminatorRegion (Generic.slotBranch profile.graph reversed 1)) mem 0
    (Generic.packResult model (out := word) (5 : Word)) mem :=
  (entry_slot_transfer_iff profile reversed 5 2 mem mem 0 _).mpr ⟨rfl, rfl, rfl⟩

private def carried (old : Word) : Tuple (Val model.value) [.value word] := .cons old .nil

private def feedbackEnv : Env (Atom model) :=
  let env := Generic.unpackEnv model (carried 5) (inputEnv model (entry 5 2))
  let updated := extend env (encode model (sort := word) (7 : Word))
  let limit := extend updated (encode model (sort := word) (7 : Word))
  extend (extend limit (.inl .unit)) .unit

example : Eval (instruction model) feedbackEnv
    (terminatorRegion (Generic.slotBranch profile.graph reversed 0)) mem 0
    (Generic.packResult model (out := word) (7 : Word)) mem :=
  (Generic.slot_transfer_iff profile.graph model reversed 0 feedbackEnv mem mem 0 _).mpr ⟨rfl, rfl, rfl⟩

example : ¬ HeaderEval 5 5 0 5 := by
  intro run
  have native := ((Generic.header_backedge_iff profile.graph model (entry 5 2) (carried 5)
    (carried 5) mem mem).mp run).1
  have different : Sum.inr (α := Word) (carried 7) = Sum.inr (carried 5) := native
  have impossible : (7 : Word) = 5 :=
    congrArg (fun xs : Tuple (Val model.value) [.value word] => xs.get .head) (Sum.inr.inj different)
  exact (by decide : (7 : Word) ≠ 5) impossible

-- The emitted CFG's runnable semantics charges two visits for one backedge.
example : Generic.Fuel.run model (inputEnv model (entry 5 2)) 1 targets.2 = none := by cbv
example : Generic.Fuel.run model (inputEnv model (entry 5 2)) 2 targets.2 =
    some (0, Generic.packResult model (out := word) (7 : Word)) := by cbv
example : Generic.Fuel.run model (inputEnv model (entry 6 2)) 1 targets.2 =
    some (0, Generic.packResult model (out := word) (6 : Word)) := by cbv

private theorem ssa_of_run (seed : Word) (fuel : Nat) (value : Word)
    (run : targets.1.runMain fuel 0 [seed, 2] mem = .returned [value] mem) :
    Eval (instruction model) (inputEnv model (entry seed 2)) targets.2
      mem 0 (Generic.packResult model (out := word) value) mem := by
  have machine : targets.1.oracle 0 [seed, 2] mem [value] mem := by
    unfold Prog.runMain at run
    split at run
    · exact ⟨_, by assumption, run_returned run⟩
    · cases run
  obtain ⟨observed, same, eval⟩ := (returns_iff admitted seed 2 mem mem [value]).mp machine
  cases same
  exact eval

example : Eval (instruction model) (inputEnv model (entry 5 2)) targets.2
    mem 0 (Generic.packResult model (out := word) (7 : Word)) mem :=
  ssa_of_run 5 10 7 (by cbv)

example : Eval (instruction model) (inputEnv model (entry 6 2)) targets.2
    mem 0 (Generic.packResult model (out := word) (6 : Word)) mem :=
  ssa_of_run 6 6 6 (by cbv)

-- Well-typed, but the guard would compare the old bank, not the update.
private def wrongGuard : WordLoop :=
  { profile.graph with
    header := match profile.graph.header with
      | .cons update updateArgs (.cons limit limitArgs _) =>
        .cons update updateArgs (.cons limit limitArgs (.cons .eq
          (.cons (.arg (.tail (.tail .head))) (.cons (.output (1 : Fin 2) .head) .nil)) .nil)) }

example : lowerChecked wrongGuard = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi
