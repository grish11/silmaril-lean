module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Denotation.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Denotation.Adequacy

/-! Unbounded partial observations at the native input and initial memory. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} {entrySigs sigs : List (List PortTy)}

/-- Membership is exactly an actual singleton RTL return with the recorded memory. -/
theorem mem_rtlDenote_iff (target : Prog Reg) (input : WordTuple arity)
    (initial final : Memory) (value : Word) :
    (value, final) ∈ rtlDenote target input initial ↔ target.oracle 0 (words input) initial [value] final :=
  Proofs.mem_rtlDenote_iff target input initial final value

/-- Membership is exactly an actual λSSA exit with the packed word and recorded memory. -/
theorem mem_lambdaDenote_iff (target : Region (Primitive WordOp)) (input : WordTuple arity)
    (initial final : Memory) (value : Word) :
    (value, final) ∈ lambdaDenote target input initial ↔
      Eval (instruction model) (inputEnv model input) target initial 0
        (Generic.packResult model (out := word) value) final :=
  Proofs.mem_lambdaDenote_iff target input initial final value

/-- Any finite instruction budget witnessing a return contributes the same observation. -/
theorem mem_rtlDenote_iff_runMain (target : Prog Reg) (input : WordTuple arity)
    (initial final : Memory) (value : Word) :
    (value, final) ∈ rtlDenote target input initial ↔
      ∃ fuel, target.runMain fuel 0 (words input) initial = .returned [value] final :=
  Proofs.mem_rtlDenote_iff_runMain target input initial final value

variable {g : SourceWithEntry arity entrySigs sigs} {targets : Checked.Phi.Targets}

/-- An exit with at most `budget` backedges is observed in `budget + 1` header visits. -/
theorem lambda_run_succ_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (value : Word) (budget : Nat) :
    Generic.Fuel.run model (inputEnv model input) (budget + 1) targets.2 =
        some (0, Generic.packResult model (out := word) value) ↔
      ∃ count ≤ budget, g.ReturnsAfter model input count (g.initial model input) value :=
  Proofs.lambda_run_succ_iff accepted input value budget

/-- Finite header-visit witnesses describe the λSSA partial observation of a checked
target. Its actual evaluation returns the entire initial memory. -/
theorem mem_lambdaDenote_iff_run (accepted : lowerChecked g = some targets)
    (input : WordTuple arity) (initial final : Memory) (value : Word) :
    (value, final) ∈ lambdaDenote targets.2 input initial ↔ final = initial ∧
      ∃ visits, Generic.Fuel.run model (inputEnv model input) visits targets.2 =
        some (0, Generic.packResult model (out := word) value) :=
  Proofs.mem_lambdaDenote_iff_run accepted input initial final value

/-- Both actual target denotations equal the native partial result paired with
initial memory. Membership can be witnessed at each backend's own budget. -/
theorem denotations_eq (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial : Memory) :
    rtlDenote targets.1 input initial = nativeDenote g input initial ∧
      lambdaDenote targets.2 input initial = nativeDenote g input initial :=
  Proofs.denotations_eq accepted input initial

/-- Each target is undefined exactly when the native loop has no finite return. -/
theorem denotations_none_iff (accepted : lowerChecked g = some targets)
    (input : WordTuple arity) (initial : Memory) :
    (rtlDenote targets.1 input initial = Part.none ↔ g.denote model input = Part.none) ∧
      (lambdaDenote targets.2 input initial = Part.none ↔ g.denote model input = Part.none) :=
  Proofs.denotations_none_iff accepted input initial

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
