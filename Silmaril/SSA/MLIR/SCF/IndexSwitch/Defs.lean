module

public import Silmaril.SSA.MLIR.CF.SwitchAssert.Defs

/-! A straight-line, result-bearing `scf.index_switch` at a 64-bit index layout. -/

@[expose] public section

namespace Silmaril.MLIR.SCF.IndexSwitch

open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature)
open CF.SwitchAssert (Block Cfg)

/-- The source `index` width in this profile. The target `i64` cast is the
identity on its representation in the width-indexed scope. -/
def indexWidth : Width := ⟨64, by decide⟩

/-- The exact bits of an upstream signed `int64_t` case attribute. Its signed
value is `BitVec.toInt`; there is a unique such value for every pattern. -/
abbrev CaseValue := BitVec indexWidth.val

/-- A region with no block arguments. Its terminator models `scf.yield`. -/
abbrev Arm (Op : OpSignature) (Input Yielded : List Width) :=
  Code Op (fun Γ => Operands Γ Yielded) Input

/-- A single structured switch in a dominating input scope. Only the selected
region's yielded values are added to that scope for the parent continuation. -/
structure Program (Op : OpSignature) (Input Result : List Width) where
  Yielded : List Width
  selector : Var Input indexWidth
  cases : List (CaseValue × Arm Op Input Yielded)
  unique : (cases.map Prod.fst).Nodup
  fallback : Arm Op Input Yielded
  cont : Code Op (fun Γ => Operands Γ Result) (Yielded ++ Input)

variable {Op : OpSignature} {Input Result Yielded : List Width}

/-- Source dispatch compares the signed interpretations of the selector and
the case attributes, with the default region used on a miss. -/
def Program.selectArm (program : Program Op Input Result) (input : Env Input) :
    Arm Op Input program.Yielded :=
  let selector := (input.get program.selector).toInt
  match program.cases.find? (fun entry => decide (entry.1.toInt = selector)) with
  | some (_, body) => body
  | none => program.fallback

/-- Evaluate the selected region, then run the parent continuation with the
yielded tuple in scope. -/
def Program.eval (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) : Env Result :=
  let values := (program.selectArm input).eval evalOp (fun args env => args.eval env) input
  program.cont.eval evalOp (fun args env => args.eval env) (values.append input)

/-- Dispatch, the chosen region, and the continuation each cost one tick. -/
def Program.run (program : Program Op Input Result) (evalOp : Eval Op)
    (input : Env Input) : Nat → Option (Env Result)
  | 0 | 1 | 2 => none
  | _ + 3 => some (program.eval evalOp input)

/-- Each listed region has a label and takes no arguments. The shared
continuation takes exactly the switch results, even when this tuple is empty. -/
inductive Label (cases : List (CaseValue × Arm Op Input Yielded)) : List Width → Type where
  | case (entry : {entry // entry ∈ cases}) : Label cases []
  | fallback : Label cases []
  | join : Label cases Yielded

/-- Emit one flat CFG. The same-width index cast is erased. The entry
dispatches with `cf.switch`, each yield becomes a branch passing its operands
to the join, and the join runs the parent continuation. -/
def Program.lower (program : Program Op Input Result) : Cfg Op (Label program.cases) Input Result where
  entry := .terminator (.switch {
    flag := program.selector
    widthSupported := by decide
    defaultEdge := ⟨.fallback, .nil⟩
    cases := program.cases.attach.map fun entry => (entry.val.1, ⟨.case entry, .nil⟩)
    unique := by simpa only [List.map_map, Function.comp_def, List.attach_map_val] using program.unique
  })
  block
    | .case entry => Block.embed (entry.val.2.mapTerm (fun values => .br ⟨.join, values⟩))
    | .fallback => Block.embed (program.fallback.mapTerm (fun values => .br ⟨.join, values⟩))
    | .join => Block.embed (program.cont.mapTerm (fun values => .ret values))

end Silmaril.MLIR.SCF.IndexSwitch
