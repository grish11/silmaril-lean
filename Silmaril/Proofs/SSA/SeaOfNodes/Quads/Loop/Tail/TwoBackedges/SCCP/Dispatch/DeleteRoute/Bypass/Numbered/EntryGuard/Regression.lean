module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard

open Bypass.MLIR.CF.Example (entry facts program regs width word)
open Bypass.Backends.Example (stoppingFacts)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Blocks (Bank)

private def assumptions := facts (.constant ⟨true⟩)

private def guardIndex (input : Bank (regs := regs) model) : Nat :=
  (((selector assumptions).2.toGraph.run (Join.model model) input).get .head).down.val

private def finalIsGamma (target : Target regs width) : Bool :=
  match target with
  | ⟨[], _⟩ => false
  | ⟨_ :: tail, .region nodes _ _⟩ =>
    (nodes (Fin.last tail.length)).kind.arity == 2

#guard
  match compile program assumptions with
  | .error _ => false
  | .ok target =>
    let run bank fuel : Option Nat :=
      (target.2.run (Join.model model) fuel bank).map (fun values => (values.get .head : Word width).toNat)
    let covered := entry true true
    let uncovered := entry true false
    finalIsGamma target &&
      guardIndex covered == 1 && guardIndex uncovered == 0 &&
      run covered 1 == some 99 && run uncovered 1 == some 7 &&
      (run covered 0).isNone && (run uncovered 0).isNone

-- A different word rejects even when the selector agrees.
#guard guardIndex (.cons ⟨true⟩ (.cons ⟨true⟩ (.cons (8 : Word width) .nil))) = 0

-- The true arm loops forever; the false arm stops with the original word.
private def trueLoops : Program Op regs word :=
  { program with feedback := fun side => if side then [] else program.feedback false }

#guard
  match compile trueLoops assumptions with
  | .error _ => false
  | .ok target =>
    (target.2.run (Join.model model) 20 (entry true true)).isNone &&
      ((target.2.run (Join.model model) 1 (entry true false)).map
        (fun values => (values.get .head : Word width).toNat)) == some 7

private theorem trueLoops_at_header (fuel : Nat) :
    trueLoops.source.runFrom model fuel 1 (entry true true) = none := by
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [Program.source_header]
      have step : trueLoops.step model (entry true true) = .inr (true, entry true true) := rfl
      rw [step]
      exact ih (fuel - 2) (by omega)

example {target : Target regs width} (success : compile trueLoops assumptions = .ok target) :
    ∀ fuel, target.2.run (Join.model model) fuel (entry true true) = none := by
  apply (compile_noReturn_iff success (entry true true)).mpr
  rintro ⟨value, fuel, returned⟩
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Program.source_entry] at returned
    change trueLoops.source.runFrom model fuel 1 (entry true true) = some value at returned
    rw [trueLoops_at_header] at returned
    cases returned

#guard (match compile program (facts .overdefined) with | .error .bothMarked => true | _ => false)
#guard (match compile program stoppingFacts with | .error .neitherMarked => true | _ => false)

example {target : Target regs width} (success : compile program assumptions = .ok target) :
    target.2.Returns (Join.model model) (entry true false) (.cons (7 : Word width) .nil) :=
  (compile_returns_iff success (entry true false) 7).mpr ⟨5, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard
