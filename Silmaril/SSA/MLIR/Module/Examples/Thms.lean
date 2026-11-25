module

public import Silmaril.SSA.MLIR.Thms
public import Silmaril.SSA.MLIR.Institution.Syntax.Defs
public import Silmaril.SSA.MLIR.Institution.Arith.Thms
public import Silmaril.SSA.MLIR.Institution.Arith.Examples.Defs

/-! Exercise the typed module interface with scalar SSA and isolated-region expressions. -/

namespace Silmaril.MLIR.Module.Examples

open Arith (Block Env Width)
open Arith.Examples (doubleMul i1 i8 squareAdd)
open Institution.Arith (assignment model signature translate translate_denote)
open Institution.Arith.Examples (squareInput)

private def double : FuncOf Block := ⟨"double", [i8], i8, doubleMul i8⟩

private def square : FuncOf Block := ⟨"square_add", [i1, i8], i8, squareAdd⟩

private def scalarModule : FuncModule Block := ⟨[double, square]⟩

private abbrev Context := Institution.Syntax.Context signature

private abbrev IsolatedBody (inputs outputs : Context) :=
  Institution.Block signature inputs.ty outputs.ty

private def inputContext (widths : List Width) : Context := ⟨widths.length, widths.get⟩

private def outputContext (width : Width) : Context := ⟨1, fun _ => width⟩

private def translateBody {inputs : List Width} {output : Width} (body : Block inputs output) :
    IsolatedBody (inputContext inputs) (outputContext output) :=
  fun _ => translate body

private def isolatedModule : FuncModule IsolatedBody :=
  scalarModule.map inputContext outputContext translateBody

example : scalarModule.find? "double" = some double := rfl

example : double.body.denote (Env.cons 200#8 .nil) = 144#8 := rfl

example : isolatedModule.toModule =
    Module.map (FuncOf.map inputContext outputContext translateBody) scalarModule.toModule :=
  scalarModule.toModule_map inputContext outputContext translateBody

example : isolatedModule.find? "square_add" =
    some (square.map inputContext outputContext translateBody) :=
  scalarModule.find?_map inputContext outputContext translateBody "square_add"

example : ((square.map inputContext outputContext translateBody).body (0 : Fin 1)).denote
    model (assignment squareInput) = 164#8 :=
  (translate_denote squareAdd squareInput).trans rfl

end Silmaril.MLIR.Module.Examples
