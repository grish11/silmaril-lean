module

public import Silmaril.Languages.Python.Compile.Closure.Body.Defs

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.Link

open Source (BlockPath)
open Core.Closure (CaptureSlot CodeRef Layout Slot)

inductive Code (layout : Layout) where
  | ret (value : Body.Expr layout)
  | assert (test : Body.Expr layout) (next : Code layout)
  | assertFreeVars (receiver : Body.Expr layout) (needle : List UInt32) (expected : Bool) (next : Code layout)
  | assertCellVars (receiver : Body.Expr layout) (needle : List UInt32) (next : Code layout)
  | assertCodeNames (receiver : Body.Expr layout) (needle : List UInt32) (next : Code layout)
  | discardCall (callee : Body.Expr layout) (next : Code layout)
  | assign (destination : Slot layout) (value : Body.Expr layout) (next : Code layout)
  | closure (destination : Slot layout) (path : BlockPath) (ref : CodeRef)
      (captures : Fin ref.layout.captures → CaptureSlot layout) (next : Code layout)

def Code.references {layout : Layout} : Code layout → List (BlockPath × CodeRef)
  | .ret _ => []
  | .assign _ _ next | .assert _ next | .assertFreeVars _ _ _ next
  | .assertCellVars _ _ next | .assertCodeNames _ _ next | .discardCall _ next => next.references
  | .closure _ path ref _ next => (path, ref) :: next.references

end Silmaril.Languages.Python.Compile.Closure.Link
