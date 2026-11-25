module

public import Silmaril.Languages.Python.Compile.Closure.Body.Defs
public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs

/-! # Link lowered Python closure bodies into a Core dispatch table

The entry function has key zero. Lexical preorder assigns dense keys to
nested declarations. A linked closure carries its child's code reference
and captures, with the child body stored in the code table.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.Link

open Source (BlockPath)
open Core.Closure (CaptureSlot CodeRef Layout Slot)
open Core.Closure.Dispatch (CodeTable Entry)

inductive Code (layout : Layout) where
  | ret (value : Body.Expr layout)
  | assign (destination : Slot layout) (value : Body.Expr layout) (next : Code layout)
  | closure (destination : Slot layout) (path : BlockPath) (ref : CodeRef)
      (captures : Fin ref.layout.captures → CaptureSlot layout) (next : Code layout)

def Code.references {layout : Layout} : Code layout → List (BlockPath × CodeRef)
  | .ret _ => []
  | .assign _ _ next => next.references
  | .closure _ path ref _ next => (path, ref) :: next.references

structure Block where
  path : BlockPath
  entry : Entry Code

structure LinkedBody (layout : Layout) where
  code : Code layout
  children : List Block

/-- `first` is the key available for the next nested declaration. -/
def linkBody {layout : Layout} (first : Nat) : Body.Code layout → LinkedBody layout
  | .ret value => ⟨.ret value, []⟩
  | .assign slot value rest =>
    let tail := linkBody first rest
    ⟨.assign slot value tail.code, tail.children⟩
  | .closure slot path childLayout parameters captures child rest =>
    let nested := linkBody (first + 1) child
    let tail := linkBody (first + 1 + nested.children.length) rest
    let entry : Entry Code := ⟨childLayout, ⟨parameters, nested.code⟩⟩
    ⟨.closure slot path ⟨first, childLayout⟩ captures tail.code,
      ⟨path, entry⟩ :: (nested.children ++ tail.children)⟩

structure Program where
  entry : CodeRef
  blocks : List Block

def Program.table (program : Program) : CodeTable Code :=
  fun key => program.blocks[key]?.map Block.entry

def Program.references (program : Program) : List (BlockPath × CodeRef) :=
  program.blocks.flatMap (fun block => block.entry.definition.body.references)

def link {source : Source.Module} (compiled : Body.Compiled source) : Program :=
  let layout := frameLayout compiled.tree.scope
  let root := linkBody 1 compiled.code
  ⟨⟨0, layout⟩, ⟨compiled.tree.scope.context.path, ⟨layout, ⟨compiled.parameters, root.code⟩⟩⟩ ::
    root.children⟩

end Silmaril.Languages.Python.Compile.Closure.Link
