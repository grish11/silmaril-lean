module

public import Silmaril.Languages.Python.Compile.Closure.Link.Defs

/-! # Resolve the name-table evidence for a linked function -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.CodeNames

open Core.Closure (CodeRef)
open Source (Name ScopeTree)

structure Evidence (tree : ScopeTree) (blocks : List Link.Block) (ref : CodeRef) where
  block : Link.Block
  found : blocks[ref.key]? = some block
  layout : block.entry.layout = ref.layout
  checked : Link.BlockCodeNames tree block

def Evidence.tuple {tree : ScopeTree} {blocks : List Link.Block} {ref : CodeRef}
    (evidence : Evidence tree blocks ref) (version : Version) : List Name :=
  names version evidence.checked.operations

/-- Use the same checked operations as the linker's stored tuple. -/
def checked? (tree : ScopeTree) (blocks : List Link.Block) (ref : CodeRef) :
    Option (Evidence tree blocks ref) := do
  match found : blocks[ref.key]? with
  | none => none
  | some block =>
    if layout : block.entry.layout = ref.layout then
      let checked ← Link.blockCodeNames? tree block
      return ⟨block, found, layout, checked⟩
    else none

end Silmaril.Languages.Python.Compile.Closure.CodeNames
