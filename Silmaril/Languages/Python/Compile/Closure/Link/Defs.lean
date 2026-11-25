module

public import Silmaril.Languages.Python.Compile.Closure.CodeNames.Emission
public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs

/-! # Link lowered Python closure bodies into a Core dispatch table

The entry function has key zero. Lexical preorder assigns dense keys to
nested declarations. A linked closure carries its child's code reference
and captures, with the child body stored in the code table.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.Link

open Source (BlockPath Scope ScopeTree)
open Core.Closure (CodeRef Layout)
open Core.Closure.Dispatch (CodeTable Entry ProfiledCodeNames)

structure Block where
  path : BlockPath
  entry : Entry Code

/-- Use the lexical path of the generated code block to select the analyzed
function. A class scope is outside the ordinary metadata profile. -/
def ordinaryScopeAt? (tree : ScopeTree) : (path : BlockPath) →
    Option {scope : Scope // tree.atPath path = some scope}
  | [] => if tree.scope.context.kind == .function then some ⟨tree.scope, rfl⟩ else none
  | index :: rest =>
    if tree.scope.context.kind == .class_ then none else
      match found : tree.children[index]? with
      | none => none
      | some child => ordinaryScopeAt? child rest
        |>.map fun ⟨scope, located⟩ => ⟨scope, by simp [ScopeTree.atPath, found, located]⟩

structure BlockFreeVars (tree : ScopeTree) (block : Block) where
  scope : Scope
  located : tree.atPath block.path = some scope
  codeLayout : block.entry.layout = frameLayout scope
  names : List Source.Name
  profile : FreeVarProfile scope
  exactNames : names = freeVarNames scope

def blockScope? (tree : ScopeTree) (block : Block) : Option {scope : Scope //
    tree.atPath block.path = some scope ∧ block.entry.layout = frameLayout scope} := do
  unless tree.scope.context.kind == .module_ do none
  let scope ← ordinaryScopeAt? tree block.path
  if layout : block.entry.layout = frameLayout scope.val then
    return ⟨scope.val, scope.property, layout⟩
  else none

def blockFreeVars? (tree : ScopeTree) (block : Block) : Option (BlockFreeVars tree block) := do
  let ⟨scope, located, layout⟩ ← blockScope? tree block
  let ⟨names, profile, exactNames⟩ ← freeVarNames? scope
  return ⟨scope, located, layout, names, profile, exactNames⟩

structure BlockCellVars (tree : ScopeTree) (block : Block) where
  scope : Scope
  located : tree.atPath block.path = some scope
  codeLayout : block.entry.layout = frameLayout scope
  names : List Source.Name
  profile : CellVarProfile scope
  exactNames : names = cellVarNames scope

def blockCellVars? (tree : ScopeTree) (block : Block) : Option (BlockCellVars tree block) := do
  let ⟨scope, located, layout⟩ ← blockScope? tree block
  let ⟨names, profile, exactNames⟩ ← cellVarNames? scope
  return ⟨scope, located, layout, names, profile, exactNames⟩

structure BlockCodeNames (tree : ScopeTree) (block : Block) where
  scope : Scope
  located : tree.atPath block.path = some scope
  codeLayout : block.entry.layout = frameLayout scope
  operations : List CodeNames.Operation
  emitted : CodeNames.operations? block.entry.definition.body = some operations

def blockCodeNames? (tree : ScopeTree) (block : Block) : Option (BlockCodeNames tree block) := do
  let ⟨scope, located, layout⟩ ← blockScope? tree block
  match emitted : CodeNames.operations? block.entry.definition.body with
  | none => none
  | some operations => return ⟨scope, located, layout, operations, emitted⟩

/-- Attach only the metadata checked against this block's source scope and
layout. The code reference, parameters and body are independent of the tuple. -/
def Block.withFreeVars (block : Block) (tree : ScopeTree) : Block :=
  { block with entry := { block.entry with definition := { block.entry.definition with
    freevars := (blockFreeVars? tree block).map (·.names) } } }

def Block.withCellVars (block : Block) (tree : ScopeTree) : Block :=
  { block with entry := { block.entry with definition := { block.entry.definition with
    cellvars := (blockCellVars? tree block).map (·.names) } } }

def Block.withCodeNames (block : Block) (tree : ScopeTree) : Block :=
  { block with entry := { block.entry with definition := { block.entry.definition with
    codeNames := (blockCodeNames? tree block).map fun checked =>
      ⟨.cpython3135ExecOptimize0, CodeNames.names .cpython3135 checked.operations⟩ } } }

structure LinkedBody (layout : Layout) where
  code : Code layout
  children : List Block

/-- `first` is the key available for the next nested declaration. -/
def linkBody {layout : Layout} (first : Nat) (tree : ScopeTree) : Body.Code layout → LinkedBody layout
  | .ret value => ⟨.ret value, []⟩
  | .assert test rest =>
    let tail := linkBody first tree rest
    ⟨.assert test tail.code, tail.children⟩
  | .assertFreeVars receiver needle expected rest =>
    let tail := linkBody first tree rest
    ⟨.assertFreeVars receiver needle expected tail.code, tail.children⟩
  | .assertCellVars receiver needle rest =>
    let tail := linkBody first tree rest
    ⟨.assertCellVars receiver needle tail.code, tail.children⟩
  | .assertCodeNames receiver needle rest =>
    let tail := linkBody first tree rest
    ⟨.assertCodeNames receiver needle tail.code, tail.children⟩
  | .discardCall callee rest =>
    let tail := linkBody first tree rest
    ⟨.discardCall callee tail.code, tail.children⟩
  | .assign slot value rest =>
    let tail := linkBody first tree rest
    ⟨.assign slot value tail.code, tail.children⟩
  | .closure slot path childLayout parameters captures child rest =>
    let nested := linkBody (first + 1) tree child
    let tail := linkBody (first + 1 + nested.children.length) tree rest
    let entry : Entry Code := ⟨childLayout, { parameters, body := nested.code }⟩
    ⟨.closure slot path ⟨first, childLayout⟩ captures tail.code,
      (((Block.mk path entry).withFreeVars tree).withCellVars tree).withCodeNames tree :: (nested.children ++ tail.children)⟩

structure Program where
  entry : CodeRef
  blocks : List Block

def Program.table (program : Program) : CodeTable Code :=
  fun key => program.blocks[key]?.map Block.entry

def Program.entryFreeVars (program : Program) : Option (List Source.Name) :=
  program.blocks[program.entry.key]?.bind (·.entry.definition.freevars)

def Program.entryCellVars (program : Program) : Option (List Source.Name) :=
  program.blocks[program.entry.key]?.bind (·.entry.definition.cellvars)

def Program.entryCodeNames (program : Program) : Option ProfiledCodeNames :=
  program.blocks[program.entry.key]?.bind (·.entry.definition.codeNames)

def Program.references (program : Program) : List (BlockPath × CodeRef) :=
  program.blocks.flatMap (fun block => block.entry.definition.body.references)

def link {source : Source.Module} (compiled : Body.Compiled source) : Program :=
  let layout := frameLayout compiled.tree.scope
  let root := linkBody 1 compiled.moduleTree compiled.code
  let entry : Entry Code := ⟨layout, { parameters := compiled.parameters, body := root.code }⟩
  let block := ((Block.mk compiled.tree.scope.context.path entry).withFreeVars compiled.moduleTree)
    |>.withCellVars compiled.moduleTree
    |>.withCodeNames compiled.moduleTree
  ⟨⟨0, layout⟩, block :: root.children⟩

end Silmaril.Languages.Python.Compile.Closure.Link
