module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot

open Silmaril.Semantics.Prolly (Block)

variable {Root Name Key Payload : Type}

structure Directory (Root Name Key Payload : Type) where
  arena : Indexed Name Key Payload
  roots : Root → Option (Handle Name)

namespace Directory

def empty : Directory Root Name Key Payload := ⟨.empty, fun _ => none⟩

structure Valid (directory : Directory Root Name Key Payload) : Prop where
  backward : ∀ (index : Nat) block, directory.arena.blocks[index]? = some block → Indexed.admissible index block = true
  live : ∀ root ref, directory.roots root = some ref → Indexed.KnownBefore directory.arena.blocks.size ref

/-- Set or insert one root by appending a proposed root block. The existing
snapshot is not edited. Aliases and child indices are not redirected. This
does not certify the new block's Prolly ordering or canonicality. -/
def copy? [DecidableEq Root] (directory : Directory Root Name Key Payload) (root : Root)
    (block : Block (Handle Name) Key Payload) : Option (Directory Root Name Key Payload × Nat) := do
  let (arena, index) ← directory.arena.append? block
  pure (⟨arena, fun query => if query = root then some (.local index) else directory.roots query⟩, index)

end Directory
end Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot
