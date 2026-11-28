module

public import Silmaril.SSA.PEG.Projection.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Automatic.Defs

/-! # Graph-only two-level reversion after removing dead rows

Keep the designated return and every eval for the outer loop and its
sole child, with the complete operand closure of those seeds. Loop
keys and parent entries are retained verbatim. The existing graph-only
reverter must accept the resulting full table.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n l : Nat}

structure Accepted (g : Graph P outer [result] n l) where
  projection : g.Projection
  core : Reindexed.Automatic.Accepted projection.graph

def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P outer [result] n l) : Option (Accepted g) := do
  let cached := Automatic.cacheRows g
  let root := cached.roots.get .head
  let some outerKey := Automatic.evalLoop (cached.node root.id).label | none
  let some childKey := Automatic.soleChild cached.forest outerKey | none
  let anchors := Automatic.bundleIds cached outerKey ++ Automatic.bundleIds cached childKey
  let some rows := Projection.dependencyRows cached anchors | none
  let some projection := g.checkProjection rows | none
  let some core := Reindexed.Automatic.extract projection.graph | none
  return ⟨projection, core⟩

variable {g : Graph P outer [result] n l}

def Accepted.revert (a : Accepted g) : Program P true outer result :=
  a.core.revert

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected
