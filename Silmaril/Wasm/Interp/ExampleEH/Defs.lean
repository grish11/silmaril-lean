module

public import Silmaril.Wasm.Interp.EHExt.Defs
public import Silmaril.Wasm.Abstract.CallXE.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# A caught exception

Validated example for the exception simulation (`Silmaril.Wasm.Interp.EHSim`):

```wat
(tag $t (param i32))
(block (result i32)
  (try_table (catch $t 0)
    (throw $t (i32.const 7)))
  unreachable)
```

The `throw` allocates the exception `0` with the field `7`; the clause `catch $t 0` branches to the
block's label with that field, so the block produces `7`. The store has the one tag and no
functions; nothing is called (`ehC`, the empty oracle).

Theorems in `Silmaril.Wasm.Interp.ExampleEH.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.ExampleEH

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The tag `$t : [i32] → []`. -/
def ehTag : TagInst := ⟨V2.FuncType.toDefType ⟨[.num (.int .i32)], []⟩⟩

/-- The store's tag instances. -/
def ehTags : List TagInst := [ehTag]

/-- The module instance: its tag `0` is the store's tag `0`. -/
def ehMod : ModuleInst := { tags := [0] }

/-- The store: the tag, no functions, no exceptions. -/
def ehStore : Store Empty := { tags := ehTags }

/-- The frame. -/
def ehFrame : Frame := { module := ehMod }

/-- The thrown value `7`. -/
def v7 : Val := Binaryen.ofInt .i32 7

/-- The code. -/
def ehBody : List Binaryen.BExpr :=
  [.block (.value (.num (.int .i32)))
    [.tryTable .empty [.catch_ ⟨0⟩ ⟨0⟩] [.op (.throw ⟨0⟩) [.op (.intConst .i32 7) []]],
     .op .unreachable []]]

/-- The store after the run: the exception `0`, of tag `0` with the field `7`. -/
def ehStore' : Store Empty := ehStore.addExn ⟨0, [v7]⟩

/-- The empty oracle: nothing is called. -/
def ehC : Abstract.CallRel Empty := fun _ _ _ _ => False

end Silmaril.Wasm.Interp.ExampleEH
