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
block's label with that field, so the block produces `7`. A second program (`ehBody2`) catches
with `catch_ref` and rethrows with `throw_ref`; a third (`ehBody3`) passes two parameters into an
`if` and into a `try_table` whose body throws one of them. The store has the one tag and no
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

/-- A rethrow through `catch_ref` and `throw_ref`:

```wat
(block (result exnref)
  (try_table (catch_ref $t 0)
    (throw $t (i32.const 7)))
  unreachable)
throw_ref
```

The clause pushes the field and the exception reference; the block keeps the reference, and
`throw_ref` throws the same exception `0` again. -/
def ehBody2 : List Binaryen.BExpr :=
  [.block (.value (.ref ⟨true, .abstract .exn⟩))
    [.tryTable .empty [.catchRef ⟨0⟩ ⟨0⟩] [.op (.throw ⟨0⟩) [.op (.intConst .i32 7) []]],
     .op .unreachable []],
   .op .throwRef []]

/-- The type `[i32 i32] → [i32]` of the multi-value blocks. -/
def ehPair : Validation.DefType :=
  V2.FuncType.toDefType ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩

/-- The module instance of the multi-value program: the type `0` is `ehPair`, the tag as before. -/
def ehMod3 : ModuleInst := { types := [ehPair], tags := [0] }

/-- The frame of the multi-value program. -/
def ehFrame3 : Frame := { module := ehMod3 }

/-- **Multi-value block parameters** for `if` and `try_table`:

```wat
(block (result i32)
  i32.const 1  i32.const 2
  (if (param i32 i32) (result i32) (i32.const 1)
    (then i32.add) (else i32.sub))        ;; 3
  i32.const 4
  (try_table (param i32 i32) (result i32) (catch $t 0)
    drop
    (throw $t)))                          ;; throws 3, caught: the block produces 3
```
-/
def ehBody3 : List Binaryen.BExpr :=
  [.block (.value (.num (.int .i32)))
    [.op (.intConst .i32 1) [], .op (.intConst .i32 2) [],
     .if_ (.typeIdx ⟨0⟩) [.op (.intConst .i32 1) []] [.op (.intBinOp .i32 .add) []]
       [.op (.intBinOp .i32 .sub) []],
     .op (.intConst .i32 4) [],
     .tryTable (.typeIdx ⟨0⟩) [.catch_ ⟨0⟩ ⟨0⟩] [.op .drop [], .op (.throw ⟨0⟩) []]]]

/-- The value `3`. -/
def v3 : Val := Binaryen.ofInt .i32 3

/-- The store after the multi-value run: the exception `0` with the field `3`. -/
def ehStore3 : Store Empty := ehStore.addExn ⟨0, [v3]⟩

/-- The empty oracle: nothing is called. -/
def ehC : Abstract.CallRel Empty := fun _ _ _ _ => False

end Silmaril.Wasm.Interp.ExampleEH
