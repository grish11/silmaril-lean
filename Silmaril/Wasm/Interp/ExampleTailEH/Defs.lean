module

public import Silmaril.Wasm.Abstract.XRecursionP.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# Tail calls inside handlers

Validated example for the pending tail calls (`Silmaril.Wasm.Abstract.CallXP`):

```wat
(tag $t (param i32))
(type $r (func (result i32)))
(func $thrower (type $r) (throw $t (i32.const 9)))                    ;; function 0
(func $tailer (type $r)                                               ;; function 1
  (block (result i32) (try_table (catch $t 0) (return_call $thrower)) unreachable))
(func $caller (type $r)                                               ;; function 2
  (block (result i32) (try_table (catch $t 0) (call $thrower)) unreachable))
(func $nuller (type $r) (local $n funcref)                            ;; function 3
  (block (result i32) (try_table (catch $t 0) (return_call_ref $r (local.get $n))) unreachable))
```

* `$tailer`: the tail call leaves the handler before `$thrower` runs, so `$thrower`'s exception
  is **not** caught: `$tailer` throws.
* `$caller`: an ordinary call runs inside the handler, so the exception is caught: `$caller`
  returns `9`.
* `$nuller`: a tail call of null traps (at the frame, in Core), through the handler.

Theorems in `Silmaril.Wasm.Interp.ExampleTailEH.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.ExampleTailEH

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The tag `$t : [i32] → []`. -/
def tTag : TagInst := ⟨V2.FuncType.toDefType ⟨[.num (.int .i32)], []⟩⟩

/-- The type `$r = [] → [i32]` of every function. -/
def tTy : Validation.DefType := V2.FuncType.toDefType ⟨[], [.num (.int .i32)]⟩

/-- The module instance. -/
def tMod : ModuleInst := { types := [tTy], tags := [0], funcs := [0, 1, 2, 3] }

/-- The `try_table` with the clause `catch $t 0` around `body`, in a block producing an `i32`. -/
def guarded (body : List Instr) : List Instr :=
  [.block (.value (.num (.int .i32))) [.tryTable .empty [.catch_ ⟨0⟩ ⟨0⟩] body, .unreachable]]

def thrower : Func := ⟨⟨0⟩, [], [.intConst .i32 9, .throw ⟨0⟩]⟩
def tailer : Func := ⟨⟨0⟩, [], guarded [.returnCall ⟨0⟩]⟩
def caller : Func := ⟨⟨0⟩, [], guarded [.call ⟨0⟩]⟩
def nuller : Func :=
  ⟨⟨0⟩, [.ref ⟨true, .abstract .func⟩], guarded [.localGet ⟨0⟩, .returnCallRef ⟨0⟩]⟩

/-- The store: the tag and the four functions. -/
def tStore : Store Empty :=
  { tags := [tTag],
    funcs := [⟨tTy, tMod, .wasm thrower⟩, ⟨tTy, tMod, .wasm tailer⟩, ⟨tTy, tMod, .wasm caller⟩,
      ⟨tTy, tMod, .wasm nuller⟩] }

/-- The value `9`. -/
def v9 : Val := Binaryen.ofInt .i32 9

/-- The store after `$thrower` ran: the exception `0` with the field `9`. -/
def tStore' : Store Empty := tStore.addExn ⟨0, [v9]⟩

end Silmaril.Wasm.Interp.ExampleTailEH
