module

public import Silmaril.Wasm.Abstract.XRecursionP.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# Tail calls inside handlers

Example for the pending tail calls (`Silmaril.Wasm.Abstract.CallXP`). The **original** module

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

is **not valid** Wasm (`tModuleOld`, rejected by `Validation.validate?`): `$caller`'s
`try_table` has the empty block type but its body leaves `$thrower`'s `i32`, and `$nuller`'s
`return_call_ref $r` is applied to a `funcref`, not a `(ref null $r)`. Its store `tStore` also
fails the arity checker (`ehExt`), on `$caller`. The closure's answers on it are still recorded
(they do not depend on typing), as a regression.

The **corrected** module `tModuleV` (validated) replaces those two functions:

```wat
(func $caller (type $r)                                               ;; function 2
  (block (result i32) (try_table (result i32) (catch $t 0) (call $thrower)) unreachable))
(func $nuller (type $r) (local $n (ref null $r))                      ;; function 3
  (block (result i32) (try_table (catch $t 0) (return_call_ref $r (local.get $n))) unreachable))
```

and `tStoreV` is its store (the same tag, type and instance as `tStore`):

* `$tailer`: the tail call leaves the handler before `$thrower` runs, so `$thrower`'s exception
  is **not** caught: `$tailer` throws.
* `$caller`: an ordinary call runs inside the handler, so the exception is caught and branches
  to the block with its field: `$caller` returns `9`.
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

/-! ## The corrected, validated module -/

/-- `$caller` with a `try_table` of result `i32`. -/
def callerV : Func :=
  ⟨⟨0⟩, [], [.block (.value (.num (.int .i32)))
    [.tryTable (.value (.num (.int .i32))) [.catch_ ⟨0⟩ ⟨0⟩] [.call ⟨0⟩], .unreachable]]⟩

/-- `$nuller` with a local of type `(ref null $r)`. -/
def nullerV : Func :=
  ⟨⟨0⟩, [.ref ⟨true, .typeIdx ⟨0⟩⟩], guarded [.localGet ⟨0⟩, .returnCallRef ⟨0⟩]⟩

/-- The source module with the given functions: the types `$r = [] → [i32]` (index 0) and
`[i32] → []` (index 1), and the tag `$t` of type 1. -/
def tModule (fs : List Func) : Module where
  types := [⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[.num (.int .i32)], []⟩⟩]⟩]
  tags := [⟨1⟩]
  funcs := fs

/-- The original module (not valid). -/
def tModuleOld : Module := tModule [thrower, tailer, caller, nuller]

/-- The corrected module (valid). -/
def tModuleV : Module := tModule [thrower, tailer, callerV, nullerV]

/-- The store of the corrected module: the tag and the four functions. -/
def tStoreV : Store Empty :=
  { tags := [tTag],
    funcs := [⟨tTy, tMod, .wasm thrower⟩, ⟨tTy, tMod, .wasm tailer⟩, ⟨tTy, tMod, .wasm callerV⟩,
      ⟨tTy, tMod, .wasm nullerV⟩] }

/-- The corrected store after `$thrower` ran: the exception `0` with the field `9`. -/
def tStoreV' : Store Empty := tStoreV.addExn ⟨0, [v9]⟩

end Silmaril.Wasm.Interp.ExampleTailEH
