module

public import Silmaril.Wasm.Cfg.MachineL.Defs

/-!
# Pending, trap-answered and exception-answered calls (regression fixtures, definitions)

* `bodyCall`: `try_table (catch_all 0) (call 0)`: a call inside a handler;
* `bodyTail`: `try_table (catch_all 0) (return_call 0)`: a tail call inside a handler.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.ExamplePending

open Silmaril.Wasm

/-- Label `0`. -/
def l0 : LabelIdx := ⟨0, by decide⟩

/-- `try_table (catch_all 0) (call 0)`. -/
def bodyCall : Expr := [.tryTable .empty [.catchAll l0] [.call ⟨0⟩]]

/-- `try_table (catch_all 0) (return_call 0)`. -/
def bodyTail : Expr := [.tryTable .empty [.catchAll l0] [.returnCall ⟨0⟩]]

end Silmaril.Wasm.Cfg.ExamplePending
