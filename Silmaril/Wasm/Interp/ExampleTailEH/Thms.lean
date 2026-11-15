module

public import Silmaril.Wasm.Interp.ExampleTailEH.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Thms
import Silmaril.Proofs.Wasm.Interp.ExampleTailEH

/-!
# Tail calls inside handlers: theorems

Answers of the closure with pending tail calls (`XRecursionP.closedCallXP`):

* `tailer_answer_iff`: `$tailer`'s **only** answer is `$thrower`'s exception. Its tail call passes
  the `try_table` untouched and is made when the frame is left, so the clause `catch $t 0` is
  **bypassed**.
* `caller_answer_iff`: `$caller`'s **only** answer is `9`. Its ordinary call throws inside the
  handler, which **catches** it.
* `nuller_answer`: `$nuller`'s tail call of null traps, through the handler.
-/

public section

namespace Silmaril.Wasm.Interp.ExampleTailEH

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.XRecursionP

/-- **The handler is bypassed by a tail call.** -/
theorem tailer_answer_iff {out : Store Empty × Binaryen.Flow} :
    closedCallXP tStore 1 [] out ↔ out = (tStore', .throw 0) :=
  ⟨Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tailer_answer_inv,
    fun h => h ▸ Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tailer_answer⟩

/-- **The handler catches an ordinary call's exception.** -/
theorem caller_answer_iff {out : Store Empty × Binaryen.Flow} :
    closedCallXP tStore 2 [] out ↔ out = (tStore', .normal [v9]) :=
  ⟨Silmaril.Proofs.Wasm.Interp.ExampleTailEH.caller_answer_inv,
    fun h => h ▸ Silmaril.Proofs.Wasm.Interp.ExampleTailEH.caller_answer⟩

/-- **A tail call of null traps**, through the handler. -/
theorem nuller_answer : closedCallXP tStore 3 [] (tStore, .trap) :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.nuller_answer

end Silmaril.Wasm.Interp.ExampleTailEH
