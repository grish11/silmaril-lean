module

public import Silmaril.Wasm.Interp.ExampleTailEH.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Thms
public import Silmaril.Wasm.Interp.PendSim.Thms
public import Silmaril.Wasm.Validation.Check.Validate
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

These hold of the original store `tStore`, whose module is **not valid**
(`tModuleOld_not_moduleValid`) and which fails the arity checker (`tStore_not_storeChk`). The
corrected module is valid (`tModuleV_moduleValid`); on its store `tStoreV` the same answers hold
(`tailer_answerV`, `caller_answerV`, `nuller_answerV`), and they are **Core 3.0 runs** of the calls,
in every profile, host, frame and `call_ref` form (from `PendSim.closedCallXP_sound`):

* `tailer_steps`: `$tailer` throws `$thrower`'s exception (the handler is bypassed: the tail call
  leaves it by `return_call_ref-handler` before `$thrower` runs);
* `caller_steps`: `$caller` returns `9` (the handler catches);
* `nuller_steps`: `$nuller` traps (Core's pending null tail call, at the frame).
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


/-! ## The original module is not valid; the corrected one is -/

/-- The original module is rejected by the validator. -/
theorem tModuleOld_invalid : Validation.validate? tModuleOld = none :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tModuleOld_invalid

/-- **The original module is not valid.** -/
theorem tModuleOld_not_moduleValid : ¬ Validation.ModuleValid tModuleOld :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tModuleOld_not_moduleValid

/-- **The corrected module is valid.** -/
theorem tModuleV_moduleValid : Validation.ModuleValid tModuleV :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tModuleV_moduleValid

/-- The original store fails the arity checker (on `$caller`). -/
theorem tStore_not_storeChk : ¬ Interp.StoreChkE (Interp.ehExt [tTag]) tStore.funcs :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tStore_not_storeChk

/-- The corrected store passes it. -/
theorem tStoreV_storeChk : Interp.StoreChkE (Interp.ehExt [tTag]) tStoreV.funcs :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tStoreV_storeChk

/-- The corrected store has the tag invariants. -/
theorem tStoreV_tagsOk : Interp.TagsOk [tTag] tStoreV :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tStoreV_tagsOk

/-! ## The closure's answers on the corrected store -/

theorem tailer_answerV : closedCallXP tStoreV 1 [] (tStoreV', .throw 0) :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tailer_answerV

theorem caller_answerV : closedCallXP tStoreV 2 [] (tStoreV', .normal [v9]) :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.caller_answerV

theorem nuller_answerV : closedCallXP tStoreV 3 [] (tStoreV, .trap) :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.nuller_answerV

/-! ## The Core 3.0 runs -/

variable {P : Numerics.Profile} {host : HostSemantics Empty}

/-- **`$tailer` throws `$thrower`'s exception in Core 3.0**: the handler is bypassed. -/
theorem tailer_steps (f : Frame) (c : Admin) (hc : c.IsCallRef) :
    Steps P host ⟨tStoreV, f, vals [] ++ [.ref (.func 1), c]⟩ ⟨tStoreV', f, throwing 0⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.tailer_steps f c hc

/-- **`$caller` returns `9` in Core 3.0**: the handler catches. -/
theorem caller_steps (f : Frame) (c : Admin) (hc : c.IsCallRef) :
    Steps P host ⟨tStoreV, f, vals [] ++ [.ref (.func 2), c]⟩ ⟨tStoreV', f, vals [v9]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.caller_steps f c hc

/-- **`$nuller` traps in Core 3.0**, at the frame. -/
theorem nuller_steps (f : Frame) (c : Admin) (hc : c.IsCallRef) :
    Steps P host ⟨tStoreV, f, vals [] ++ [.ref (.func 3), c]⟩ ⟨tStoreV, f, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Interp.ExampleTailEH.nuller_steps f c hc

end Silmaril.Wasm.Interp.ExampleTailEH
