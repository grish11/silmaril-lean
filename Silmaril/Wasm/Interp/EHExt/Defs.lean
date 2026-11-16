module

public import Silmaril.Wasm.Interp.Defs

/-!
# The arity checker extension with exceptions (F5)

`ehExt tags` extends the tail checker's descriptor (`tExt`, the five call forms) with the
exception forms, for a store whose tag instances are `tags` (they do not change at run time):

* `throw x`: never falls through after popping the tag's fields (`tagFields`, read off the tag
  instance's function type `[ts] → []`);
* `throw_ref`: never falls through after popping the reference;
* `try_table bt cs _`: its clauses push their tag's fields (`catch`), the fields and the
  exception reference (`catch_ref`), nothing (`catch_all`) or the reference (`catch_all_ref`)
  (`clauseCount`); `chk1E` checks each against its label's arity (`catchOk`).

Every other instruction gets `tExt`'s answer (`ehExt_of_not_eh`), so on exception-free code the
two checks coincide. Theorems in `Silmaril.Wasm.Interp.EHExt.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The number of fields of the tag `x` of an instance, in a store with tag instances `tags`. -/
def tagFields (tags : List TagInst) (mi : ModuleInst) (x : TagIdx) : Option Nat := do
  let ta ← mi.tags[x.toNat]?
  let ti ← tags[ta]?
  match Validation.DefType.funcType? ti.type with
  | some (ps, []) => some ps.length
  | _ => none

/-- The values a handler clause pushes. -/
def clauseCount (tags : List TagInst) (mi : ModuleInst) : Catch → Option Nat
  | .catch_ x _ => tagFields tags mi x
  | .catchRef x _ => (tagFields tags mi x).map (· + 1)
  | .catchAll _ => some 0
  | .catchAllRef _ => some 1

end Silmaril.Wasm.Interp
