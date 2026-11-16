module

public import Silmaril.Wasm.Execution.Core.Step

/-!
# Resolving indirect calls, as Core 3.0 does (F4, call forms)

`call_indirect x y` on a table index `i` (an address-type constant) is, in Core
3.0, `table.get x; ref.cast (ref null y); call_ref y` (`Step_pure/call_indirect`).
`IndRes s f x y a i r` records the outcome of that chain before the call itself:

* `r = some fa`: the table entry is the function reference `fa` and the cast to
  `(ref null y)` succeeds; `call_ref` then calls `fa` at its own type;
* `r = none`: the call traps. The index is out of bounds (`table.get-oob`), the
  cast fails (`ref.cast-fail`), or the entry is null, which passes the nullable
  cast and traps in `call_ref` (`call_ref-null`).

An entry that passes the cast and is neither null nor a function reference has
no Core continuation (stuck); `IndRes` has no outcome for it.

This is the resolution shared by the indirect, reference and tail call forms;
the call it resolves to is the direct-call machinery (`Recursion.EvalO`'s call
oracle), which is the subject of `Silmaril.Wasm.Abstract.StoreCall`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.CallRes

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The reference type `call_indirect x y` casts to: `(ref null y)`. -/
def castTo (y : TypeIdx) : RefType := ⟨true, .typeIdx y⟩

/-- **The resolution of `call_indirect x y`** on the index `i`: the callee
address, or a trap (`none`). -/
inductive IndRes (s : Store H) (f : Frame) (x : TableIdx) (y : TypeIdx) (a : AddrType)
    (i : BitVec a.intType.width) : Option Nat → Prop
  /-- `table.get-oob`. -/
  | oob {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
      (h : ti.refs.length ≤ i.toNat) : IndRes s f x y a i none
  /-- `ref.cast-fail`. -/
  | castFail {ta : Nat} {ti : TableInst} {r : Ref} (ht : s.table? f x = some (ta, ti))
      (hr : ti.refs[i.toNat]? = some r) (hc : ¬ RefOk s r (f.module.instRef (castTo y))) :
      IndRes s f x y a i none
  /-- A null entry: the nullable cast succeeds, `call_ref-null` traps. -/
  | null {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
      (hr : ti.refs[i.toNat]? = some .null) (hc : RefOk s .null (f.module.instRef (castTo y))) :
      IndRes s f x y a i none
  /-- A function entry passing the cast: the callee. -/
  | func {ta : Nat} {ti : TableInst} {fa : Nat} (ht : s.table? f x = some (ta, ti))
      (hr : ti.refs[i.toNat]? = some (.func fa))
      (hc : RefOk s (.func fa) (f.module.instRef (castTo y))) :
      IndRes s f x y a i (some fa)

end Silmaril.Wasm.Abstract.CallRes
