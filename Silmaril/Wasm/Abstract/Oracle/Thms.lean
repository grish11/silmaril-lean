module

public import Silmaril.Wasm.Abstract.Closing.Thms
import Silmaril.Proofs.Wasm.Abstract.Closing.Oracle

/-!
# The call oracle `CallRel` and its closed instance against Core 3.0

**Conventions of `CallRel H`** (`Silmaril.Wasm.Abstract.Recursion.Defs`), as
`EvalO` uses them:

* `C s a us (s', fl)`. `a` is the callee address, from `s.func? f x` for a
  direct call. `us` are the arguments **in parameter order**: `EvalO` passes
  `(stk.take ps.length).reverse` of its top-first stack. `s'` is the store the
  call leaves.
* `fl` is the callee's **raw body flow**, its values **top-first**. The caller
  continues when `fl.retVals = some vs` (normal, `return`, or a branch to the
  body label) with `vs.take rs.length` pushed top-first, i.e.
  `(vs.take rs.length).reverse` in bottom-first order. `.trap` and `.throw t`
  propagate. Every other flow (`brk (k + 1)`) has no caller rule.
* The function type comes from `DefType.funcType? fi.type = some (ps, rs)`.
  `EvalO` does **not** check `stk.length ≥ ps.length` (it truncates with
  `take`); typing guarantees it. Requiring `us.length = ps.length` is stricter,
  and agrees on typed code.
* The oracle, not the call rule, decides what a callee is: `closedCall` has no
  entry for host functions (`bodyCall` requires `.wasm` code).

**The closed instance against Core 3.0** (closed host; typed, native,
arity-checked stores; every profile):

* `closedCall_core_iff`: `closedCall s a us (s', bfl)`, read through
  `exitFlow rs.length` (the top `rs.length` values, in result order), is
  exactly a Core run of `invoke s a us` to a result with final store `s'`;
* `closedCall_none_iff_diverges`: no such entry is exactly Core divergence.

So `C := closedCall` needs no assumed adequacy hypothesis on this slice.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The closed oracle is Core 3.0 call semantics**, final store included. -/
theorem closedCall_core_iff {s : Store H} {a : Nat} {us : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a us) (P : Numerics.Profile) (r : Result) (s' : Store H) :
    (∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (bfl fl : Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      closedCall s a us (s', bfl) ∧ exitFlow rs.length bfl = some fl ∧
      flowBeh fl = some r.toBehaviour) ↔
      ∃ c : Config H, Steps P closedHost (invoke s a us) c ∧ c.code = r.toAdmin ∧ c.store = s' :=
  Silmaril.Proofs.Wasm.Abstract.Closing.closedCall_core_iff hs hF hS hok P r s'

/-- **No closed-oracle entry is Core 3.0 divergence.** -/
theorem closedCall_none_iff_diverges {s : Store H} {a : Nat} {us : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a us) (P : Numerics.Profile) :
    (∀ (fi : FuncInst H) (ps rs : List Validation.CValType) (s' : Store H) (bfl : Flow),
      s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
      closedCall s a us (s', bfl) → exitFlow rs.length bfl = none) ↔
      Diverges P closedHost (invoke s a us) :=
  Silmaril.Proofs.Wasm.Abstract.Closing.closedCall_none_iff_diverges hs hF hS hok P

end Silmaril.Wasm.Abstract
