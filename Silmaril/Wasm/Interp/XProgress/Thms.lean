module

public import Silmaril.Proofs.Wasm.Interp.XClassify
public import Silmaril.Proofs.Wasm.Interp.XIndRes

/-!
# Typed progress for the extended semantics: theorems

Facts towards the converse (Core → `EvalOX`) for the new call forms:

* `calleeX_flow`: a typed callee's closed answer returns, traps or throws;
* `callRef_top`, `returnCallRef_top`: at a `call_ref y`/`return_call_ref y` site typed in
  context, in an instance with valid types, the top of the stack is a null or a function
  reference of the store. Derived from the Core typing of the site (`AdminsOk` inversion), with
  the instance's valid types for a closed type context; no frame typing (`StateOk`) is needed.
* `indirect_res`: at a `call_indirect x y`/`return_call_indirect x y` site typed in context,
  the top of the stack is an index that resolves (`CallRes.IndRes`): the table exists (the site's
  frame is typed), and an entry passing the cast is null or a function reference, so the stuck
  case of `indRes_cases` cannot occur.
-/

public section

namespace Silmaril.Wasm.Interp.XProgress

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

variable {H : Type}

/-- **A typed callee's closed answer returns, traps or throws.** -/
theorem calleeX_flow {s s' : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {fl : Binaryen.Flow} (P : Numerics.Profile)
    (hS : StoreChkE tExt s.funcs) (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hE : TypedEntry s a us) (h : Abstract.XRecursion.closedCallX s a us (s', fl)) :
    (∃ vs, fl.retVals = some vs) ∨ fl = .trap ∨ ∃ t, fl = .throw t :=
  Silmaril.Wasm.Interp.calleeX_flow (P := P) hS hfi hcode hty hn hE h

/-- **The operand of a typed `call_ref y`** is a null or a function reference of the store. -/
theorem callRef_top {s : Store H} {f : Frame} {stk : List Val} {y : TypeIdx} {rest : List Admin}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain (.callRef y) :: rest⟩)
    (hm : Abstract.CallXT.TyTypes f.module) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧
      (r = .null ∨ ∃ (a : Nat) (fi : FuncInst H), r = .func a ∧ s.funcs[a]? = some fi) :=
  Silmaril.Wasm.Interp.callRef_top ht hm

/-- **The operand of a typed `return_call_ref y`** is a null or a function reference. -/
theorem returnCallRef_top {s : Store H} {f : Frame} {stk : List Val} {y : TypeIdx}
    {rest : List Admin}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain (.returnCallRef y) :: rest⟩)
    (hm : Abstract.CallXT.TyTypes f.module) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧
      (r = .null ∨ ∃ (a : Nat) (fi : FuncInst H), r = .func a ∧ s.funcs[a]? = some fi) :=
  Silmaril.Wasm.Interp.returnCallRef_top ht hm

/-- **A typed indirect call site resolves.** -/
theorem indirect_res {s : Store H} {f : Frame} {stk : List Val} {x : TableIdx} {y : TypeIdx}
    {rest : List Admin} {i : Instr} (hi : i = .callIndirect x y ∨ i = .returnCallIndirect x y)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩) :
    ∃ (ad : AddrType) (j : BitVec ad.intType.width) (stk' : List Val) (o : Option Nat),
      stk = .num ⟨.int ad.intType, j⟩ :: stk' ∧ Abstract.CallRes.IndRes s f x y ad j o :=
  Silmaril.Wasm.Interp.indirect_res hi ht

end Silmaril.Wasm.Interp.XProgress
