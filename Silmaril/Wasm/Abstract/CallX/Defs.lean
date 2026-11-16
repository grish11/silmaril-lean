module

public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Abstract.CallRes.Defs
public import Silmaril.Wasm.Abstract.StoreCall.Defs

/-!
# Indirect, reference and tail calls, with an oracle (F4, call forms)

`EvalOX C` extends `Silmaril.Wasm.Abstract.Recursion.EvalO C` by the call forms
`EvalO` (and the native interpreter) have no rule for, each resolved as Core
3.0 resolves it and then answered by the same call oracle `C : CallRel H`:

* `call_indirect x y`: the index on top of the stack, resolved by
  `CallRes.IndRes` (`table.get; ref.cast (ref null y)`); a resolved callee is
  called at its own type, as `call_ref` does (`callIndOk`, `callIndStop`); an
  unresolved index traps (`callIndRes`);
* `call_ref y`: a function reference on top is called (`callRefOk`,
  `callRefStop`), null traps (`callRefNull`);
* tail calls `return_call x`, `return_call_indirect x y`, `return_call_ref y`
  (`TailRes`): the callee runs in place of the caller and its result ends the
  caller with a return (`tail`, `tailFlow`), as Core 3.0's
  `return_call_ref-frame-addr` hands the callee the caller's frame; an
  unresolved tail callee traps (`tailRes`). The caller's frame is replaced, so
  the callee's results become the caller's (`.ret` of the callee's result
  arity); on typed code the two arities agree, as Core 3.0 validation of
  `return_call*` requires.

Every rule of `EvalO` is a rule of `EvalOX`. Code without the new call forms
(`xFree`) runs in `EvalOX C` exactly as in `EvalO C`
(`Silmaril.Wasm.Abstract.CallX.Thms`): the direct part is `EvalO`, not a second
copy of it.

Host imports are not resolved here (the oracle answers every call).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.CallX

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)

variable {H : Type}

/-- Flows that end a call abruptly: traps and exceptions. -/
def _root_.Silmaril.Wasm.Binaryen.Flow.Abrupt : Flow → Prop
  | .trap | .throw _ => True
  | _ => False

/-- The operands a tail call consumes before its arguments: the table index of
`return_call_indirect`, the reference of `return_call_ref`. -/
def tailPop : Instr → Nat
  | .returnCallIndirect _ _ | .returnCallRef _ => 1
  | _ => 0

/-- The resolution of a tail call on the stack `stk` (top first): the callee
address and the argument stack, or a trap (`none`). -/
inductive TailRes (s : Store H) (f : Frame) : Instr → List Val → Option (Nat × List Val) → Prop
  /-- `return_call x`. -/
  | direct {x : FuncIdx} {a : Nat} {fi : FuncInst H} {stk : List Val}
      (hfi : s.func? f x = some (a, fi)) : TailRes s f (.returnCall x) stk (some (a, stk))
  /-- `return_call_indirect x y`, resolved. -/
  | indirect {x : TableIdx} {y : TypeIdx} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {stk : List Val} (hres : CallRes.IndRes s f x y ad i (some fa)) :
      TailRes s f (.returnCallIndirect x y) (.num ⟨.int ad.intType, i⟩ :: stk) (some (fa, stk))
  /-- `return_call_indirect x y`, unresolved. -/
  | indirectTrap {x : TableIdx} {y : TypeIdx} {ad : AddrType} {i : BitVec ad.intType.width}
      {stk : List Val} (hres : CallRes.IndRes s f x y ad i none) :
      TailRes s f (.returnCallIndirect x y) (.num ⟨.int ad.intType, i⟩ :: stk) none
  /-- `return_call_ref y` on a function reference. -/
  | ref {y : TypeIdx} {fa : Nat} {stk : List Val} :
      TailRes s f (.returnCallRef y) (.ref (.func fa) :: stk) (some (fa, stk))
  /-- `return_call_ref y` on null. -/
  | refNull {y : TypeIdx} {stk : List Val} : TailRes s f (.returnCallRef y) (.ref .null :: stk) none

/-- The caller's flow after a tail call whose callee body ended with `fl`: its
`n` result values returned, or the callee's trap or exception. -/
def tailFlow (n : Nat) : Flow → Flow
  | .normal vs | .ret vs | .brk 0 vs => .ret (vs.take n)
  | .trap => .trap
  | .throw t => .throw t
  | .brk (_ + 1) _ => .trap

/-- **The extended oracle relation**: `EvalO`'s rules, and the indirect,
reference and tail call forms, every call answered by `C`. -/
inductive EvalOX (C : CallRel H) : Store H → Frame → List Val → List BExpr → Store H × Frame × Flow → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalOX C s f stk [] (s, f, .normal stk)
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {fl : Flow} (hargs : EvalOX C s f stk args (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOX C s f stk (.op i args :: es) (s₁, f₁, fl)
  | callOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
      (hvs : fl.retVals = some vs)
      (hk : EvalOX C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOX C s f stk (.op (.call x) args :: es) r
  | callTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
      EvalOX C s f stk (.op (.call x) args :: es) (s₂, f₁, .trap)
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {t : Nat}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
      EvalOX C s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {r : Store H × Frame × Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalOX C s₂ f₂ stk₂ es r) :
      EvalOX C s f stk (.op i args :: es) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOX C s f stk (.op i args :: es) (s₂, f₂, fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX C s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOX C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOX C s f stk (.block bt body :: es) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOX C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalOX C s f stk (.block bt body :: es) (s₁, f₁, .brk k vs)
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalOX C s f stk (.block bt body :: es) (s₁, f₁, fl)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX C s f (stk.take np) body (s₁, f₁, .normal vs))
      (hk : EvalOX C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOX C s f stk (.loop bt body :: es) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX C s f (stk.take np) body (s₁, f₁, .brk 0 vs))
      (hk : EvalOX C s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
      EvalOX C s f stk (.loop bt body :: es) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOX C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalOX C s f stk (.loop bt body :: es) (s₁, f₁, .brk k vs)
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalOX C s f stk (.loop bt body :: es) (s₁, f₁, fl)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hc : EvalOX C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOX C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOX C s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
      EvalOX C s f stk (.if_ bt c t el :: es) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat}
      (hc : EvalOX C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOX C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .brk (k + 1) vs)) :
      EvalOX C s f stk (.if_ bt c t el :: es) (s₂, f₂, .brk k vs)
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : EvalOX C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOX C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl)) (hfl : fl.Escapes) :
      EvalOX C s f stk (.if_ bt c t el :: es) (s₂, f₂, fl)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {fl : Flow}
      (hc : EvalOX C s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOX C s f stk (.if_ bt c t el :: es) (s₁, f₁, fl)

  /-- `call_indirect x y`: the callee resolved (`CallRes.IndRes`), then a returning call. -/
  | callIndOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOX C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOX C s f stk (.op (.callIndirect x y) args :: es) r
  /-- `call_indirect x y` that does not resolve: a trap. -/
  | callIndRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
      {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i none) :
      EvalOX C s f stk (.op (.callIndirect x y) args :: es) (s₁, f₁, .trap)
  /-- `call_indirect x y` whose callee traps or throws. -/
  | callIndStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOX C s f stk (.op (.callIndirect x y) args :: es) (s₂, f₁, fl)
  /-- `call_ref y` on a function reference: a returning call. -/
  | callRefOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOX C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOX C s f stk (.op (.callRef y) args :: es) r
  /-- `call_ref y` on null: a trap. -/
  | callRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal (.ref .null :: stk₁))) :
      EvalOX C s f stk (.op (.callRef y) args :: es) (s₁, f₁, .trap)
  /-- `call_ref y` whose callee traps or throws. -/
  | callRefStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOX C s f stk (.op (.callRef y) args :: es) (s₂, f₁, fl)
  /-- A tail call (`return_call`, `return_call_indirect`, `return_call_ref`) to a
  resolved callee: the callee's values (or abrupt flow) end the caller with a
  return. -/
  | tail {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal stk₁))
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa ((stk₁.drop (tailPop i)).take ps.length).reverse (s₂, fl))
      (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) :
      EvalOX C s f stk (.op i args :: es) (s₂, f₁, tailFlow rs.length fl)
  /-- A tail call that does not resolve: a trap. -/
  | tailRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr}
      (hargs : EvalOX C s f stk args (s₁, f₁, .normal stk₁)) (hres : TailRes s₁ f₁ i stk₁ none) :
      EvalOX C s f stk (.op i args :: es) (s₁, f₁, .trap)


/-- Every `EvalO` rule is an `EvalOX` rule. -/
theorem EvalOX.of_evalO {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalO C s f stk es r) :
    EvalOX C s f stk es r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ => exact .callOk ih₁ hfi hty hcall hvs ih₂
  | callTrap _ hfi hty hcall ih => exact .callTrap ih hfi hty hcall
  | callThrow _ hfi hty hcall ih => exact .callThrow ih hfi hty hcall
  | opOk hi _ hflat _ ih₁ ih₂ => exact .opOk hi ih₁ hflat ih₂
  | opStop hi _ hflat hfl ih => exact .opStop hi ih hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ => exact .blockOk har ih₁ hvs ih₂
  | blockBrk har _ ih => exact .blockBrk har ih
  | blockEsc har _ hfl ih => exact .blockEsc har ih hfl
  | loopOk har _ _ ih₁ ih₂ => exact .loopOk har ih₁ ih₂
  | loopBack har _ _ ih₁ ih₂ => exact .loopBack har ih₁ ih₂
  | loopBrk har _ ih => exact .loopBrk har ih
  | loopEsc har _ hfl ih => exact .loopEsc har ih hfl
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ => exact .ifOk ih₁ hb har ih₂ hvs ih₃
  | ifBrk _ hb har _ ih₁ ih₂ => exact .ifBrk ih₁ hb har ih₂
  | ifEsc _ hb har _ hfl ih₁ ih₂ => exact .ifEsc ih₁ hb har ih₂ hfl
  | ifAbort _ hfl ih => exact .ifAbort ih hfl

/-- The extended call forms. -/
def isXCall : Instr → Bool
  | .callIndirect _ _ | .callRef _ | .returnCall _ | .returnCallIndirect _ _
  | .returnCallRef _ => true
  | _ => false

mutual

/-- No extended call form in the tree. -/
def xFree : BExpr → Bool
  | .op i args => !isXCall i && xFreeL args
  | .block _ body => xFreeL body
  | .loop _ body => xFreeL body
  | .if_ _ c t e => xFreeL c && xFreeL t && xFreeL e
  | .tryTable _ _ body => xFreeL body

/-- `xFree` on every tree of a list. -/
def xFreeL : List BExpr → Bool
  | [] => true
  | e :: es => xFree e && xFreeL es

end

/-! ## The exposed body of the extended call forms

As in `StoreCall`, a call is a visible event `(callee, args, store)` of
`CallSig H`. The extended forms first resolve their callee as `EvalOX` does,
classically (`resolveInd`, `resolveTail`: the unique resolution, or none), then
make the same call event; a tail call ends the caller with the callee's result
(`tailAns`). -/

section Exposed

open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.Body (getState setState trap callImport)

/-- The indirect-call resolution of a stack (top first): the resolution and the
stack below the index. -/
def IndResS (s : Store H) (f : Frame) (x : TableIdx) (y : TypeIdx) (stk : List Val) :
    Option Nat × List Val → Prop := fun p =>
  ∃ (ad : AddrType) (i : BitVec ad.intType.width), stk = .num ⟨.int ad.intType, i⟩ :: p.2 ∧
    CallRes.IndRes s f x y ad i p.1

open Classical in
/-- The resolution of `call_indirect x y` on a stack, if any. -/
noncomputable def resolveInd (s : Store H) (f : Frame) (x : TableIdx) (y : TypeIdx)
    (stk : List Val) : Option (Option Nat × List Val) :=
  if h : ∃ p, IndResS s f x y stk p then some (Classical.choose h) else none

open Classical in
/-- The resolution of a tail call on a stack, if any. -/
noncomputable def resolveTail (s : Store H) (f : Frame) (i : Instr) (stk : List Val) :
    Option (Option (Nat × List Val)) :=
  if h : ∃ o, TailRes s f i stk o then some (Classical.choose h) else none

/-- A call event to the function at address `fa`, its answer read as `EvalO`'s
call rules read their oracle. -/
noncomputable def callAt (fa : Nat) (f : Frame) (stk : List Val) : M (CallSig H) H Res :=
  getState >>= fun s =>
    match s.down.funcs[fa]? with
    | some fi =>
      match Validation.DefType.funcType? fi.type with
      | some (ps, rs) =>
        callImport (E := CallSig H) (fa, (stk.take ps.length).reverse, s.down) >>= fun ans =>
          callAns f stk ps rs ans.down
      | none => stuck
    | none => stuck

/-- The answer of a tail call: the callee's result values return from the caller. -/
noncomputable def tailAns (f : Frame) (rs : List Validation.CValType) :
    Store H × Flow → M (CallSig H) H Res
  | (_, .trap) => trap ⟨⟩
  | (s₂, .throw t) => setState ⟨s₂⟩ >>= fun _ => pure ⟨(f, .throw t)⟩
  | (s₂, fl) =>
    match fl.retVals with
    | some vs => setState ⟨s₂⟩ >>= fun _ => pure ⟨(f, .ret (vs.take rs.length))⟩
    | none => stuck

/-- A tail call event to the function at address `fa`. -/
noncomputable def tailAt (fa : Nat) (f : Frame) (stk : List Val) : M (CallSig H) H Res :=
  getState >>= fun s =>
    match s.down.funcs[fa]? with
    | some fi =>
      match Validation.DefType.funcType? fi.type with
      | some (ps, rs) =>
        callImport (E := CallSig H) (fa, (stk.take ps.length).reverse, s.down) >>= fun ans =>
          tailAns f rs ans.down
      | none => stuck
    | none => stuck

/-- `call_indirect x y`, exposed. -/
noncomputable def indEv (x : TableIdx) (y : TypeIdx) (f : Frame) (stk : List Val) :
    M (CallSig H) H Res :=
  getState >>= fun s =>
    match resolveInd s.down f x y stk with
    | some (some fa, stk₁) => callAt fa f stk₁
    | some (none, _) => trap ⟨⟩
    | none => stuck

/-- `call_ref y`, exposed. -/
noncomputable def refEv (f : Frame) : List Val → M (CallSig H) H Res
  | .ref (.func fa) :: stk₁ => callAt fa f stk₁
  | .ref .null :: _ => trap ⟨⟩
  | _ => stuck

/-- A tail call, exposed. -/
noncomputable def tailEv (i : Instr) (f : Frame) (stk : List Val) : M (CallSig H) H Res :=
  getState >>= fun s =>
    match resolveTail s.down f i stk with
    | some (some (fa, stk₁)) => tailAt fa f stk₁
    | some none => trap ⟨⟩
    | none => stuck

/-- An operator, exposed: every call form makes a call event, other operators are
the lifted primitive. -/
noncomputable def opCX (i : Instr) (f : Frame) (stk : List Val) : M (CallSig H) H Res :=
  match i with
  | .call x => callEv x f stk
  | .callIndirect x y => indEv x y f stk
  | .callRef _ => refEv f stk
  | .returnCall _ | .returnCallIndirect _ _ | .returnCallRef _ => tailEv i f stk
  | _ => flatK i f stk

mutual

/-- The exposed abstract body of a folded tree, all call forms as events. -/
noncomputable def denX : BExpr → Frame → List Val → M (CallSig H) H Res
  | .op i args, f, stk => denListX args f stk >>= thenK (opCX i)
  | .block bt body, f, stk =>
    match arity f bt with
    | some (np, nr) => denListX body f (stk.take np) >>= blockK np nr stk
    | none => stuck
  | .loop bt body, f, stk =>
    Silmaril.Elgot.iter (fun c : ULift.{1} (Frame × List Val) =>
      match arity c.down.1 bt with
      | some (np, nr) => denListX body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
      | none => stuck) ⟨(f, stk)⟩
  | .if_ bt c t el, f, stk =>
    denListX c f stk >>= fun r =>
      match r with
      | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
        match truthy cv, arity f₁ bt with
        | some b, some (np, nr) =>
          (if b then denListX t f₁ (stk₁.take np) else denListX el f₁ (stk₁.take np)) >>=
            blockK np nr stk₁
        | _, _ => stuck
      | ⟨(_, .normal [])⟩ => stuck
      | r => pure r
  | .tryTable .., _, _ => stuck

/-- The exposed abstract body of a list of trees. -/
noncomputable def denListX : List BExpr → Frame → List Val → M (CallSig H) H Res
  | [], f, stk => pure ⟨(f, .normal stk)⟩
  | e :: es, f, stk => denX e f stk >>= thenK (denListX es)

end

/-- The body of one loop iteration, exposed. -/
noncomputable def loopBodyX (bt : BlockType) (body : List BExpr) :
    ULift.{1} (Frame × List Val) → M (CallSig H) H (Res ⊕ ULift.{1} (Frame × List Val)) :=
  fun c =>
    match arity c.down.1 bt with
    | some (np, nr) => denListX body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
    | none => stuck

end Exposed

end Silmaril.Wasm.Abstract.CallX
