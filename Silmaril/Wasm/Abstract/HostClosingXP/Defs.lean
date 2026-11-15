module

public import Silmaril.Wasm.Abstract.HostClosing.Defs
public import Silmaril.Wasm.Abstract.CallXP.Defs

/-!
# The canonical relation with host calls as an open module, closed by `Shape.close`

`Silmaril.Wasm.Abstract.HostClosing` reads the native relation `EvalL` (no exceptions in the
code, no extended call forms) as an open module `wasmHOpen` of the shape `wasmHShape H` (host
functions the only imports, every function a `self` call) and closes it with `Shape.close`.
This module does the same for the canonical relation `CallXP.EvalOXP` (exceptions, every call
form, tail calls pending until the frame is left), over the **same** shape and log type:

* `EvalLXPh s f stk es l r`: the logged relation of `EvalOXP`. Every call (`call`,
  `call_indirect`, `call_ref`; Wasm and host callees alike) is an open call recorded in the log
  `l : List (OCall H)` with an *arbitrary* answer, as in `EvalL`: returned values `inl ws`
  (result order; the caller continues on `ws.reverse` over the passive stack), or an exception
  `inr t`, raised at the call, inside the caller's handlers (so it may be caught). A pending tail
  call is a result (`POut.tail`), making no call in the body.
* `wasmHOpenXP`: a Wasm function's body runs in `EvalLXPh` in a fresh frame; a flow result ends
  the function through its exit flow (`exitFlow`, `endOfFlow`; an uncaught exception is
  `ret (inr t)`); a pending tail call `tail a' args n` makes **one open call** `(a', args)` at the
  frame, logged after the body's log, outside every handler, and the function ends as that call's
  answer does (`tailAns`: `tailFlow n` of the answer as a callee flow, as `CallXP.FrameP`). Host
  functions are exactly as in `wasmHOpen`. A tail call to a host function is the same open call,
  which the closure resolves to the host import event.
* `wasmEvFunXP := Shape.close wasmHOpenXP`.

**Cut calls.** `Shape.close` resolves a call whose callee traps by `Shape.Subst.intTrap`, which
needs a *finished* open behaviour of the caller through that call (with any answer, and anything
after it). `EvalL` always has one (an exception answer leaves every block of exception-free code),
but under a `try_table` every answer may be caught and lead to a run with no finished behaviour
(a loop around a handler catching everything). So each call also has a **cut** behaviour: the call
recorded with an answer of more values than the callee's result arity, the body then ending at
once in a trap (`callCut`, `indCut`, `refCut`). No behaviour of the closure returns such an answer
(a function returns at most its result arity), so a cut call is never resolved by a return
(`Shape.Subst.int`); it only lets the closure see a trapping (or diverging) callee. It contributes
no returning or throwing behaviour.

Theorems in `Silmaril.Wasm.Abstract.HostClosingXP.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes)
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- **The logged canonical relation**: `EvalOXP`'s rules, every call an open call recorded with an
arbitrary answer (values `inl ws` in result order, or an exception `inr t` raised at the call), or
cut (an answer of more values than the callee's arity, then a trap). -/
inductive EvalLXPh : Store H → Frame → List Val → List BExpr → List (OCall H) →
    Store H × Frame × POut → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} :
      EvalLXPh s f stk [] [] (s, f, .flow (.normal stk))
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {o : POut} {l : List (OCall H)} (hargs : EvalLXPh s f stk args l (s₁, f₁, o))
      (ho : ¬ o.IsNormal) :
      EvalLXPh s f stk (.op i args :: es) l (s₁, f₁, o)
  /-- `call x` answered by returned values. -/
  | callRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (OCall H)} {r : Store H × Frame × POut}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hk : EvalLXPh s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLXPh s f stk (.op (.call x) args :: es)
        (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) r
  /-- `call x` answered by an exception, raised at the call. -/
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {t : Nat} {l₁ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLXPh s f stk (.op (.call x) args :: es)
        (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr t) s₂]) (s₂, f₁, .flow (.throw t))
  /-- `call x`, cut: an answer no callee of the type returns, then a trap. -/
  | callCut {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hws : rs.length < ws.length) :
      EvalLXPh s f stk (.op (.call x) args :: es)
        (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]) (s₂, f₁, .flow .trap)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × POut}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalLXPh s₂ f₂ stk₂ es l₂ r) :
      EvalLXPh s f stk (.op i args :: es) (l₁ ++ l₂) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} {l : List (OCall H)} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalLXPh s f stk (.op i args :: es) l (s₂, f₂, .flow fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      {r : Store H × Frame × POut} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) (hk : EvalLXPh s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLXPh s f stk (.block bt body :: es) (l₁ ++ l₂) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (OCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalLXPh s f stk (.block bt body :: es) l (s₁, f₁, .flow (.brk k vs))
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {o : POut} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, o)) (ho : o.Escapes) :
      EvalLXPh s f stk (.block bt body :: es) l (s₁, f₁, o)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow (.normal vs)))
      (hk : EvalLXPh s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLXPh s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow (.brk 0 vs)))
      (hk : EvalLXPh s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ r) :
      EvalLXPh s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (OCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalLXPh s f stk (.loop bt body :: es) l (s₁, f₁, .flow (.brk k vs))
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {o : POut} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, o)) (ho : o.Escapes) :
      EvalLXPh s f stk (.loop bt body :: es) l (s₁, f₁, o)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (OCall H)} {r : Store H × Frame × POut}
      (hc : EvalLXPh s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPh s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, .flow fl))
      (hvs : fl.blockVals = some vs)
      (hk : EvalLXPh s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ r) :
      EvalLXPh s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat} {l₁ l₂ : List (OCall H)}
      (hc : EvalLXPh s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPh s₁ f₁ (stk₁.take np) (if b then t else el) l₂
        (s₂, f₂, .flow (.brk (k + 1) vs))) :
      EvalLXPh s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, .flow (.brk k vs))
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {o : POut} {l₁ l₂ : List (OCall H)}
      (hc : EvalLXPh s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPh s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, o))
      (ho : o.Escapes) :
      EvalLXPh s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, o)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {o : POut} {l : List (OCall H)}
      (hc : EvalLXPh s f stk c l (s₁, f₁, o)) (ho : ¬ o.IsNormal) :
      EvalLXPh s f stk (.if_ bt c t el :: es) l (s₁, f₁, o)
  /-- A resolved `call_indirect x y` answered by returned values. -/
  | indRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ l₂ : List (OCall H)}
      {r : Store H × Frame × POut}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hk : EvalLXPh s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLXPh s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) r
  /-- A resolved `call_indirect x y` answered by an exception, raised at the call. -/
  | indThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {t : Nat}
      {l₁ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPh s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr t) s₂])
        (s₂, f₁, .flow (.throw t))
  /-- A resolved `call_indirect x y`, cut. -/
  | indCut {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) (hws : rs.length < ws.length) :
      EvalLXPh s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]) (s₂, f₁, .flow .trap)
  /-- An unresolved `call_indirect` traps, making no call. -/
  | indRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
      {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width} {l : List (OCall H)}
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i none) :
      EvalLXPh s f stk (.op (.callIndirect x y) args :: es) l (s₁, f₁, .flow .trap)
  /-- `call_ref y` on a function reference, answered by returned values. -/
  | refRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (OCall H)} {r : Store H × Frame × POut}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hk : EvalLXPh s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLXPh s f stk (.op (.callRef y) args :: es)
        (l₁ ++ OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) r
  /-- `call_ref y` answered by an exception, raised at the call. -/
  | refThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {t : Nat} {l₁ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPh s f stk (.op (.callRef y) args :: es)
        (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr t) s₂])
        (s₂, f₁, .flow (.throw t))
  /-- `call_ref y`, cut. -/
  | refCut {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) (hws : rs.length < ws.length) :
      EvalLXPh s f stk (.op (.callRef y) args :: es)
        (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]) (s₂, f₁, .flow .trap)
  /-- `call_ref` on null traps, making no call. -/
  | refNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {l : List (OCall H)}
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal (.ref .null :: stk₁)))) :
      EvalLXPh s f stk (.op (.callRef y) args :: es) l (s₁, f₁, .flow .trap)
  /-- **A tail call** to a resolved callee: the body ends in the pending tail call, making no
  call here. -/
  | tail {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l : List (OCall H)}
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPh s f stk (.op i args :: es) l
        (s₁, f₁, .tail fa ((stk₁.drop (tailPop i)).take ps.length).reverse rs.length)
  | tailRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {l : List (OCall H)}
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (hres : TailRes s₁ f₁ i stk₁ none) :
      EvalLXPh s f stk (.op i args :: es) l (s₁, f₁, .flow .trap)
  | throw {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TagIdx}
      {args es : List BExpr} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
      {l : List (OCall H)}
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (ht : s₁.tag? f₁ x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
      (hn : ts.length ≤ stk₁.length) :
      EvalLXPh s f stk (.op (.throw x) args :: es) l
        (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩, f₁, .flow (.throw s₁.exns.length))
  | throwRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {args es : List BExpr}
      {l : List (OCall H)}
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal (.ref .null :: stk₁)))) :
      EvalLXPh s f stk (.op .throwRef args :: es) l (s₁, f₁, .flow .trap)
  | throwRefExn {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {a : Nat}
      {args es : List BExpr} {l : List (OCall H)}
      (hargs : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal (.ref (.exn a) :: stk₁)))) :
      EvalLXPh s f stk (.op .throwRef args :: es) l (s₁, f₁, .flow (.throw a))
  | tryOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      {r : Store H × Frame × POut} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) (hk : EvalLXPh s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLXPh s f stk (.tryTable bt cs body :: es) (l₁ ++ l₂) r
  | tryBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr k : Nat} {l : List (OCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalLXPh s f stk (.tryTable bt cs body :: es) l (s₁, f₁, .flow (.brk k vs))
  /-- A return, a trap or a pending tail call passes through the handler untouched. -/
  | tryEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {o : POut} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, o)) (ho : o.Escapes)
      (hnt : o.NotThrow) :
      EvalLXPh s f stk (.tryTable bt cs body :: es) l (s₁, f₁, o)
  | tryCatch {s s₁ : Store H} {f f₁ : Frame} {stk us : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat} {l' : LabelIdx}
      {l : List (OCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, .flow (.throw a)))
      (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l'))) :
      EvalLXPh s f stk (.tryTable bt cs body :: es) l
        (s₁, f₁, .flow (.brk l'.toNat (us.reverse ++ stk.drop np)))
  | tryRethrow {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l (s₁, f₁, .flow (.throw a)))
      (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
      EvalLXPh s f stk (.tryTable bt cs body :: es) l (s₁, f₁, .flow (.throw a))

/-- An open call's answer read as a callee flow: returned values (result order) as a fallthrough
of those values top-first, an exception as a throw. -/
def ansFlow : List Val ⊕ Nat → Flow
  | .inl ws => .normal ws.reverse
  | .inr t => .throw t

/-- **The end of a frame left by a pending tail call** of result arity `n`, in a function of
result arity `m`, from the tail call's answer `(b, s')`: the frame ends as the callee does
(`tailFlow n`, as `CallXP.FrameP.tail`), through the function's exit flow. -/
def tailAns (m n : Nat) (b : List Val ⊕ Nat) (s' : Store H) : End (Store H) (List Val ⊕ Nat) :=
  match exitFlow m (CallX.tailFlow n (ansFlow b)) with
  | some fl => endOfFlow fl s'
  | none => .trap

/-- **The functions of a store under the canonical relation, host functions as imports.** -/
def wasmHOpenXP : (wasmHShape H).OpenMod := fun a s vs =>
  {x | (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s' : Store H)
      (f₂ : Frame) (bfl fl : Flow) (l : List (OCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      EvalLXPh s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l
        (s', f₂, .flow bfl) ∧
      exitFlow rs.length bfl = some fl ∧ x = (l.map OCall.lift, endOfFlow fl s')) ∨
    (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s₁ s₂ : Store H)
      (f₂ : Frame) (a' n : Nat) (args : List Val) (b : List Val ⊕ Nat) (l : List (OCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      EvalLXPh s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l
        (s₁, f₂, .tail a' args n) ∧
      x = ((l ++ [OCall.mk a' args s₁ b s₂]).map OCall.lift, tailAns rs.length n b s₂)) ∨
    (∃ (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType) (s' : Store H) (r : Result)
      (fl : Flow),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length (resFlow r) = some fl ∧
      x = ([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlow fl s'))}

/-- **The logged canonical semantics of an invocation**: host calls as events, internal calls
closed. -/
def wasmEvFunXP : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.close wasmHOpenXP p.1 s p.2

end Silmaril.Wasm.Abstract
