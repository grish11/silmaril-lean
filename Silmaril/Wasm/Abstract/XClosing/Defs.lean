module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Defs

/-!
# The extended call forms as an open abstract module (F4, call forms)

`Silmaril.Wasm.Abstract.Closing` turns the functions of a store into the open
abstract module `wasmOpen`, whose internal calls are the direct `call`s. This
module does the same with every call form: `EvalLX` is `EvalL` with the
indirect, reference and tail calls also recorded in the call log, each
resolved as `CallX.EvalOX` resolves it (`CallRes.IndRes`, `CallX.TailRes`) and
answered arbitrarily:

* returned values `inl ws` (result order): a returning call continues with
  them; a tail call ends the caller with a return of them;
* an exception `inr t`: the caller stops with it.

A callee trap needs no answer of its own: `Shape.Subst` resolves a recorded
call whose callee traps into a trap of the caller. An unresolved callee
(out-of-bounds index, failed cast, null reference) traps without a call.

`wasmOpenX` reads a function's behaviours off `EvalLX`, as `wasmOpen` does off
`EvalL`. Its closure is `XRecursion.closedCallX`
(`Silmaril.Wasm.Abstract.XClosing.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.XClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmOShape OCall OCall.mk endOfFlow exitFlow)

variable {H : Type}

/-- The extended big-step relation with every call, of any call form, recorded
in a log and answered arbitrarily. -/
inductive EvalLX : Store H → Frame → List Val → List BExpr → List (OCall H) →
    Store H × Frame × Flow → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalLX s f stk [] [] (s, f, .normal stk)
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {fl : Flow} {l : List (OCall H)} (hargs : EvalLX s f stk args l (s₁, f₁, fl))
      (hfl : ¬ fl.IsNormal) :
      EvalLX s f stk (.op i args :: es) l (s₁, f₁, fl)
  | callRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hk : EvalLX s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLX s f stk (.op (.call x) args :: es)
        (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) r
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {t : Nat} {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLX s f stk (.op (.call x) args :: es)
        (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr t) s₂]) (s₂, f₁, .throw t)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalLX s₂ f₂ stk₂ es l₂ r) :
      EvalLX s f stk (.op i args :: es) (l₁ ++ l₂) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} {l : List (OCall H)} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLX s f stk args l (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalLX s f stk (.op i args :: es) l (s₂, f₂, fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalLX s f (stk.take np) body l₁ (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalLX s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLX s f stk (.block bt body :: es) (l₁ ++ l₂) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLX s f (stk.take np) body l (s₁, f₁, .brk (k + 1) vs)) :
      EvalLX s f stk (.block bt body :: es) l (s₁, f₁, .brk k vs)
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l : List (OCall H)}
      (har : arity f bt = some (np, nr)) (hbody : EvalLX s f (stk.take np) body l (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalLX s f stk (.block bt body :: es) l (s₁, f₁, fl)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLX s f (stk.take np) body l₁ (s₁, f₁, .normal vs))
      (hk : EvalLX s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLX s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLX s f (stk.take np) body l₁ (s₁, f₁, .brk 0 vs))
      (hk : EvalLX s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ r) :
      EvalLX s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLX s f (stk.take np) body l (s₁, f₁, .brk (k + 1) vs)) :
      EvalLX s f stk (.loop bt body :: es) l (s₁, f₁, .brk k vs)
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l : List (OCall H)}
      (har : arity f bt = some (np, nr)) (hbody : EvalLX s f (stk.take np) body l (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalLX s f stk (.loop bt body :: es) l (s₁, f₁, fl)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (OCall H)} {r : Store H × Frame × Flow}
      (hc : EvalLX s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLX s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalLX s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ r) :
      EvalLX s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat} {l₁ l₂ : List (OCall H)}
      (hc : EvalLX s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLX s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, .brk (k + 1) vs)) :
      EvalLX s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, .brk k vs)
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      (hc : EvalLX s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLX s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, fl)) (hfl : fl.Escapes) :
      EvalLX s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, fl)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {fl : Flow} {l : List (OCall H)}
      (hc : EvalLX s f stk c l (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalLX s f stk (.if_ bt c t el :: es) l (s₁, f₁, fl)

  /-- `call_indirect x y` to a resolved callee, which returns. -/
  | callIndRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ l₂ : List (OCall H)}
      {r : Store H × Frame × Flow}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hk : EvalLX s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLX s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) r
  /-- `call_indirect x y` to a resolved callee, answered by an exception. -/
  | callIndThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {t : Nat}
      {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLX s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr t) s₂]) (s₂, f₁, .throw t)
  /-- `call_indirect x y` that does not resolve: a trap, no call. -/
  | callIndRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i none) :
      EvalLX s f stk (.op (.callIndirect x y) args :: es) l₁ (s₁, f₁, .trap)
  /-- `call_ref y` on a function reference, which returns. -/
  | callRefRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hk : EvalLX s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLX s f stk (.op (.callRef y) args :: es)
        (l₁ ++ OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) r
  /-- `call_ref y` on a function reference, answered by an exception. -/
  | callRefThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {t : Nat} {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLX s f stk (.op (.callRef y) args :: es)
        (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr t) s₂]) (s₂, f₁, .throw t)
  /-- `call_ref y` on null: a trap, no call. -/
  | callRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal (.ref .null :: stk₁))) :
      EvalLX s f stk (.op (.callRef y) args :: es) l₁ (s₁, f₁, .trap)
  /-- A tail call to a resolved callee, which returns: the caller returns its values. -/
  | tailRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hres : CallX.TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (CallX.tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLX s f stk (.op i args :: es)
        (l₁ ++ [OCall.mk fa ((stk₁.drop (CallX.tailPop i)).take ps.length).reverse s₁ (.inl ws) s₂])
        (s₂, f₁, .ret ws.reverse)
  /-- A tail call to a resolved callee, answered by an exception. -/
  | tailThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {t : Nat} {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hres : CallX.TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (CallX.tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLX s f stk (.op i args :: es)
        (l₁ ++ [OCall.mk fa ((stk₁.drop (CallX.tailPop i)).take ps.length).reverse s₁ (.inr t) s₂])
        (s₂, f₁, .throw t)
  /-- A tail call that does not resolve: a trap, no call. -/
  | tailRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ : List (OCall H)}
      (hargs : EvalLX s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hres : CallX.TailRes s₁ f₁ i stk₁ none) :
      EvalLX s f stk (.op i args :: es) l₁ (s₁, f₁, .trap)

/-- **Every call form of a store's functions as an open abstract module.** A
behaviour of the function at `a` on `vs` in `s` is the call log of a logged
extended run of its body in a fresh frame, ended as the body's exit flow says. -/
def wasmOpenX : (wasmOShape H).OpenMod := fun a s vs =>
  {x | ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s' : Store H)
      (f₂ : Frame) (bfl fl : Flow),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalLX s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) x.1 (s', f₂, bfl) ∧
    exitFlow rs.length bfl = some fl ∧ x.2 = endOfFlow fl s'}

end Silmaril.Wasm.Abstract.XClosing
