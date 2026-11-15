module

public import Silmaril.Wasm.Binaryen.Interp
public import Mathlib.Order.FixedPoints

/-!
# Recursion through internal calls, exposed and closed

The native interpreter's big-step relation `Silmaril.Wasm.Binaryen.Eval`
handles `call` recursively: a call evaluates the callee's body
(`callOk`/`callTrap`/`callThrow`). It is adequate for Core 3.0 including the
final store (`Silmaril.Wasm.Interp.native_store_adequacy`).

**Exposure.** `EvalO C` is the same relation with every internal call answered
by an *oracle* `C : CallRel H`: `C s a args (s', fl)` says that calling the
function at address `a` on `args` in store `s` may end in store `s'` with
body flow `fl`. The code of the caller is evaluated by `EvalO`; the callee is
not entered. This is the open semantics of a function, with its internal
calls as interactions.

**Closing.** `bodyCall C` reads the code at an address and evaluates its body
with `EvalO C`: one round of answering calls by running callees. Closing is
the least fixpoint `closedCall := lfp bodyCall`, the same construction as
`Silmaril.Games.Abstract.Shape.close` for abstract modules.

`Silmaril.Wasm.Abstract.Recursion.Thms` proves that closing agrees with the
recursive semantics: `EvalO closedCall = Eval`, and `closedCall` is exactly the
callee relation of `Eval`. These are **terminating** runs: least fixpoints and
inductive derivations are both finite. Divergence through unbounded recursion
needs the coinductive half (`Shape.closeD`) and the Core 3.0 `Step` inversion
lemmas, which are coordinated separately.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- An oracle for internal calls: from a store, a function address and
arguments to a final store and body flow. -/
abbrev CallRel (H : Type) : Type := Store H → Nat → List Val → Store H × Flow → Prop

/-- The native big-step relation with internal calls answered by `C`. -/
inductive EvalO (C : CallRel H) : Store H → Frame → List Val → List BExpr → Store H × Frame × Flow → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalO C s f stk [] (s, f, .normal stk)
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {fl : Flow} (hargs : EvalO C s f stk args (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalO C s f stk (.op i args :: es) (s₁, f₁, fl)
  | callOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
      (hvs : fl.retVals = some vs)
      (hk : EvalO C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalO C s f stk (.op (.call x) args :: es) r
  | callTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType}
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
      EvalO C s f stk (.op (.call x) args :: es) (s₂, f₁, .trap)
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {t : Nat}
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
      EvalO C s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {r : Store H × Frame × Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalO C s₂ f₂ stk₂ es r) :
      EvalO C s f stk (.op i args :: es) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalO C s f stk (.op i args :: es) (s₂, f₂, fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalO C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalO C s f stk (.block bt body :: es) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalO C s f stk (.block bt body :: es) (s₁, f₁, .brk k vs)
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalO C s f stk (.block bt body :: es) (s₁, f₁, fl)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .normal vs))
      (hk : EvalO C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalO C s f stk (.loop bt body :: es) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .brk 0 vs))
      (hk : EvalO C s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
      EvalO C s f stk (.loop bt body :: es) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalO C s f stk (.loop bt body :: es) (s₁, f₁, .brk k vs)
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalO C s f stk (.loop bt body :: es) (s₁, f₁, fl)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hc : EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalO C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalO C s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
      EvalO C s f stk (.if_ bt c t el :: es) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat}
      (hc : EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalO C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .brk (k + 1) vs)) :
      EvalO C s f stk (.if_ bt c t el :: es) (s₂, f₂, .brk k vs)
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalO C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl)) (hfl : fl.Escapes) :
      EvalO C s f stk (.if_ bt c t el :: es) (s₂, f₂, fl)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {fl : Flow}
      (hc : EvalO C s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalO C s f stk (.if_ bt c t el :: es) (s₁, f₁, fl)

/-- One round of answering calls by running callees: the code at `a`
evaluated by `EvalO C` in a fresh frame. -/
def bodyCall (C : CallRel H) : CallRel H := fun s a args out =>
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalO C s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (out.1, f₂, out.2)

theorem EvalO.mono {C C' : CallRel H} (hC : C ≤ C') {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalO C s f stk es r) : EvalO C' s f stk es r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ => exact .callOk ih₁ hfi hty (hC _ _ _ _ hcall) hvs ih₂
  | callTrap _ hfi hty hcall ih => exact .callTrap ih hfi hty (hC _ _ _ _ hcall)
  | callThrow _ hfi hty hcall ih => exact .callThrow ih hfi hty (hC _ _ _ _ hcall)
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

/-- One round of answering calls, as a monotone operator. -/
def bodyCallOp : CallRel H →o CallRel H where
  toFun := bodyCall
  monotone' _ _ hC _ _ _ _ := fun ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄⟩ =>
    ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄.mono hC⟩

/-- Closing: the least fixpoint of answering calls by running callees. -/
def closedCall : CallRel H := (bodyCallOp (H := H)).lfp

/-- The callee relation of the recursive semantics `Eval`. -/
def evalCall : CallRel H := fun s a args out =>
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    Eval s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (out.1, f₂, out.2)

/-- The flow a call hands back for a final flow of its body, as `invokeRun`
does: values (from a normal end, a `return` or a branch out of the body), a
trap or an uncaught exception. -/
def exitFlow (n : Nat) : Flow → Option Flow
  | .normal ws | .ret ws | .brk 0 ws => some (.normal (ws.take n).reverse)
  | .trap => some .trap
  | .throw x => some (.throw x)
  | _ => none

/-- The closed outcomes of an invocation: the body evaluated in the open
semantics with internal calls answered by the closure, and the flow it hands
back. -/
def ClosedOutcome (s : Store H) (a : Nat) (vs : List Val) (s' : Store H) (fl : Flow) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame) (bfl : Flow),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalO closedCall s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) (s', f₂, bfl) ∧
    exitFlow rs.length bfl = some fl

end Silmaril.Wasm.Abstract
