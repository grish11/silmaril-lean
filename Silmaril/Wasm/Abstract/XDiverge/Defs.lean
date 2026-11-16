module

public import Silmaril.Wasm.Interp.Diverge.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Defs

/-!
# Coinductive divergence through every call form (F4, call forms)

`Silmaril.Wasm.Interp.EvalDiv` and `LocalDiv` are the coinductive big-step
divergence of the native recursive semantics (#319/#322), in the style of
Leroy and Grall. This module extends them structurally with the indirect,
reference and tail calls of `CallX.EvalOX`. The terminating parts are read by
the closed extended semantics `EvalOX closedCallX`
(`Silmaril.Wasm.Abstract.XRecursion`), in place of `Eval`.

`DivStepX X Y` has `DivStep`'s rules and, for each extended call form resolved
as `EvalOX` resolves it:

* the callee's body diverges (`callIndCallee`, `callRefCallee`,
  `tailCallee`), read by `Y`;
* the callee returned and the continuation diverges (`callIndRet`,
  `callRefRet`), read by `X`. A tail call has no continuation.

The two greatest fixpoints are as in `Interp`:

* `EvalDivX := gfp (X ↦ DivStepX X X)`: divergence of the extended recursive
  semantics;
* `LocalDivX := gfp (X ↦ DivStepX X ⊥)`: divergence within the function,
  every call it makes terminating.

On direct stores and code they are `EvalDiv` and `LocalDiv`
(`Silmaril.Wasm.Abstract.XDiverge.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.XDiverge

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion

variable {H : Type}

/-- One unfolding of extended divergence: `X` for the code itself, `Y` for callee
bodies; terminating parts run in the closed extended semantics. -/
inductive DivStepX (X Y : Problem H) : Problem H where
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr} :
      X s f stk args → DivStepX X Y s f stk (.op i args :: es)
  | callee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Y s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) →
      DivStepX X Y s f stk (.op (.call x) args :: es)
  | callRet {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      X s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es →
      DivStepX X Y s f stk (.op (.call x) args :: es)
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      X s₂ f₂ stk₂ es → DivStepX X Y s f stk (.op i args :: es)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStepX X Y s f stk (.block bt body :: es)
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX closedCallX s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      X s₁ f₁ (vs.take nr ++ stk.drop np) es → DivStepX X Y s f stk (.block bt body :: es)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStepX X Y s f stk (.loop bt body :: es)
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX closedCallX s f (stk.take np) body (s₁, f₁, .normal vs)) :
      X s₁ f₁ (vs.take nr ++ stk.drop np) es → DivStepX X Y s f stk (.loop bt body :: es)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX closedCallX s f (stk.take np) body (s₁, f₁, .brk 0 vs)) :
      X s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) →
      DivStepX X Y s f stk (.loop bt body :: es)
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr} :
      X s f stk c → DivStepX X Y s f stk (.if_ bt c t el :: es)
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat}
      (hc : EvalOX closedCallX s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      X s₁ f₁ (stk₁.take np) (if b then t else el) → DivStepX X Y s f stk (.if_ bt c t el :: es)
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : EvalOX closedCallX s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOX closedCallX s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      X s₂ f₂ (vs.take nr ++ stk₁.drop np) es → DivStepX X Y s f stk (.if_ bt c t el :: es)
  /-- `call_indirect x y` to a resolved callee whose body diverges. -/
  | callIndCallee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args
        (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Y s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) →
      DivStepX X Y s f stk (.op (.callIndirect x y) args :: es)
  /-- `call_indirect x y` whose callee returned; the continuation diverges. -/
  | callIndRet {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalOX closedCallX s f stk args
        (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse
        fn.locals) [] (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      X s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es →
      DivStepX X Y s f stk (.op (.callIndirect x y) args :: es)
  /-- `call_ref y` on a function reference whose body diverges. -/
  | callRefCallee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Y s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) →
      DivStepX X Y s f stk (.op (.callRef y) args :: es)
  /-- `call_ref y` whose callee returned; the continuation diverges. -/
  | callRefRet {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse
        fn.locals) [] (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      X s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es →
      DivStepX X Y s f stk (.op (.callRef y) args :: es)
  /-- A tail call to a resolved callee whose body diverges. A tail call has no
  continuation: this is its only way to diverge after its arguments. -/
  | tailCallee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hres : CallX.TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (CallX.tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Y s₁ (Frame.forCall fi.module ((stk₁.drop (CallX.tailPop i)).take ps.length).reverse
        fn.locals) [] (liftInstrs fn.body) →
      DivStepX X Y s f stk (.op i args :: es)

theorem DivStepX.mono {X X' Y Y' : Problem H} (hX : X ≤ X') (hY : Y ≤ Y') {s : Store H}
    {f : Frame} {stk : List Val} {es : List BExpr} (h : DivStepX X Y s f stk es) :
    DivStepX X' Y' s f stk es := by
  cases h with
  | args h => exact .args (hX _ _ _ _ h)
  | callee hargs hfi hcode hty h => exact .callee hargs hfi hcode hty (hY _ _ _ _ h)
  | callRet hargs hfi hcode hty hbody hvs h =>
    exact .callRet hargs hfi hcode hty hbody hvs (hX _ _ _ _ h)
  | opK hi hargs hflat h => exact .opK hi hargs hflat (hX _ _ _ _ h)
  | block har h => exact .block har (hX _ _ _ _ h)
  | blockK har hbody hvs h => exact .blockK har hbody hvs (hX _ _ _ _ h)
  | loop har h => exact .loop har (hX _ _ _ _ h)
  | loopK har hbody h => exact .loopK har hbody (hX _ _ _ _ h)
  | loopBack har hbody h => exact .loopBack har hbody (hX _ _ _ _ h)
  | cond h => exact .cond (hX _ _ _ _ h)
  | arm hc hb har h => exact .arm hc hb har (hX _ _ _ _ h)
  | ifK hc hb har harm hvs h => exact .ifK hc hb har harm hvs (hX _ _ _ _ h)
  | callIndCallee hargs hres hfi hcode hty h =>
    exact .callIndCallee hargs hres hfi hcode hty (hY _ _ _ _ h)
  | callIndRet hargs hres hfi hcode hty hbody hvs h =>
    exact .callIndRet hargs hres hfi hcode hty hbody hvs (hX _ _ _ _ h)
  | callRefCallee hargs hfi hcode hty h => exact .callRefCallee hargs hfi hcode hty (hY _ _ _ _ h)
  | callRefRet hargs hfi hcode hty hbody hvs h =>
    exact .callRefRet hargs hfi hcode hty hbody hvs (hX _ _ _ _ h)
  | tailCallee hargs hres hfi hcode hty h => exact .tailCallee hargs hres hfi hcode hty (hY _ _ _ _ h)

/-- Unfolding of the extended recursive semantics' divergence. -/
def divOpX : Problem H →o Problem H where
  toFun X := DivStepX X X
  monotone' _ _ h _ _ _ _ := DivStepX.mono h h

/-- Unfolding of divergence within the function, every callee terminating. -/
def localDivOpX : Problem H →o Problem H where
  toFun X := DivStepX X ⊥
  monotone' _ _ h _ _ _ _ := DivStepX.mono h le_rfl

/-- **Coinductive divergence of the extended recursive semantics.** -/
def EvalDivX : Problem H := (divOpX (H := H)).gfp

/-- **Divergence within a function, every call form included**: every call it
makes terminates in the closed extended semantics. -/
def LocalDivX : Problem H := (localDivOpX (H := H)).gfp

/-- The body of the function at `a` on `vs`, in a fresh frame, diverges. -/
def FunDivX (s : Store H) (a : Nat) (vs : List Val) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    EvalDivX s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)

end Silmaril.Wasm.Abstract.XDiverge
