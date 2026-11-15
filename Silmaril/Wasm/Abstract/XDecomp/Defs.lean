module

public import Silmaril.Wasm.Abstract.Decomp.Defs
public import Silmaril.Wasm.Abstract.XDiverge.Defs

/-!
# Decomposing divergence through every call form (F4, call forms)

`Silmaril.Wasm.Abstract.Decomp` splits native divergence into local divergence
and descents (`Reach`). This module does the same for the extended divergence
`XDiverge.EvalDivX`, every call form a descent:

* `ReachX s f stk es y`: the problem reaches the call `y` (callee address,
  arguments, store), of any call form resolved as `CallX.EvalOX` resolves it,
  after a prefix that terminates in the closed extended semantics. A tail call
  is reached with its callee's arguments; it has no continuation;
* `BodyReachX x y`: the body of the call `x` reaches `y`; `BodyPathX`: finitely
  many such descents;
* `wasmLocalDivX z`: the body of `z` diverges within its function
  (`XDiverge.LocalDivX`).

`Silmaril.Wasm.Abstract.XDecomp.Thms`: a call diverges exactly when finitely
many descents reach a locally diverging call, or an infinite chain of descents
starts at it.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.XDecomp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmOShape)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDiverge

variable {H : Type}

/-- `ReachX s f stk es y`: the problem reaches the call `y`, of any call form,
after a prefix that terminates in the closed extended semantics. -/
inductive ReachX : Store H → Frame → List Val → List BExpr → (wasmOShape H).self.Op → Prop where
  | here {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachX s f stk (.op (.call x) args :: es) ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {y : (wasmOShape H).self.Op} :
      ReachX s f stk args y → ReachX s f stk (.op i args :: es) y
  | callK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {fl : Flow} {y : (wasmOShape H).self.Op}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      ReachX s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es y →
      ReachX s f stk (.op (.call x) args :: es) y
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {y : (wasmOShape H).self.Op} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      ReachX s₂ f₂ stk₂ es y → ReachX s f stk (.op i args :: es) y
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {y : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr)) :
      ReachX s f (stk.take np) body y → ReachX s f stk (.block bt body :: es) y
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX closedCallX s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      ReachX s₁ f₁ (vs.take nr ++ stk.drop np) es y → ReachX s f stk (.block bt body :: es) y
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {y : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr)) :
      ReachX s f (stk.take np) body y → ReachX s f stk (.loop bt body :: es) y
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX closedCallX s f (stk.take np) body (s₁, f₁, .normal vs)) :
      ReachX s₁ f₁ (vs.take nr ++ stk.drop np) es y → ReachX s f stk (.loop bt body :: es) y
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : EvalOX closedCallX s f (stk.take np) body (s₁, f₁, .brk 0 vs)) :
      ReachX s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) y →
      ReachX s f stk (.loop bt body :: es) y
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {y : (wasmOShape H).self.Op} :
      ReachX s f stk c y → ReachX s f stk (.if_ bt c t el :: es) y
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (hc : EvalOX closedCallX s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      ReachX s₁ f₁ (stk₁.take np) (if b then t else el) y → ReachX s f stk (.if_ bt c t el :: es) y
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {y : (wasmOShape H).self.Op}
      (hc : EvalOX closedCallX s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOX closedCallX s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      ReachX s₂ f₂ (vs.take nr ++ stk₁.drop np) es y → ReachX s f stk (.if_ bt c t el :: es) y
  /-- A resolved `call_indirect x y` is reached. -/
  | hereInd {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
      {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width} {fa : Nat}
      {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args
        (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachX s f stk (.op (.callIndirect x y) args :: es) ⟨fa, ((stk₁.take ps.length).reverse, s₁)⟩
  /-- A `call_indirect` returned; the continuation reaches `y`. -/
  | callIndK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {x : TableIdx}
      {y' : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} {fl : Flow}
      {y : (wasmOShape H).self.Op}
      (hargs : EvalOX closedCallX s f stk args
        (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y' ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse
        fn.locals) [] (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      ReachX s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es y →
      ReachX s f stk (.op (.callIndirect x y') args :: es) y
  /-- A `call_ref` on a function reference is reached. -/
  | hereRef {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachX s f stk (.op (.callRef y) args :: es) ⟨fa, ((stk₁.take ps.length).reverse, s₁)⟩
  /-- A `call_ref` returned; the continuation reaches `y`. -/
  | callRefK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {y' : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {fl : Flow} {y : (wasmOShape H).self.Op}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse
        fn.locals) [] (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      ReachX s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es y →
      ReachX s f stk (.op (.callRef y') args :: es) y
  /-- A resolved tail call is reached. -/
  | hereTail {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
      (hres : CallX.TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (CallX.tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachX s f stk (.op i args :: es)
        ⟨fa, (((stk₁.drop (CallX.tailPop i)).take ps.length).reverse, s₁)⟩

/-- The body of the call `x` reaches the call `y`. -/
def BodyReachX (x y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), x.2.2.funcs[x.1]? = some fi ∧ fi.code = .wasm fn ∧
    ReachX x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) y

/-- Finite descent paths: `BodyReachX` steps. -/
inductive BodyPathX : (wasmOShape H).self.Op → (wasmOShape H).self.Op → Prop
  | refl (x : (wasmOShape H).self.Op) : BodyPathX x x
  | step {x y z : (wasmOShape H).self.Op} : BodyReachX x y → BodyPathX y z → BodyPathX x z

/-- The call `z` diverges within its own function, every call it makes
terminating in the closed extended semantics. -/
def wasmLocalDivX (z : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
    LocalDivX z.2.2 (Frame.forCall fi.module z.2.1 fn.locals) [] (liftInstrs fn.body)

/-- The call `y` diverges. -/
def CallDivX (y : (wasmOShape H).self.Op) : Prop := FunDivX y.2.2 y.1 y.2.1

end Silmaril.Wasm.Abstract.XDecomp
