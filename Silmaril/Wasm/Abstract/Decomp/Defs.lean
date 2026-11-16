module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Interp.Diverge.Defs

/-!
# Decomposing divergence: local divergence and descents

`Silmaril.Wasm.Interp.EvalDiv` is divergence of the native recursive
semantics. This module splits it into the two ways a call can diverge:

* **within its own function** (`wasmLocalDiv`, from `Interp.LocalDiv`): the
  body diverges while every call it makes terminates. This covers a silent
  loop and a loop that calls a returning function forever;
* **inside a callee**: the body reaches a call (`Reach`) after a terminating
  prefix, and that callee diverges.

`Reach P y` says the problem `P` reaches the internal call `y`, a callee
address with its arguments and store, after everything before it terminated.
Its constructors follow `Interp.DivStep`, with the callee case as the base.
`BodyReach x y` is `Reach` from the body of the call `x`. It is the native
form of `Shape.Descends wasmOpen (Shape.close wasmOpen) x [] y`
(`Silmaril.Wasm.Abstract.Decomp.Thms`).

`wasmClosedDL := Shape.closeDL wasmOpen wasmLocalDiv` is the enriched
closing: `closeD` plus `div` after every finite descent path to a locally
diverging call.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `Reach s f stk es y`: the problem reaches the internal call `y` after a
terminating prefix. -/
inductive Reach : Store H → Frame → List Val → List BExpr → (wasmOShape H).self.Op → Prop where
  | here {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Reach s f stk (.op (.call x) args :: es) ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {y : (wasmOShape H).self.Op} :
      Reach s f stk args y → Reach s f stk (.op i args :: es) y
  | callK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {fl : Flow} {y : (wasmOShape H).self.Op}
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : Eval s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      Reach s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es y →
      Reach s f stk (.op (.call x) args :: es) y
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {y : (wasmOShape H).self.Op} (hi : ∀ x, i ≠ .call x)
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      Reach s₂ f₂ stk₂ es y → Reach s f stk (.op i args :: es) y
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {y : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr)) :
      Reach s f (stk.take np) body y → Reach s f stk (.block bt body :: es) y
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      Reach s₁ f₁ (vs.take nr ++ stk.drop np) es y → Reach s f stk (.block bt body :: es) y
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {y : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr)) :
      Reach s f (stk.take np) body y → Reach s f stk (.loop bt body :: es) y
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, .normal vs)) :
      Reach s₁ f₁ (vs.take nr ++ stk.drop np) es y → Reach s f stk (.loop bt body :: es) y
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, .brk 0 vs)) :
      Reach s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) y →
      Reach s f stk (.loop bt body :: es) y
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {y : (wasmOShape H).self.Op} :
      Reach s f stk c y → Reach s f stk (.if_ bt c t el :: es) y
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (hc : Eval s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      Reach s₁ f₁ (stk₁.take np) (if b then t else el) y → Reach s f stk (.if_ bt c t el :: es) y
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {y : (wasmOShape H).self.Op}
      (hc : Eval s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      Reach s₂ f₂ (vs.take nr ++ stk₁.drop np) es y → Reach s f stk (.if_ bt c t el :: es) y

/-- The body of the call `x` reaches the call `y`. -/
def BodyReach (x y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), x.2.2.funcs[x.1]? = some fi ∧ fi.code = .wasm fn ∧
    Reach x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) y

/-- Finite descent paths: `BodyReach` steps. -/
inductive BodyPath : (wasmOShape H).self.Op → (wasmOShape H).self.Op → Prop
  | refl (x : (wasmOShape H).self.Op) : BodyPath x x
  | step {x y z : (wasmOShape H).self.Op} : BodyReach x y → BodyPath y z → BodyPath x z

/-- The call `z` diverges within its own function, every callee terminating. -/
def wasmLocalDiv (z : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
    Interp.LocalDiv z.2.2 (Frame.forCall fi.module z.2.1 fn.locals) [] (liftInstrs fn.body)

/-- **The enriched closing** of the functions of a store: `closeD` plus local
divergence after finite descents. -/
def wasmClosedDL : (wasmOShape H).ClosedMod := Shape.closeDL wasmOpen wasmLocalDiv

end Silmaril.Wasm.Abstract
