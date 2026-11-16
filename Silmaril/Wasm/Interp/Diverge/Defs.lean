module

public import Silmaril.Wasm.Binaryen.Interp
public import Mathlib.Order.FixedPoints

/-!
# Coinductive divergence of the native recursive semantics

`Binaryen.Eval` is the inductive (terminating) big-step relation of the
native interpreter. This module defines its divergent counterpart, the
coinductive big-step divergence `EvalDiv`, in the style of Leroy and Grall.

A problem `(s, f, stk, es)` diverges when one of the following holds:

* a part evaluated first diverges: the arguments of an operator, a block or
  loop body, the condition or the chosen arm of an `if`;
* a called function's body diverges (`calleeDiv`);
* everything before the continuation terminates, as `Eval` says, and the
  continuation diverges. The continuation comes after an operator, a call
  that returned, a block, a loop exit or an `if`. For a loop whose body
  branched back to it (`loopBack`), it is the next iteration.

`DivStep X Y` is one unfolding. `X` is used for the parts of the code
itself; `Y` for the bodies of called functions. Two greatest fixpoints:

* `EvalDiv := gfp (X ↦ DivStep X X)`: divergence of the recursive semantics;
* `LocalDiv := gfp (X ↦ DivStep X ⊥)`: divergence **within the function
  itself**. Every call it makes terminates, as `Eval` says. This covers a
  silent `loop (br 0)`, a loop that calls a returning function forever, and
  every mixture. It does not cover divergence *inside* a callee.

The theorems are in `Silmaril.Wasm.Interp.Diverge.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- A predicate on native problems: store, frame, top-first stack, trees. -/
abbrev Problem (H : Type) : Type := Store H → Frame → List Val → List BExpr → Prop

/-- One unfolding of divergence: `X` for the code itself, `Y` for callee bodies. -/
inductive DivStep (X Y : Problem H) : Problem H where
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr} :
      X s f stk args → DivStep X Y s f stk (.op i args :: es)
  | callee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType}
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Y s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) →
      DivStep X Y s f stk (.op (.call x) args :: es)
  | callRet {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : Eval s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs) :
      X s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es →
      DivStep X Y s f stk (.op (.call x) args :: es)
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} (hi : ∀ x, i ≠ .call x)
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      X s₂ f₂ stk₂ es → DivStep X Y s f stk (.op i args :: es)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStep X Y s f stk (.block bt body :: es)
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      X s₁ f₁ (vs.take nr ++ stk.drop np) es → DivStep X Y s f stk (.block bt body :: es)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStep X Y s f stk (.loop bt body :: es)
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, .normal vs)) :
      X s₁ f₁ (vs.take nr ++ stk.drop np) es → DivStep X Y s f stk (.loop bt body :: es)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, .brk 0 vs)) :
      X s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) →
      DivStep X Y s f stk (.loop bt body :: es)
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr} :
      X s f stk c → DivStep X Y s f stk (.if_ bt c t el :: es)
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat}
      (hc : Eval s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      X s₁ f₁ (stk₁.take np) (if b then t else el) → DivStep X Y s f stk (.if_ bt c t el :: es)
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : Eval s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      X s₂ f₂ (vs.take nr ++ stk₁.drop np) es → DivStep X Y s f stk (.if_ bt c t el :: es)

theorem DivStep.mono {X X' Y Y' : Problem H} (hX : X ≤ X') (hY : Y ≤ Y') {s : Store H}
    {f : Frame} {stk : List Val} {es : List BExpr} (h : DivStep X Y s f stk es) :
    DivStep X' Y' s f stk es := by
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

/-- Unfolding of the recursive semantics' divergence. -/
def divOp : Problem H →o Problem H where
  toFun X := DivStep X X
  monotone' _ _ h _ _ _ _ := DivStep.mono h h

/-- Unfolding of divergence within the function, every callee terminating. -/
def localDivOp : Problem H →o Problem H where
  toFun X := DivStep X ⊥
  monotone' _ _ h _ _ _ _ := DivStep.mono h le_rfl

/-- **Coinductive divergence of the native recursive semantics.** -/
def EvalDiv : Problem H := (divOp (H := H)).gfp

/-- **Divergence within a function**: every call it makes terminates. -/
def LocalDiv : Problem H := (localDivOp (H := H)).gfp

/-- The body of the function at `a` on `vs`, in a fresh frame, diverges. -/
def FunDiv (s : Store H) (a : Nat) (vs : List Val) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    EvalDiv s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)

end Silmaril.Wasm.Interp
