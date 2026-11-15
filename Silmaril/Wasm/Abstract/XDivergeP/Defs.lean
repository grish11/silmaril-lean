module

public import Silmaril.Wasm.Interp.Diverge.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Defs

/-!
# Coinductive divergence with exceptions and pending tail calls (F5)

`XDiverge.EvalDivX` is the coinductive divergence of `CallX.EvalOX` (eager tail calls, no
exceptions). This module gives the divergence of the faithful semantics `CallXP.EvalOXP`
(`XRecursionP.closedCallXP`), where a tail call is **pending**: it passes every `block`, `loop`,
`if` and `try_table` and is made only when the frame is left (`CallXP.FrameP`).

Two predicates are defined together, as one greatest fixpoint over pairs:

* `EvalDivXP s f stk es`: the problem diverges. `DivStepXP X Y` unfolds it:
  * in the arguments of an operator (`args`), in a `block`, `loop` or `try_table` body (`block`,
    `loop`, `try_`: inside the handler), in the condition or chosen arm of an `if` (`cond`, `arm`);
  * in the continuation after a head tree that completed normally (`cont`; a tree completing
    normally includes a `block`, `loop`, `if` or `try_table` left by a branch to its own label, so
    an exception caught by a `try_table` clause branching out continues here), and in the next
    iteration of a loop whose body branched back (`loopBack`);
  * in a callee (`callee`, `callIndCallee`, `callRefCallee`), read by `Y` on the callee's address
    and arguments.
  A tail call has no unfolding here: its callee runs only at the frame.
* `FunDivXP s a vs`: the call of the function at `a` on `vs` diverges. `CallStepXP X Y` unfolds it
  at the frame: the body diverges (`body`, read by `X`), or the body ends in a pending tail call
  and **its** call diverges (`frameTail`, read by `Y`), outside every handler of the body.

The terminating parts are read by the closed semantics `EvalOXP closedCallXP`. Tail-call chains
(a function tail-calling itself forever, every body ending in a pending tail call) diverge
coinductively through `frameTail`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.XDivergeP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Abstract.CallXT (typeArity)

variable {H : Type}

/-- A call problem: the function at an address, on arguments (bottom first). -/
abbrev CallProblem (H : Type) : Type := Store H → Nat → List Val → Prop

/-- One unfolding of the divergence of a problem: `X` for the code itself, `Y` for calls;
terminating parts run in the closed semantics with pending tail calls. -/
inductive DivStepXP (X : Problem H) (Y : CallProblem H) : Problem H where
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr} :
      X s f stk args → DivStepXP X Y s f stk (.op i args :: es)
  /-- The head tree completes normally and the rest diverges. -/
  | cont {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {e : BExpr} {es : List BExpr}
      (hd : EvalOXP closedCallXP s f stk [e] (s₂, f₂, .flow (.normal stk₂))) :
      X s₂ f₂ stk₂ es → DivStepXP X Y s f stk (e :: es)
  /-- `call x`, the callee's call diverging. -/
  | callee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Y s₁ a (stk₁.take ps.length).reverse → DivStepXP X Y s f stk (.op (.call x) args :: es)
  /-- `call_indirect x y` to a resolved callee whose call diverges. -/
  | callIndCallee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP closedCallXP s f stk args
        (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      Y s₁ fa (stk₁.take ps.length).reverse →
      DivStepXP X Y s f stk (.op (.callIndirect x y) args :: es)
  /-- `call_ref y` on a function reference whose call diverges. -/
  | callRefCallee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      Y s₁ fa (stk₁.take ps.length).reverse → DivStepXP X Y s f stk (.op (.callRef y) args :: es)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStepXP X Y s f stk (.block bt body :: es)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStepXP X Y s f stk (.loop bt body :: es)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} (har : arity f bt = some (np, nr))
      (hbody : EvalOXP closedCallXP s f (stk.take np) body (s₁, f₁, .flow (.brk 0 vs))) :
      X s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) →
      DivStepXP X Y s f stk (.loop bt body :: es)
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr} :
      X s f stk c → DivStepXP X Y s f stk (.if_ bt c t el :: es)
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat}
      (hc : EvalOXP closedCallXP s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : arity f₁ bt = some (np, nr)) :
      X s₁ f₁ (stk₁.take np) (if b then t else el) → DivStepXP X Y s f stk (.if_ bt c t el :: es)
  /-- A `try_table` body diverges, inside its handler. -/
  | try_ {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStepXP X Y s f stk (.tryTable bt cs body :: es)

/-- **One unfolding of the divergence of a call, at the frame**: the body diverges, or it ends
in a pending tail call whose own call diverges. -/
inductive CallStepXP (X : Problem H) (Y : CallProblem H) : CallProblem H where
  | body {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H} {fn : Func}
      (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
      X s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) →
      CallStepXP X Y s a args
  /-- The body ends in a pending tail call; leaving the frame makes it, and it diverges. -/
  | frameTail {s s₁ : Store H} {a a' n : Nat} {args args' : List Val} {fi : FuncInst H}
      {fn : Func} {f₂ : Frame} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
      (hbody : EvalOXP closedCallXP s (Frame.forCall fi.module args fn.locals) []
        (liftInstrs fn.body) (s₁, f₂, .tail a' args' n)) :
      Y s₁ a' args' → CallStepXP X Y s a args

theorem DivStepXP.mono {X X' : Problem H} {Y Y' : CallProblem H} (hX : X ≤ X') (hY : Y ≤ Y')
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} (h : DivStepXP X Y s f stk es) :
    DivStepXP X' Y' s f stk es := by
  cases h with
  | args h => exact .args (hX _ _ _ _ h)
  | cont hd h => exact .cont hd (hX _ _ _ _ h)
  | callee hargs hfi hty h => exact .callee hargs hfi hty (hY _ _ _ h)
  | callIndCallee hargs hres hfi hty hy h => exact .callIndCallee hargs hres hfi hty hy (hY _ _ _ h)
  | callRefCallee hargs hfi hty hy h => exact .callRefCallee hargs hfi hty hy (hY _ _ _ h)
  | block har h => exact .block har (hX _ _ _ _ h)
  | loop har h => exact .loop har (hX _ _ _ _ h)
  | loopBack har hbody h => exact .loopBack har hbody (hX _ _ _ _ h)
  | cond h => exact .cond (hX _ _ _ _ h)
  | arm hc hb har h => exact .arm hc hb har (hX _ _ _ _ h)
  | try_ har h => exact .try_ har (hX _ _ _ _ h)

theorem CallStepXP.mono {X X' : Problem H} {Y Y' : CallProblem H} (hX : X ≤ X') (hY : Y ≤ Y')
    {s : Store H} {a : Nat} {args : List Val} (h : CallStepXP X Y s a args) :
    CallStepXP X' Y' s a args := by
  cases h with
  | body hfi hcode h => exact .body hfi hcode (hX _ _ _ _ h)
  | frameTail hfi hcode hbody h => exact .frameTail hfi hcode hbody (hY _ _ _ h)

/-- Unfolding of both divergences together, as a monotone operator on pairs. -/
def divOpXP : (Problem H × CallProblem H) →o (Problem H × CallProblem H) where
  toFun p := (DivStepXP p.1 p.2, CallStepXP p.1 p.2)
  monotone' _ _ h :=
    ⟨fun _ _ _ _ hd => DivStepXP.mono h.1 h.2 hd, fun _ _ _ hc => CallStepXP.mono h.1 h.2 hc⟩

/-- **Coinductive divergence of a problem** in the closed semantics with pending tail calls. -/
def EvalDivXP : Problem H := (divOpXP (H := H)).gfp.1

/-- **Coinductive divergence of a call**, its frame included: the body diverges, or a pending
tail call of its body, made when the frame is left, diverges (`funDivXP_iff_step`). -/
def FunDivXP : CallProblem H := (divOpXP (H := H)).gfp.2

end Silmaril.Wasm.Abstract.XDivergeP
