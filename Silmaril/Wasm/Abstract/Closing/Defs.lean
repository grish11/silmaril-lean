module

public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Games.Abstract.Module.Defs

/-!
# Wasm functions as an open abstract module, closed by `Shape.close`

`Silmaril.Wasm.Abstract.Recursion` exposes internal calls through an oracle
(`EvalO C`) and closes them by its own least fixpoint (`closedCall`). This
module goes further. It turns the function code of a store into an **open
abstract module** (`Silmaril.Games.Abstract.Shape.OpenMod`) whose internal
calls appear as `self` calls with their answers. The generic closing
`Shape.close` of the abstract layer then applies to it directly.

The shape `wasmOShape H` has

* imports: none (`Sig.empty`); host calls are not modelled;
* state: the store;
* functions: every address `a : Nat` (an address without native code has no
  behaviour);
* arguments: values in parameter order; results: returned values in result
  order (`inl`) or an uncaught exception tag (`inr`).

`EvalL` is the native big-step relation with each internal call recorded,
in execution order, in a call log. A call is recorded with an *arbitrary*
answer: returned values `inl ws`, after which the caller continues, or an
exception `inr t`, after which the caller's code stops with that exception.
A callee trap needs no answer of its own. `Shape.Subst` resolves any recorded
call whose callee traps into a trap of the caller (`Subst.intTrap`).

`wasmOpen` reads a function's behaviours off `EvalL` on its body in a fresh
frame: the call log, then the end given by the body flow (`exitFlow`,
`endOfFlow`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

/-- The internal shape of the functions of a store: no imports, the store as
state, a function at every address. -/
abbrev wasmOShape (H : Type) : Silmaril.Games.Abstract.Shape.{0} :=
  ⟨Sig.empty, Store H, Nat, fun _ => List Val, fun _ => List Val ⊕ Nat⟩

/-- A recorded call of the open semantics. -/
abbrev OCall (H : Type) : Type := Call ((wasmOShape H).E ⊕ₛ (wasmOShape H).self)

/-- The internal call of the function at `a` on `args` in store `s`, answered
by `b` and the store `s'`. -/
def OCall.mk {H : Type} (a : Nat) (args : List Val) (s : Store H) (b : List Val ⊕ Nat)
    (s' : Store H) : OCall H :=
  ⟨.inr ⟨a, (args, s)⟩, (b, s')⟩

variable {H : Type}

/-- The end of a function whose exit flow (`exitFlow`) is `fl`, in store `s`. -/
def endOfFlow (fl : Flow) (s : Store H) : End (Store H) (List Val ⊕ Nat) :=
  match fl with
  | .throw t => .ret (.inr t) s
  | .trap => .trap
  | .normal ws | .brk _ ws | .ret ws => .ret (.inl ws) s

/-- The native big-step relation with every internal call recorded in a log,
answered arbitrarily. -/
inductive EvalL : Store H → Frame → List Val → List BExpr → List (OCall H) →
    Store H × Frame × Flow → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalL s f stk [] [] (s, f, .normal stk)
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {fl : Flow} {l : List (OCall H)} (hargs : EvalL s f stk args l (s₁, f₁, fl))
      (hfl : ¬ fl.IsNormal) :
      EvalL s f stk (.op i args :: es) l (s₁, f₁, fl)
  | callRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hk : EvalL s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalL s f stk (.op (.call x) args :: es)
        (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) r
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {t : Nat} {l₁ : List (OCall H)}
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalL s f stk (.op (.call x) args :: es)
        (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr t) s₂]) (s₂, f₁, .throw t)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalL s₂ f₂ stk₂ es l₂ r) :
      EvalL s f stk (.op i args :: es) (l₁ ++ l₂) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} {l : List (OCall H)} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalL s f stk args l (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalL s f stk (.op i args :: es) l (s₂, f₂, fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalL s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalL s f stk (.block bt body :: es) (l₁ ++ l₂) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l (s₁, f₁, .brk (k + 1) vs)) :
      EvalL s f stk (.block bt body :: es) l (s₁, f₁, .brk k vs)
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l : List (OCall H)}
      (har : arity f bt = some (np, nr)) (hbody : EvalL s f (stk.take np) body l (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalL s f stk (.block bt body :: es) l (s₁, f₁, fl)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .normal vs))
      (hk : EvalL s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalL s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .brk 0 vs))
      (hk : EvalL s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ r) :
      EvalL s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l (s₁, f₁, .brk (k + 1) vs)) :
      EvalL s f stk (.loop bt body :: es) l (s₁, f₁, .brk k vs)
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l : List (OCall H)}
      (har : arity f bt = some (np, nr)) (hbody : EvalL s f (stk.take np) body l (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalL s f stk (.loop bt body :: es) l (s₁, f₁, fl)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (OCall H)} {r : Store H × Frame × Flow}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalL s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalL s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ r) :
      EvalL s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat} {l₁ l₂ : List (OCall H)}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalL s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, .brk (k + 1) vs)) :
      EvalL s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, .brk k vs)
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalL s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, fl)) (hfl : fl.Escapes) :
      EvalL s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, fl)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {fl : Flow} {l : List (OCall H)}
      (hc : EvalL s f stk c l (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalL s f stk (.if_ bt c t el :: es) l (s₁, f₁, fl)

/-- **The functions of a store as an open abstract module.** A behaviour of
the function at `a` on `vs` in `s` is the call log of a logged run of its body
in a fresh frame, ended as the body's exit flow says. -/
def wasmOpen : (wasmOShape H).OpenMod := fun a s vs =>
  {x | ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s' : Store H)
      (f₂ : Frame) (bfl fl : Flow),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) x.1 (s', f₂, bfl) ∧
    exitFlow rs.length bfl = some fl ∧ x.2 = endOfFlow fl s'}

end Silmaril.Wasm.Abstract
