module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Abstract.HostEval.Defs
public import Silmaril.Wasm.Abstract.HostCall.Defs

/-!
# Wasm functions with host calls as an open module, closed by `Shape.close` (stage H2)

`Silmaril.Wasm.Abstract.Closing` turns the functions of a store into an open module
`wasmOpen` with no imports: every internal call is a `self` call, recorded with its answer
in the logged run `EvalL`. This module adds the host functions as the **only** import events:

* `wasmHShape H`: imports `wasmHostSig H` (a host function, store and arguments, answered by
  store and result); state the store; a function at every address.
* `wasmHOpen`: a Wasm function's behaviours are those of `wasmOpen` (its `EvalL` log as `self`
  calls, `OCall.lift`); a host function `hh` makes the one import call `(hh, s, vs)`, answered
  arbitrarily by `(s', r)`, and ends as `r` does through its exit flow.
* `wasmEvFun`: the closure `Shape.close wasmHOpen`, as an abstract function of the invocation
  `(a, vs)`. Internal Wasm calls are resolved by the closure and never appear as events; host
  calls appear in execution order with their answers. A host relation then filters the answers
  (`HostRel.Consistent`, `hostObs`).
* `ReachL`: the logged analog of `ReachO`: the trees reach an internal call after a prefix run
  by `EvalL`, its completed calls recorded with arbitrary answers.
* `wasmEvPend`: the pending host calls of an invocation: a host function invoked directly, or
  a call reached in a Wasm body (its completed calls resolved by `Shape.SubstPre` against the
  closure) whose callee's pending call it is, finitely deep (`PendL`).

Theorems in `Silmaril.Wasm.Abstract.HostClosing.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The functions of a store with host calls as imports. -/
abbrev wasmHShape (H : Type) : Silmaril.Games.Abstract.Shape.{0} :=
  ⟨wasmHostSig H, Store H, Nat, fun _ => List Val, fun _ => List Val ⊕ Nat⟩

/-- A recorded call of the open module with host imports. -/
abbrev HCall (H : Type) : Type := Call ((wasmHShape H).E ⊕ₛ (wasmHShape H).self)

/-- An internal call of `wasmOpen`'s log, as a `self` call of `wasmHOpen`. -/
def OCall.lift : OCall H → HCall H
  | ⟨.inr y, ans⟩ => ⟨.inr y, ans⟩

/-- **The functions of a store, host functions as imports.** -/
def wasmHOpen : (wasmHShape H).OpenMod := fun a s vs =>
  {x | (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s' : Store H)
      (f₂ : Frame) (bfl fl : Flow) (l : List (OCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      EvalL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l (s', f₂, bfl) ∧
      exitFlow rs.length bfl = some fl ∧ x = (l.map OCall.lift, endOfFlow fl s')) ∨
    (∃ (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType) (s' : Store H) (r : Result)
      (fl : Flow),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length (resFlow r) = some fl ∧
      x = ([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlow fl s'))}

/-- **The logged native semantics of an invocation**: host calls as events, internal calls
closed. -/
def wasmEvFun : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.close wasmHOpen p.1 s p.2

/-- **The trees reach the internal call `y`** after a logged prefix (`EvalL`): the logged
analog of `ReachO`. -/
inductive ReachL : Store H → Frame → List Val → List BExpr → List (OCall H) →
    (wasmOShape H).self.Op → Prop where
  | here {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l : List (OCall H)} (hargs : EvalL s f stk args l (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachL s f stk (.op (.call x) args :: es) l ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {l : List (OCall H)} {y : (wasmOShape H).self.Op} :
      ReachL s f stk args l y → ReachL s f stk (.op i args :: es) l y
  | callK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {l₁ l₂ : List (OCall H)} {y : (wasmOShape H).self.Op}
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachL s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ y →
      ReachL s f stk (.op (.call x) args :: es)
        (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂) y
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (OCall H)} {y : (wasmOShape H).self.Op}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      ReachL s₂ f₂ stk₂ es l₂ y → ReachL s f stk (.op i args :: es) (l₁ ++ l₂) y
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (OCall H)} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) :
      ReachL s f (stk.take np) body l y → ReachL s f stk (.block bt body :: es) l y
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      ReachL s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ y →
      ReachL s f stk (.block bt body :: es) (l₁ ++ l₂) y
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (OCall H)} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) :
      ReachL s f (stk.take np) body l y → ReachL s f stk (.loop bt body :: es) l y
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .normal vs)) :
      ReachL s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ y →
      ReachL s f stk (.loop bt body :: es) (l₁ ++ l₂) y
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .brk 0 vs)) :
      ReachL s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ y →
      ReachL s f stk (.loop bt body :: es) (l₁ ++ l₂) y
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {l : List (OCall H)} {y : (wasmOShape H).self.Op} :
      ReachL s f stk c l y → ReachL s f stk (.if_ bt c t el :: es) l y
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)}
      {y : (wasmOShape H).self.Op}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      ReachL s₁ f₁ (stk₁.take np) (if b then t else el) l₂ y →
      ReachL s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) y
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (OCall H)} {y : (wasmOShape H).self.Op}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalL s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      ReachL s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ y →
      ReachL s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃) y

/-- **A pending host call of an invocation**, after the host calls `cs`: a host function
invoked directly, or the pending call of a callee reached in a Wasm body, the body's
completed calls resolved against the closure. -/
inductive PendL : Store H → Nat → List Val → List (Call (wasmHostSig H)) →
    (wasmHostSig H).Op → Prop where
  | self {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {hh : H}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) : PendL s a vs [] (hh, s, vs)
  | desc {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func}
      {l : List (OCall H)} {q q' : List (Call (wasmHostSig H))} {y : (wasmOShape H).self.Op}
      {m : (wasmHostSig H).Op}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
      (hr : ReachL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l y)
      (hq : Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q) :
      PendL y.2.2 y.1 y.2.1 q' m → PendL s a vs (q ++ q') m

/-- **The pending host calls of an invocation.** -/
def wasmEvPend : Silmaril.Games.Abstract.Pending (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => {x | PendL s p.1 p.2 x.1 x.2}

end Silmaril.Wasm.Abstract
