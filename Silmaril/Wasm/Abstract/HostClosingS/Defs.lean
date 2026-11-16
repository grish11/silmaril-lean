module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Games.Abstract.StratObs.Defs

/-!
# Session closing: the canonical relation closed with traps that keep the store

`Silmaril.Wasm.Abstract.HostClosingXP` closes the canonical relation by `Shape.close` over the
shape `wasmHShape H`, whose ends are `End (Store H) (List Val ⊕ Nat)`. A trap there is `End.trap`,
which carries no store, and a callee trap is resolved by `Shape.Subst.intTrap`, which drops the
store the callee left. A Wasm session needs that store: a trap aborts only the current
invocation, and the next invocation starts from the store the trap left.

This module closes the same relation natively with store-keeping traps:

* `wasmHShapeS H`: `wasmHShape H` with answers `(List Val ⊕ Nat) ⊕ PUnit`. The answer
  `(.inr (), s₂)` means the callee trapped, leaving the store `s₂`; `(.inl b, s₂)` is an answer
  `b` of `wasmHShape H` (returned values `inl ws`, an exception `inr t`).
* `EvalLXPS`: the logged canonical relation `EvalLXPh` over these answers, with the same rules
  and constructor names, except that there are **no cut rules** (`callCut`, `indCut`, `refCut`):
  each call form (`call`, resolved `call_indirect`, `call_ref`) instead has a **trap answer** rule
  (`callTrap`, `indTrap`, `refTrap`). The call is recorded with the answer `(.inr (), s₂)`, and the
  caller ends at once in `(s₂, f₁, .flow .trap)`, a trap flow, which no handler catches.
* `endOfFlowS`, `tailAnsS`: the ends of a frame, as `endOfFlow` and `tailAns`, with a trap keeping
  its store: `.ret (.inr ()) s`.
* `wasmHOpenXPS`: the open module, as `wasmHOpenXP`: a body ending in a trap flow ends
  `.ret (.inr ()) s'`; a pending tail call ends as its answer does, a trap answer `(.inr (), s₂)`
  ending `.ret (.inr ()) s₂`; a host function whose result is a trap, leaving `s'`, ends
  `.ret (.inr ()) s'`.
* `wasmEvFunXPS := Shape.close wasmHOpenXPS`: the session closure. A callee trap is a returned
  answer `.inr ()` with its store, resolved by `Shape.Subst.int`.
* `ReachLXPS`, `PendLXPS`, `wasmEvPendXPS`: the pending host calls, as `ReachLXP`, `PendLXP`,
  `wasmEvPendXP`, over the session relation and closure.
* `wasmEvFunDXPS`, `sessionTripleXP`: with the divergent behaviours of `wasmEvFunDXP` and the
  productive streams of `wasmEvInfNXP`, which carry no trap store: the session analog of
  `openTripleXP`.

Erasing the stores of traps (`StratSession.eraseEnd`) projects the session closure onto
`wasmEvFunXP`, with the same logs (`Silmaril.Wasm.Abstract.HostClosingS.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes)
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- **The functions of a store with host calls as imports, traps keeping the store**: the answer
`.inr ()` is a trap. -/
abbrev wasmHShapeS (H : Type) : Silmaril.Games.Abstract.Shape.{0} :=
  ⟨wasmHostSig H, Store H, Nat, fun _ => List Val, fun _ => (List Val ⊕ Nat) ⊕ PUnit⟩

/-- A recorded call of the session open module. -/
abbrev SCall (H : Type) : Type := Call ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self)

/-- The internal call of the function at `a` on `args` in store `s`, answered by `b` and the store
`s'`. -/
def SCall.mk (a : Nat) (args : List Val) (s : Store H) (b : (List Val ⊕ Nat) ⊕ PUnit.{1})
    (s' : Store H) : SCall H :=
  ⟨.inr ⟨a, (args, s)⟩, (b, s')⟩

/-- **The logged canonical relation with trap answers**: `EvalLXPh`'s rules over session answers,
every call an open call answered by values `inl (inl ws)`, an exception `inl (inr t)` raised at
the call, or a trap `inr ()` of the callee, the caller then trapping at once. No cut rules. -/
inductive EvalLXPS : Store H → Frame → List Val → List BExpr → List (SCall H) →
    Store H × Frame × POut → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} :
      EvalLXPS s f stk [] [] (s, f, .flow (.normal stk))
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {o : POut} {l : List (SCall H)} (hargs : EvalLXPS s f stk args l (s₁, f₁, o))
      (ho : ¬ o.IsNormal) :
      EvalLXPS s f stk (.op i args :: es) l (s₁, f₁, o)
  /-- `call x` answered by returned values. -/
  | callRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (SCall H)} {r : Store H × Frame × POut}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hk : EvalLXPS s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLXPS s f stk (.op (.call x) args :: es)
        (l₁ ++ SCall.mk a (stk₁.take ps.length).reverse s₁ (.inl (.inl ws)) s₂ :: l₂) r
  /-- `call x` answered by an exception, raised at the call. -/
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {t : Nat} {l₁ : List (SCall H)}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLXPS s f stk (.op (.call x) args :: es)
        (l₁ ++ [SCall.mk a (stk₁.take ps.length).reverse s₁ (.inl (.inr t)) s₂]) (s₂, f₁, .flow (.throw t))
  /-- `call x` answered by a trap of the callee, leaving its store: the caller traps
  at once, outside every handler. -/
  | callTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ : List (SCall H)}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      EvalLXPS s f stk (.op (.call x) args :: es)
        (l₁ ++ [SCall.mk a (stk₁.take ps.length).reverse s₁ (.inr ()) s₂]) (s₂, f₁, .flow .trap)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (SCall H)} {r : Store H × Frame × POut}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalLXPS s₂ f₂ stk₂ es l₂ r) :
      EvalLXPS s f stk (.op i args :: es) (l₁ ++ l₂) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} {l : List (SCall H)} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalLXPS s f stk (.op i args :: es) l (s₂, f₂, .flow fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (SCall H)}
      {r : Store H × Frame × POut} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) (hk : EvalLXPS s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLXPS s f stk (.block bt body :: es) (l₁ ++ l₂) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (SCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalLXPS s f stk (.block bt body :: es) l (s₁, f₁, .flow (.brk k vs))
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {o : POut} {l : List (SCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, o)) (ho : o.Escapes) :
      EvalLXPS s f stk (.block bt body :: es) l (s₁, f₁, o)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (SCall H)} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow (.normal vs)))
      (hk : EvalLXPS s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLXPS s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (SCall H)} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow (.brk 0 vs)))
      (hk : EvalLXPS s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ r) :
      EvalLXPS s f stk (.loop bt body :: es) (l₁ ++ l₂) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} {l : List (SCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalLXPS s f stk (.loop bt body :: es) l (s₁, f₁, .flow (.brk k vs))
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {o : POut} {l : List (SCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, o)) (ho : o.Escapes) :
      EvalLXPS s f stk (.loop bt body :: es) l (s₁, f₁, o)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (SCall H)} {r : Store H × Frame × POut}
      (hc : EvalLXPS s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPS s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, .flow fl))
      (hvs : fl.blockVals = some vs)
      (hk : EvalLXPS s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ r) :
      EvalLXPS s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat} {l₁ l₂ : List (SCall H)}
      (hc : EvalLXPS s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPS s₁ f₁ (stk₁.take np) (if b then t else el) l₂
        (s₂, f₂, .flow (.brk (k + 1) vs))) :
      EvalLXPS s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, .flow (.brk k vs))
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {o : POut} {l₁ l₂ : List (SCall H)}
      (hc : EvalLXPS s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPS s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, o))
      (ho : o.Escapes) :
      EvalLXPS s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) (s₂, f₂, o)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {o : POut} {l : List (SCall H)}
      (hc : EvalLXPS s f stk c l (s₁, f₁, o)) (ho : ¬ o.IsNormal) :
      EvalLXPS s f stk (.if_ bt c t el :: es) l (s₁, f₁, o)
  /-- A resolved `call_indirect x y` answered by returned values. -/
  | indRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ l₂ : List (SCall H)}
      {r : Store H × Frame × POut}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hk : EvalLXPS s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLXPS s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl (.inl ws)) s₂ :: l₂) r
  /-- A resolved `call_indirect x y` answered by an exception, raised at the call. -/
  | indThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {t : Nat}
      {l₁ : List (SCall H)}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPS s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ [SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl (.inr t)) s₂])
        (s₂, f₁, .flow (.throw t))
  /-- A resolved `call_indirect x y` answered by a trap of the callee, leaving its store: the
  caller traps at once, outside every handler. -/
  | indTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ : List (SCall H)}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPS s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ [SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr ()) s₂]) (s₂, f₁, .flow .trap)
  /-- An unresolved `call_indirect` traps, making no call. -/
  | indRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
      {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width} {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i none) :
      EvalLXPS s f stk (.op (.callIndirect x y) args :: es) l (s₁, f₁, .flow .trap)
  /-- `call_ref y` on a function reference, answered by returned values. -/
  | refRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (SCall H)} {r : Store H × Frame × POut}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hk : EvalLXPS s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ r) :
      EvalLXPS s f stk (.op (.callRef y) args :: es)
        (l₁ ++ SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl (.inl ws)) s₂ :: l₂) r
  /-- `call_ref y` answered by an exception, raised at the call. -/
  | refThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {t : Nat} {l₁ : List (SCall H)}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPS s f stk (.op (.callRef y) args :: es)
        (l₁ ++ [SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl (.inr t)) s₂])
        (s₂, f₁, .flow (.throw t))
  /-- `call_ref y` answered by a trap of the callee, leaving its store: the caller traps
  at once, outside every handler. -/
  | refTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ : List (SCall H)}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPS s f stk (.op (.callRef y) args :: es)
        (l₁ ++ [SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr ()) s₂]) (s₂, f₁, .flow .trap)
  /-- `call_ref` on null traps, making no call. -/
  | refNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal (.ref .null :: stk₁)))) :
      EvalLXPS s f stk (.op (.callRef y) args :: es) l (s₁, f₁, .flow .trap)
  /-- **A tail call** to a resolved callee: the body ends in the pending tail call, making no
  call here. -/
  | tail {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalLXPS s f stk (.op i args :: es) l
        (s₁, f₁, .tail fa ((stk₁.drop (tailPop i)).take ps.length).reverse rs.length)
  | tailRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (hres : TailRes s₁ f₁ i stk₁ none) :
      EvalLXPS s f stk (.op i args :: es) l (s₁, f₁, .flow .trap)
  | throw {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TagIdx}
      {args es : List BExpr} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
      {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (ht : s₁.tag? f₁ x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
      (hn : ts.length ≤ stk₁.length) :
      EvalLXPS s f stk (.op (.throw x) args :: es) l
        (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩, f₁, .flow (.throw s₁.exns.length))
  | throwRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {args es : List BExpr}
      {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal (.ref .null :: stk₁)))) :
      EvalLXPS s f stk (.op .throwRef args :: es) l (s₁, f₁, .flow .trap)
  | throwRefExn {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {a : Nat}
      {args es : List BExpr} {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal (.ref (.exn a) :: stk₁)))) :
      EvalLXPS s f stk (.op .throwRef args :: es) l (s₁, f₁, .flow (.throw a))
  | tryOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (SCall H)}
      {r : Store H × Frame × POut} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) (hk : EvalLXPS s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ r) :
      EvalLXPS s f stk (.tryTable bt cs body :: es) (l₁ ++ l₂) r
  | tryBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr k : Nat} {l : List (SCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalLXPS s f stk (.tryTable bt cs body :: es) l (s₁, f₁, .flow (.brk k vs))
  /-- A return, a trap or a pending tail call passes through the handler untouched. -/
  | tryEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {o : POut} {l : List (SCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, o)) (ho : o.Escapes)
      (hnt : o.NotThrow) :
      EvalLXPS s f stk (.tryTable bt cs body :: es) l (s₁, f₁, o)
  | tryCatch {s s₁ : Store H} {f f₁ : Frame} {stk us : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat} {l' : LabelIdx}
      {l : List (SCall H)} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, .flow (.throw a)))
      (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l'))) :
      EvalLXPS s f stk (.tryTable bt cs body :: es) l
        (s₁, f₁, .flow (.brk l'.toNat (us.reverse ++ stk.drop np)))
  | tryRethrow {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat} {l : List (SCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l (s₁, f₁, .flow (.throw a)))
      (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
      EvalLXPS s f stk (.tryTable bt cs body :: es) l (s₁, f₁, .flow (.throw a))

/-- **The end of a function whose exit flow is `fl`**, in store `s`, a trap keeping `s`. -/
def endOfFlowS (fl : Flow) (s : Store H) : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  match fl with
  | .throw t => .ret (.inl (.inr t)) s
  | .trap => .ret (.inr ()) s
  | .normal ws | .brk _ ws | .ret ws => .ret (.inl (.inl ws)) s

/-- **The end of a frame left by a pending tail call** of result arity `n`, in a function of result
arity `m`, from the tail call's answer `(b, s')`, as `tailAns`: a trap answer traps, keeping
`s'`. -/
def tailAnsS (m n : Nat) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}) (s' : Store H) :
    End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  match b with
  | .inl b =>
    match exitFlow m (CallX.tailFlow n (ansFlow b)) with
    | some fl => endOfFlowS fl s'
    | none => .ret (.inr ()) s'
  | .inr _ => .ret (.inr ()) s'

/-- **The functions of a store under the canonical relation, host functions as imports, traps
keeping the store.** -/
def wasmHOpenXPS : (wasmHShapeS H).OpenMod := fun a s vs =>
  {x | (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s' : Store H)
      (f₂ : Frame) (bfl fl : Flow) (l : List (SCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      EvalLXPS s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l
        (s', f₂, .flow bfl) ∧
      exitFlow rs.length bfl = some fl ∧ x = (l, endOfFlowS fl s')) ∨
    (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s₁ s₂ : Store H)
      (f₂ : Frame) (a' n : Nat) (args : List Val) (b : (List Val ⊕ Nat) ⊕ PUnit.{1})
      (l : List (SCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      EvalLXPS s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l
        (s₁, f₂, .tail a' args n) ∧
      x = (l ++ [SCall.mk a' args s₁ b s₂], tailAnsS rs.length n b s₂)) ∨
    (∃ (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType) (s' : Store H) (r : Result)
      (fl : Flow),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length (resFlow r) = some fl ∧
      x = ([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlowS fl s'))}

/-- **The session semantics of an invocation**: host calls as events, internal calls closed, a
trap keeping the store it leaves (`.ret (.inr ()) s'`). -/
def wasmEvFunXPS :
    AFun (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  fun s p => Shape.close wasmHOpenXPS p.1 s p.2

/-! ## Pending host calls -/

/-- **The trees reach the internal call `z`** after a logged session prefix (`EvalLXPS`): as
`ReachLXP`, over the session relation. The prefix runs end normally, so no call before `z` is
answered by a trap. -/
inductive ReachLXPS : Store H → Frame → List Val → List BExpr → List (SCall H) →
    (wasmOShape H).self.Op → Prop where
  /-- At `call x`. -/
  | call {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l : List (SCall H)} (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachLXPS s f stk (.op (.call x) args :: es) l ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩
  /-- At a resolved `call_indirect x y`. -/
  | ind {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      ReachLXPS s f stk (.op (.callIndirect x y) args :: es) l
        ⟨fa, ((stk₁.take ps.length).reverse, s₁)⟩
  /-- At `call_ref y` on a function reference. -/
  | ref {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l : List (SCall H)}
      (hargs : EvalLXPS s f stk args l (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      ReachLXPS s f stk (.op (.callRef y) args :: es) l ⟨fa, ((stk₁.take ps.length).reverse, s₁)⟩
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {l : List (SCall H)} {z : (wasmOShape H).self.Op} :
      ReachLXPS s f stk args l z → ReachLXPS s f stk (.op i args :: es) l z
  | callK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (SCall H)} {z : (wasmOShape H).self.Op}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachLXPS s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ z →
      ReachLXPS s f stk (.op (.call x) args :: es)
        (l₁ ++ SCall.mk a (stk₁.take ps.length).reverse s₁ (.inl (.inl ws)) s₂ :: l₂) z
  | indK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ l₂ : List (SCall H)}
      {z : (wasmOShape H).self.Op}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      ReachLXPS s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ z →
      ReachLXPS s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl (.inl ws)) s₂ :: l₂) z
  | refK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (SCall H)} {z : (wasmOShape H).self.Op}
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      ReachLXPS s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ z →
      ReachLXPS s f stk (.op (.callRef y) args :: es)
        (l₁ ++ SCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl (.inl ws)) s₂ :: l₂) z
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (SCall H)} {z : (wasmOShape H).self.Op}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLXPS s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      ReachLXPS s₂ f₂ stk₂ es l₂ z → ReachLXPS s f stk (.op i args :: es) (l₁ ++ l₂) z
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (SCall H)} {z : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) :
      ReachLXPS s f (stk.take np) body l z → ReachLXPS s f stk (.block bt body :: es) l z
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (SCall H)}
      {z : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) :
      ReachLXPS s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ z →
      ReachLXPS s f stk (.block bt body :: es) (l₁ ++ l₂) z
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (SCall H)} {z : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) :
      ReachLXPS s f (stk.take np) body l z → ReachLXPS s f stk (.loop bt body :: es) l z
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (SCall H)} {z : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow (.normal vs))) :
      ReachLXPS s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ z →
      ReachLXPS s f stk (.loop bt body :: es) (l₁ ++ l₂) z
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (SCall H)} {z : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow (.brk 0 vs))) :
      ReachLXPS s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ z →
      ReachLXPS s f stk (.loop bt body :: es) (l₁ ++ l₂) z
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {l : List (SCall H)} {z : (wasmOShape H).self.Op} :
      ReachLXPS s f stk c l z → ReachLXPS s f stk (.if_ bt c t el :: es) l z
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {l₁ l₂ : List (SCall H)}
      {z : (wasmOShape H).self.Op}
      (hc : EvalLXPS s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      ReachLXPS s₁ f₁ (stk₁.take np) (if b then t else el) l₂ z →
      ReachLXPS s f stk (.if_ bt c t el :: es) (l₁ ++ l₂) z
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (SCall H)} {z : (wasmOShape H).self.Op}
      (hc : EvalLXPS s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPS s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, .flow fl))
      (hvs : fl.blockVals = some vs) :
      ReachLXPS s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ z →
      ReachLXPS s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃) z
  /-- Inside a handler. -/
  | handler {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {l : List (SCall H)} {z : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) :
      ReachLXPS s f (stk.take np) body l z → ReachLXPS s f stk (.tryTable bt cs body :: es) l z
  | tryK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (SCall H)}
      {z : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPS s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) :
      ReachLXPS s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ z →
      ReachLXPS s f stk (.tryTable bt cs body :: es) (l₁ ++ l₂) z

/-- **A pending host call of an invocation under the session relation**, as `PendLXP`, after the host calls
`cs`: a host function invoked directly; or the pending call of a callee reached in a Wasm body,
the body's completed calls resolved against the closure (`desc`); or the pending call of the
callee of the body's pending tail call, made at the frame after the body's calls (`tail`; a host
tail callee is pending there, as the same self call). -/
inductive PendLXPS : Store H → Nat → List Val → List (Call (wasmHostSig H)) →
    (wasmHostSig H).Op → Prop where
  | self {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {hh : H}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) : PendLXPS s a vs [] (hh, s, vs)
  | desc {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func}
      {l : List (SCall H)} {q q' : List (Call (wasmHostSig H))} {z : (wasmOShape H).self.Op}
      {m : (wasmHostSig H).Op}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
      (hr : ReachLXPS s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l z)
      (hq : Shape.SubstPre (Shape.close wasmHOpenXPS) l q) :
      PendLXPS z.2.2 z.1 z.2.1 q' m → PendLXPS s a vs (q ++ q') m
  | tail {s s₁ : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func}
      {f₂ : Frame} {a' n : Nat} {args : List Val} {l : List (SCall H)}
      {q q' : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
      (hbody : EvalLXPS s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l
        (s₁, f₂, .tail a' args n))
      (hq : Shape.SubstPre (Shape.close wasmHOpenXPS) l q) :
      PendLXPS s₁ a' args q' m → PendLXPS s a vs (q ++ q') m

/-- **The pending host calls of an invocation under the session relation.** -/
def wasmEvPendXPS : Silmaril.Games.Abstract.Pending (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => {x | PendLXPS s p.1 p.2 x.1 x.2}

/-! ## The session triple -/

/-- **The session semantics of an invocation with divergence**: the session closure, and the
divergent behaviours of `wasmEvFunDXP`, which carry no trap store. -/
def wasmEvFunDXPS :
    AFun (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  fun s p => wasmEvFunXPS s p ∪ {y | y.2 = .div ∧ (y.1, End.div) ∈ wasmEvFunDXP s p}

/-- **The session triple**: finished and divergent behaviours keeping trap stores
(`wasmEvFunDXPS`), the session pending calls (`wasmEvPendXPS`), and the productive streams of
`wasmEvInfNXP`, which carry no trap store. -/
def sessionTripleXP :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  (wasmEvFunDXPS, wasmEvPendXPS, wasmEvInfNXP)

end Silmaril.Wasm.Abstract
