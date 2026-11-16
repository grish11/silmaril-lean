module

public import Silmaril.Wasm.Abstract.CallXE.Defs
public import Silmaril.Wasm.Abstract.CallXT.Defs

/-!
# Pending tail calls (F5, semantics)

In Core 3.0 a tail call does not run where it is made: `return_call_ref` leaves every enclosing
label (`return_call_ref-label`) and **handler** (`return_call_ref-handler`) untouched, and only
the frame is replaced by the call (`return_call_ref-frame-addr`). So a tail callee's exception is
raised outside the caller's handlers: a `try_table` around a `return_call` does not catch it.

`CallXE.EvalOXE` answers a tail call at once (its `tail` rule asks the oracle and ends the body in
the callee's flow), so under a `try_table` a tail callee's exception would be caught. This module
gives the faithful semantics, additively (the result type `Flow` of the existing relations is not
changed):

* `POut`: a body result is a flow or a **pending tail call** `tail a args n` (the callee's
  address, its arguments bottom first, its result arity), as `Cfg.Region.Out.tail`;
* `EvalOXP C`: `EvalOXE`'s rules (with `CallXT.EvalOXT`'s typed callee arities for the indirect,
  reference and tail call forms, `typeArity`/`tailAnn`: facts of validated code), where a resolved tail call ends the body in the pending tail
  call, **not** answered; a pending tail call passes every `block`, `loop`, `if` and `try_table`
  untouched (`Escapes`), and a handler catches only a thrown exception (`.flow (.throw a)`);
* `FrameP C`: leaving the frame, and only there, a pending tail call is answered by `C`, ending
  as the callee does (`tailFlow`, as `EvalOX`'s `tail` rule);
* `bodyCallXP`, `closedCallXP`: answering calls by running callees this way, and its least
  fixpoint.

On code without the extended call forms the new relation is `EvalOXE`
(`Silmaril.Wasm.Abstract.CallXP.Thms`). A tail call of null still traps where it is made, as in
`EvalOXE`: a trap passes every label and handler, which is Core's pending null tail call trapping
at the frame (`Cfg.Region.Out.tailNull`, `Logic.Core.Outcome.tailNull`), in the same store.

**Status: canonical F5 semantics.** Exceptions and every call form, tail calls pending until the
frame is left. Together with `Abstract.XRecursionP` (closure), `Abstract.ExposeP` (exact BodyM
denotation, body and frame level) and `Interp.PendSim` (Core 3.0 forward simulation and closure
soundness), this is the API the structure-preserving functor (F7) builds on. The older
`CallXE`/`XRecursionE`/`ExposeE`/`EHSim`/`EHClose` forms are legacy, valid on code without the
extended call forms.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.CallXP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)

variable {H : Type}

/-- **A body result**: a flow, or a pending tail call. -/
inductive POut where
  /-- The body ended with the flow `fl`. -/
  | flow (fl : Flow)
  /-- A pending tail call of the function at address `a` on the arguments `args` (bottom
  first), of result arity `n`: it replaces the frame, so it is made only when the frame is left. -/
  | tail (a : Nat) (args : List Val) (n : Nat)
  deriving Repr

/-- Falling through. -/
def POut.IsNormal : POut → Prop
  | .flow fl => fl.IsNormal
  | .tail .. => False

/-- Leaving every label and handler of the frame: a return, a trap, a thrown exception, or a
pending tail call. -/
def POut.Escapes : POut → Prop
  | .flow fl => fl.Escapes
  | .tail .. => True

/-- What a handler does not catch: everything but a thrown exception. -/
def POut.NotThrow : POut → Prop
  | .flow (.throw _) => False
  | _ => True

/-- **The relation with pending tail calls.** -/
inductive EvalOXP (C : CallRel H) :
    Store H → Frame → List Val → List BExpr → Store H × Frame × POut → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalOXP C s f stk [] (s, f, .flow (.normal stk))
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {o : POut} (hargs : EvalOXP C s f stk args (s₁, f₁, o)) (ho : ¬ o.IsNormal) :
      EvalOXP C s f stk (.op i args :: es) (s₁, f₁, o)
  | callOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {fl : Flow} {r : Store H × Frame × POut}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOXP C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXP C s f stk (.op (.call x) args :: es) r
  | callTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
      EvalOXP C s f stk (.op (.call x) args :: es) (s₂, f₁, .flow .trap)
  /-- An ordinary call whose callee throws: the exception is raised at the call, inside the
  caller's handlers. -/
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {t : Nat} (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
      EvalOXP C s f stk (.op (.call x) args :: es) (s₂, f₁, .flow (.throw t))
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {r : Store H × Frame × POut} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalOXP C s₂ f₂ stk₂ es r) :
      EvalOXP C s f stk (.op i args :: es) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOXP C s f stk (.op i args :: es) (s₂, f₂, .flow fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOXP C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXP C s f stk (.block bt body :: es) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalOXP C s f stk (.block bt body :: es) (s₁, f₁, .flow (.brk k vs))
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {o : POut} (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, o)) (ho : o.Escapes) :
      EvalOXP C s f stk (.block bt body :: es) (s₁, f₁, o)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow (.normal vs)))
      (hk : EvalOXP C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXP C s f stk (.loop bt body :: es) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow (.brk 0 vs)))
      (hk : EvalOXP C s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
      EvalOXP C s f stk (.loop bt body :: es) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat} (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalOXP C s f stk (.loop bt body :: es) (s₁, f₁, .flow (.brk k vs))
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {o : POut} (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, o)) (ho : o.Escapes) :
      EvalOXP C s f stk (.loop bt body :: es) (s₁, f₁, o)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {r : Store H × Frame × POut}
      (hc : EvalOXP C s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXP C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .flow fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOXP C s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
      EvalOXP C s f stk (.if_ bt c t el :: es) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat}
      (hc : EvalOXP C s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXP C s₁ f₁ (stk₁.take np) (if b then t else el)
        (s₂, f₂, .flow (.brk (k + 1) vs))) :
      EvalOXP C s f stk (.if_ bt c t el :: es) (s₂, f₂, .flow (.brk k vs))
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {o : POut}
      (hc : EvalOXP C s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁)))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXP C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, o)) (ho : o.Escapes) :
      EvalOXP C s f stk (.if_ bt c t el :: es) (s₂, f₂, o)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {o : POut}
      (hc : EvalOXP C s f stk c (s₁, f₁, o)) (ho : ¬ o.IsNormal) :
      EvalOXP C s f stk (.if_ bt c t el :: es) (s₁, f₁, o)
  | callIndOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      {r : Store H × Frame × POut}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOXP C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXP C s f stk (.op (.callIndirect x y) args :: es) r
  | callIndRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
      {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i none) :
      EvalOXP C s f stk (.op (.callIndirect x y) args :: es) (s₁, f₁, .flow .trap)
  | callIndStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOXP C s f stk (.op (.callIndirect x y) args :: es) (s₂, f₁, .flow fl)
  | callRefOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow} {r : Store H × Frame × POut}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOXP C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXP C s f stk (.op (.callRef y) args :: es) r
  | callRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.ref .null :: stk₁)))) :
      EvalOXP C s f stk (.op (.callRef y) args :: es) (s₁, f₁, .flow .trap)
  | callRefStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOXP C s f stk (.op (.callRef y) args :: es) (s₂, f₁, .flow fl)
  /-- **A tail call** (`return_call`, `return_call_indirect`, `return_call_ref`) to a resolved
  callee: the body ends in the pending tail call, which is **not** answered here. -/
  | tail {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length)) :
      EvalOXP C s f stk (.op i args :: es)
        (s₁, f₁, .tail fa ((stk₁.drop (tailPop i)).take ps.length).reverse rs.length)
  /-- A tail call that does not resolve: a trap (on null, Core's pending null tail call, which
  traps at the frame in the same store). -/
  | tailRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hres : TailRes s₁ f₁ i stk₁ none) :
      EvalOXP C s f stk (.op i args :: es) (s₁, f₁, .flow .trap)
  | throw {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TagIdx}
      {args es : List BExpr} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (ht : s₁.tag? f₁ x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
      (hn : ts.length ≤ stk₁.length) :
      EvalOXP C s f stk (.op (.throw x) args :: es)
        (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩, f₁, .flow (.throw s₁.exns.length))
  | throwRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {args es : List BExpr}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.ref .null :: stk₁)))) :
      EvalOXP C s f stk (.op .throwRef args :: es) (s₁, f₁, .flow .trap)
  | throwRefExn {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {a : Nat}
      {args es : List BExpr}
      (hargs : EvalOXP C s f stk args (s₁, f₁, .flow (.normal (.ref (.exn a) :: stk₁)))) :
      EvalOXP C s f stk (.op .throwRef args :: es) (s₁, f₁, .flow (.throw a))
  | tryOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow fl)) (hvs : fl.blockVals = some vs)
      (hk : EvalOXP C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXP C s f stk (.tryTable bt cs body :: es) r
  | tryBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr k : Nat} (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow (.brk (k + 1) vs))) :
      EvalOXP C s f stk (.tryTable bt cs body :: es) (s₁, f₁, .flow (.brk k vs))
  /-- A return, a trap or a **pending tail call** passes through the handler untouched. -/
  | tryEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {o : POut} (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, o)) (ho : o.Escapes) (hnt : o.NotThrow) :
      EvalOXP C s f stk (.tryTable bt cs body :: es) (s₁, f₁, o)
  | tryCatch {s s₁ : Store H} {f f₁ : Frame} {stk us : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat} {l : LabelIdx}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow (.throw a)))
      (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l))) :
      EvalOXP C s f stk (.tryTable bt cs body :: es)
        (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))
  | tryRethrow {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXP C s f (stk.take np) body (s₁, f₁, .flow (.throw a)))
      (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
      EvalOXP C s f stk (.tryTable bt cs body :: es) (s₁, f₁, .flow (.throw a))

/-- **Leaving the frame**: a flow ends the frame as it is; a pending tail call is answered by
`C`, here and only here, and the frame ends as the callee does (`tailFlow`). -/
inductive FrameP (C : CallRel H) : Store H × POut → Store H × Flow → Prop where
  | flow {s : Store H} {fl : Flow} : FrameP C (s, .flow fl) (s, fl)
  | tail {s s₂ : Store H} {a n : Nat} {args : List Val} {fl : Flow}
      (hcall : C s a args (s₂, fl)) (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) :
      FrameP C (s, .tail a args n) (s₂, tailFlow n fl)

/-- One round of answering calls by running callees with pending tail calls: the code at `a`
evaluated by `EvalOXP C` in a fresh frame, then the frame left (`FrameP`). -/
def bodyCallXP (C : CallRel H) : CallRel H := fun s a args out =>
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame)
    (s₁ : Store H) (o : POut),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalOXP C s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (s₁, f₂, o) ∧
    FrameP C (s₁, o) out

end Silmaril.Wasm.Abstract.CallXP
