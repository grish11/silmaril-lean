module

public import Silmaril.Wasm.Abstract.CallX.Defs
public import Silmaril.Wasm.Cfg.Region.Defs

/-!
# The extended relation with exceptions (F5, semantics)

`EvalOXE C` is `CallX.EvalOX C` (every call form, answered by `C`) with exception handling:

* `throw x` allocates the exception with the tag's fields (bottom first) and throws it, as
  Core's `Step.throw` and `Cfg.Region.RunC.throw` do (`s.addExn ⟨ta, vs⟩`, address
  `s.exns.length`);
* `throw_ref` traps on null and rethrows an exception reference;
* `try_table bt cs body` runs its body as a block; a thrown exception is resolved by the
  handler clauses with **the existing first-match resolution** `Cfg.Region.Catches` (the
  `throw_ref-handler-*` rules): a match is a branch to the clause's label from outside the block,
  with the clause's values; no match rethrows.

Multiple values and block parameters are as in `EvalOX` (`arity` gives both counts of every
block type, `if` and `try_table` included).

It is a **conservative** extension: every `EvalOX` run is an `EvalOXE` run (`EvalOXE.of_evalOX`),
and on code without `throw`, `throw_ref` and `try_table` the two are the same
(`Silmaril.Wasm.Abstract.CallXE.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.CallXE

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.CallX

variable {H : Type}

/-- **The extended relation with exceptions.** -/
inductive EvalOXE (C : CallRel H) : Store H → Frame → List Val → List BExpr → Store H × Frame × Flow → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalOXE C s f stk [] (s, f, .normal stk)
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {fl : Flow} (hargs : EvalOXE C s f stk args (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOXE C s f stk (.op i args :: es) (s₁, f₁, fl)
  | callOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
      (hvs : fl.retVals = some vs)
      (hk : EvalOXE C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXE C s f stk (.op (.call x) args :: es) r
  | callTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
      EvalOXE C s f stk (.op (.call x) args :: es) (s₂, f₁, .trap)
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {t : Nat}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
      EvalOXE C s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {r : Store H × Frame × Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalOXE C s₂ f₂ stk₂ es r) :
      EvalOXE C s f stk (.op i args :: es) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOXE C s f stk (.op i args :: es) (s₂, f₂, fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOXE C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXE C s f stk (.block bt body :: es) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalOXE C s f stk (.block bt body :: es) (s₁, f₁, .brk k vs)
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalOXE C s f stk (.block bt body :: es) (s₁, f₁, fl)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, .normal vs))
      (hk : EvalOXE C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXE C s f stk (.loop bt body :: es) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, .brk 0 vs))
      (hk : EvalOXE C s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
      EvalOXE C s f stk (.loop bt body :: es) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalOXE C s f stk (.loop bt body :: es) (s₁, f₁, .brk k vs)
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalOXE C s f stk (.loop bt body :: es) (s₁, f₁, fl)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hc : EvalOXE C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXE C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOXE C s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
      EvalOXE C s f stk (.if_ bt c t el :: es) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat}
      (hc : EvalOXE C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXE C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .brk (k + 1) vs)) :
      EvalOXE C s f stk (.if_ bt c t el :: es) (s₂, f₂, .brk k vs)
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : EvalOXE C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXE C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl)) (hfl : fl.Escapes) :
      EvalOXE C s f stk (.if_ bt c t el :: es) (s₂, f₂, fl)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {fl : Flow}
      (hc : EvalOXE C s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOXE C s f stk (.if_ bt c t el :: es) (s₁, f₁, fl)

  /-- `call_indirect x y`: the callee resolved (`CallRes.IndRes`), then a returning call. -/
  | callIndOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOXE C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXE C s f stk (.op (.callIndirect x y) args :: es) r
  /-- `call_indirect x y` that does not resolve: a trap. -/
  | callIndRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
      {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i none) :
      EvalOXE C s f stk (.op (.callIndirect x y) args :: es) (s₁, f₁, .trap)
  /-- `call_indirect x y` whose callee traps or throws. -/
  | callIndStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOXE C s f stk (.op (.callIndirect x y) args :: es) (s₂, f₁, fl)
  /-- `call_ref y` on a function reference: a returning call. -/
  | callRefOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOXE C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXE C s f stk (.op (.callRef y) args :: es) r
  /-- `call_ref y` on null: a trap. -/
  | callRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.ref .null :: stk₁))) :
      EvalOXE C s f stk (.op (.callRef y) args :: es) (s₁, f₁, .trap)
  /-- `call_ref y` whose callee traps or throws. -/
  | callRefStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOXE C s f stk (.op (.callRef y) args :: es) (s₂, f₁, fl)
  /-- A tail call (`return_call`, `return_call_indirect`, `return_call_ref`) to a
  resolved callee: the callee's values (or abrupt flow) end the caller with a
  return. -/
  | tail {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁))
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ fa ((stk₁.drop (tailPop i)).take ps.length).reverse (s₂, fl))
      (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) :
      EvalOXE C s f stk (.op i args :: es) (s₂, f₁, tailFlow rs.length fl)
  /-- A tail call that does not resolve: a trap. -/
  | tailRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁)) (hres : TailRes s₁ f₁ i stk₁ none) :
      EvalOXE C s f stk (.op i args :: es) (s₁, f₁, .trap)


  /-- `throw x`: the exception is allocated with the tag's fields (bottom first), and thrown
  (`Step.throw`, `Region.RunC.throw`). -/
  | throw {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TagIdx}
      {args es : List BExpr} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal stk₁))
      (ht : s₁.tag? f₁ x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
      (hn : ts.length ≤ stk₁.length) :
      EvalOXE C s f stk (.op (.throw x) args :: es)
        (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩, f₁, .throw s₁.exns.length)
  /-- `throw_ref` on null: a trap. -/
  | throwRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {args es : List BExpr}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.ref .null :: stk₁))) :
      EvalOXE C s f stk (.op .throwRef args :: es) (s₁, f₁, .trap)
  /-- `throw_ref` on an exception reference: it is thrown again. -/
  | throwRefExn {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {a : Nat}
      {args es : List BExpr}
      (hargs : EvalOXE C s f stk args (s₁, f₁, .normal (.ref (.exn a) :: stk₁))) :
      EvalOXE C s f stk (.op .throwRef args :: es) (s₁, f₁, .throw a)
  /-- `try_table bt cs body` whose body exits as a block's does: the continuation runs. -/
  | tryOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, fl)) (hvs : fl.blockVals = some vs)
      (hk : EvalOXE C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXE C s f stk (.tryTable bt cs body :: es) r
  /-- A branch past the `try_table` block. -/
  | tryBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr k : Nat} (har : arity f bt = some (np, nr))
      (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalOXE C s f stk (.tryTable bt cs body :: es) (s₁, f₁, .brk k vs)
  /-- A return or a trap passes through the handler. -/
  | tryEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} (har : arity f bt = some (np, nr))
      (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, fl)) (hfl : fl.Escapes)
      (hnt : ∀ a, fl ≠ .throw a) :
      EvalOXE C s f stk (.tryTable bt cs body :: es) (s₁, f₁, fl)
  /-- A thrown exception caught by the first matching clause (`Cfg.Region.Catches`): a branch
  to its label, from outside the block, with the clause's values (bottom first) on the values
  below the block. -/
  | tryCatch {s s₁ : Store H} {f f₁ : Frame} {stk us : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat} {l : LabelIdx}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, .throw a))
      (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l))) :
      EvalOXE C s f stk (.tryTable bt cs body :: es)
        (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np))
  /-- No clause matches: the exception propagates. -/
  | tryRethrow {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {cs : List Catch} {body es : List BExpr} {np nr a : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXE C s f (stk.take np) body (s₁, f₁, .throw a))
      (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
      EvalOXE C s f stk (.tryTable bt cs body :: es) (s₁, f₁, .throw a)

/-- The exception instructions. -/
def ehInstr : Instr → Bool
  | .throw _ | .throwRef => true
  | _ => false

mutual

/-- No `throw`, `throw_ref` or `try_table` in the tree. -/
def ehFree : BExpr → Bool
  | .op i args => !ehInstr i && ehFreeL args
  | .block _ body => ehFreeL body
  | .loop _ body => ehFreeL body
  | .if_ _ c t e => ehFreeL c && ehFreeL t && ehFreeL e
  | .tryTable .. => false

/-- `ehFree` on every tree of a list. -/
def ehFreeL : List BExpr → Bool
  | [] => true
  | e :: es => ehFree e && ehFreeL es

end

end Silmaril.Wasm.Abstract.CallXE
