module

public import Silmaril.Wasm.Abstract.CallX.Defs

/-!
# The extended relation with typed callee arities (F4, call forms)

`CallX.EvalOX` resolves the callee of `call_indirect x y` and `call_ref y` at
run time and calls it at its own type. The arity checker extension describes
these instructions by the annotated type `y`. Core 3.0's `ref.cast` makes the
two agree for `call_indirect` on typed stores; for `call_ref` the agreement is a
typing fact about the reference on the stack.

`EvalOXT C` is `EvalOX C` whose indirect and reference calls additionally
record that agreement (`typeArity f.module y = some (ps.length, rs.length)` for
the callee's type `(ps, rs)`; for the tail forms `return_call_indirect x y` and
`return_call_ref y` the same, `tailAnn`). It is a *stronger derivation*, not another
semantics: every `EvalOXT` run is an `EvalOX` run with the same outcome
(`EvalOXT.forget`), and on code without these forms (`irFree`) the two are
the same (`Silmaril.Wasm.Abstract.CallXT.Thms`). That typed, validated code
runs in `EvalOXT` is the discharge of the premise, from typing.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.CallXT

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX

variable {H : Type}

/-- The parameter and result counts of the function type `y` of a module instance. -/
def typeArity (mi : ModuleInst) (y : TypeIdx) : Option (Nat × Nat) :=
  (mi.types[y.toNat]?).bind fun d =>
    (Validation.DefType.funcType? d).map fun p => (p.1.length, p.2.length)

/-- The type annotation of an indirect or reference tail call. -/
def tailAnn : Instr → Option TypeIdx
  | .returnCallIndirect _ y | .returnCallRef y => some y
  | _ => none

/-- **The extended oracle relation, with typed callee arities**: `EvalOX`'s
rules, where an indirect or reference call additionally records that its
resolved callee's parameter and result counts are those of the annotated type
`y` (`typeArity`). -/
inductive EvalOXT (C : CallRel H) : Store H → Frame → List Val → List BExpr → Store H × Frame × Flow → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalOXT C s f stk [] (s, f, .normal stk)
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {fl : Flow} (hargs : EvalOXT C s f stk args (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOXT C s f stk (.op i args :: es) (s₁, f₁, fl)
  | callOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
      (hvs : fl.retVals = some vs)
      (hk : EvalOXT C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXT C s f stk (.op (.call x) args :: es) r
  | callTrap {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
      EvalOXT C s f stk (.op (.call x) args :: es) (s₂, f₁, .trap)
  | callThrow {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {t : Nat}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
      EvalOXT C s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {r : Store H × Frame × Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : EvalOXT C s₂ f₂ stk₂ es r) :
      EvalOXT C s f stk (.op i args :: es) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOXT C s f stk (.op i args :: es) (s₂, f₂, fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXT C s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOXT C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXT C s f stk (.block bt body :: es) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXT C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalOXT C s f stk (.block bt body :: es) (s₁, f₁, .brk k vs)
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXT C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalOXT C s f stk (.block bt body :: es) (s₁, f₁, fl)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXT C s f (stk.take np) body (s₁, f₁, .normal vs))
      (hk : EvalOXT C s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      EvalOXT C s f stk (.loop bt body :: es) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXT C s f (stk.take np) body (s₁, f₁, .brk 0 vs))
      (hk : EvalOXT C s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
      EvalOXT C s f stk (.loop bt body :: es) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : EvalOXT C s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      EvalOXT C s f stk (.loop bt body :: es) (s₁, f₁, .brk k vs)
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalOXT C s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      EvalOXT C s f stk (.loop bt body :: es) (s₁, f₁, fl)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hc : EvalOXT C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXT C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) (hk : EvalOXT C s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
      EvalOXT C s f stk (.if_ bt c t el :: es) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat}
      (hc : EvalOXT C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXT C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .brk (k + 1) vs)) :
      EvalOXT C s f stk (.if_ bt c t el :: es) (s₂, f₂, .brk k vs)
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : EvalOXT C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalOXT C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl)) (hfl : fl.Escapes) :
      EvalOXT C s f stk (.if_ bt c t el :: es) (s₂, f₂, fl)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {fl : Flow}
      (hc : EvalOXT C s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      EvalOXT C s f stk (.if_ bt c t el :: es) (s₁, f₁, fl)

  /-- `call_indirect x y`: the callee resolved (`CallRes.IndRes`), then a returning call. -/
  | callIndOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOXT C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXT C s f stk (.op (.callIndirect x y) args :: es) r
  /-- `call_indirect x y` that does not resolve: a trap. -/
  | callIndRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx} {y : TypeIdx}
      {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i none) :
      EvalOXT C s f stk (.op (.callIndirect x y) args :: es) (s₁, f₁, .trap)
  /-- `call_indirect x y` whose callee traps or throws. -/
  | callIndStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal (.num ⟨.int ad.intType, i⟩ :: stk₁)))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOXT C s f stk (.op (.callIndirect x y) args :: es) (s₂, f₁, fl)
  /-- `call_ref y` on a function reference: a returning call. -/
  | callRefOk {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
      (hk : EvalOXT C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      EvalOXT C s f stk (.op (.callRef y) args :: es) r
  /-- `call_ref y` on null: a trap. -/
  | callRefNull {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal (.ref .null :: stk₁))) :
      EvalOXT C s f stk (.op (.callRef y) args :: es) (s₁, f₁, .trap)
  /-- `call_ref y` whose callee traps or throws. -/
  | callRefStop {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal (.ref (.func fa) :: stk₁)))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      EvalOXT C s f stk (.op (.callRef y) args :: es) (s₂, f₁, fl)
  /-- A tail call (`return_call`, `return_call_indirect`, `return_call_ref`) to a
  resolved callee: the callee's values (or abrupt flow) end the caller with a
  return. -/
  | tail {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {fl : Flow}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal stk₁))
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length))
      (hcall : C s₁ fa ((stk₁.drop (tailPop i)).take ps.length).reverse (s₂, fl))
      (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) :
      EvalOXT C s f stk (.op i args :: es) (s₂, f₁, tailFlow rs.length fl)
  /-- A tail call that does not resolve: a trap. -/
  | tailRes {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr}
      (hargs : EvalOXT C s f stk args (s₁, f₁, .normal stk₁)) (hres : TailRes s₁ f₁ i stk₁ none) :
      EvalOXT C s f stk (.op i args :: es) (s₁, f₁, .trap)

/-- An indirect or reference call, tail or not. -/
def irCall : Instr → Bool
  | .callIndirect _ _ | .callRef _ | .returnCallIndirect _ _ | .returnCallRef _ => true
  | _ => false

mutual

/-- No `call_indirect`, `call_ref`, `return_call_indirect` or `return_call_ref` in the tree. -/
def irFree : BExpr → Bool
  | .op i args => !irCall i && irFreeL args
  | .block _ body => irFreeL body
  | .loop _ body => irFreeL body
  | .if_ _ c t e => irFreeL c && irFreeL t && irFreeL e
  | .tryTable _ _ body => irFreeL body

/-- `irFree` on every tree of a list. -/
def irFreeL : List BExpr → Bool
  | [] => true
  | e :: es => irFree e && irFreeL es

end

/-- The function types of a store are valid. -/
def TyFuncs (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H), s.funcs[a]? = some fi → Validation.TyOk {} fi.type

/-- An oracle whose answers keep function types valid. -/
def KeepsTy (C : CallRel H) : Prop := ∀ s a args out, C s a args out → TyFuncs s → TyFuncs out.1

/-- The defined types of a module instance are valid. -/
def TyTypes (mi : ModuleInst) : Prop :=
  ∀ (y : Nat) (d : Validation.DefType), mi.types[y]? = some d → Validation.TyOk {} d

/-- The code of an instance's function: no `call_ref`/`return_call_ref`, and every
`call_indirect`/`return_call_indirect` names a type of the instance. -/
def indInstr (mi : ModuleInst) : Instr → Bool
  | .callRef _ | .returnCallRef _ => false
  | .callIndirect _ y | .returnCallIndirect _ y => (mi.types[y.toNat]?).isSome
  | _ => true

mutual

/-- `indInstr` on every instruction of the tree. -/
def indOk (mi : ModuleInst) : BExpr → Bool
  | .op i args => indInstr mi i && indOkL mi args
  | .block _ body => indOkL mi body
  | .loop _ body => indOkL mi body
  | .if_ _ c t e => indOkL mi c && indOkL mi t && indOkL mi e
  | .tryTable _ _ body => indOkL mi body

/-- `indOk` on every tree of a list. -/
def indOkL (mi : ModuleInst) : List BExpr → Bool
  | [] => true
  | e :: es => indOk mi e && indOkL mi es

end

end Silmaril.Wasm.Abstract.CallXT
