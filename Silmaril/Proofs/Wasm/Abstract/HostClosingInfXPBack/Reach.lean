module

public import Silmaril.Wasm.Interp.PProgress.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms

/-!
# Closed reaches of a host call, and their Core runs (proofs)

The closed canonical semantics `CallXP.EvalOXP closedCallXP` answers Wasm callees only. A problem
or call **reaches a host call** in it (`HReach`, `HCallReach`) when, along the unfoldings of
`XDivergeP.DivStepXP` and `XDivergeP.CallStepXP` (the terminating parts run in the closed
semantics), it calls a host function: the unfoldings are the constructors, and a call to a host
function is the base case (`HCallReach.host`).

* `hreach_core`: on checked code, a reach is a Core run, under any host and in any active
  context, to a configuration at a host call (`decompose?`). The steps are those of the forward
  divergence simulation `Interp.progressP`, ending at the host call;
* `not_hreach_of_diverges`, `not_hcallReach_of_diverges`: so a problem or call whose Core run
  diverges host-free (deterministic profile) reaches no host call: the run to the host call ends
  in a configuration with no host-free step;
* `no_outcome_of_diverges`, `no_answer_of_diverges`: and has no closed outcome or answer: its Core
  run would end in a final form.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Binaryen (BExpr liftInstrs truthy)

variable {H : Type}

/-! ## Closed reaches of a host call -/

mutual

/-- **A problem reaches a host call** in the closed canonical semantics: along the unfoldings of
`DivStepXP`, a callee reaching one. -/
inductive HReach : Store H → Frame → List Val → List BExpr → Prop where
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr} :
      HReach s f stk args → HReach s f stk (.op i args :: es)
  | cont {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {e : BExpr} {es : List BExpr}
      (hd : EvalOXP closedCallXP s f stk [e] (s₂, f₂, .flow (.normal stk₂))) :
      HReach s₂ f₂ stk₂ es → HReach s f stk (e :: es)
  | callee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      HCallReach s₁ a (stk₁.take ps.length).reverse → HReach s f stk (.op (.call x) args :: es)
  | callIndCallee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP closedCallXP s f stk args
        (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : Silmaril.Wasm.Abstract.CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      HCallReach s₁ fa (stk₁.take ps.length).reverse →
      HReach s f stk (.op (.callIndirect x y) args :: es)
  | callRefCallee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalOXP closedCallXP s f stk args (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      HCallReach s₁ fa (stk₁.take ps.length).reverse → HReach s f stk (.op (.callRef y) args :: es)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr)) :
      HReach s f (stk.take np) body → HReach s f stk (.block bt body :: es)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr)) :
      HReach s f (stk.take np) body → HReach s f stk (.loop bt body :: es)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
      (hbody : EvalOXP closedCallXP s f (stk.take np) body (s₁, f₁, .flow (.brk 0 vs))) :
      HReach s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) →
      HReach s f stk (.loop bt body :: es)
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} :
      HReach s f stk c → HReach s f stk (.if_ bt c t el :: es)
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat}
      (hc : EvalOXP closedCallXP s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr)) :
      HReach s₁ f₁ (stk₁.take np) (if b then t else el) → HReach s f stk (.if_ bt c t el :: es)
  | try_ {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr)) :
      HReach s f (stk.take np) body → HReach s f stk (.tryTable bt cs body :: es)

/-- **A call reaches a host call** in the closed canonical semantics: it is one, or its body
reaches one, or its body ends in a pending tail call whose call reaches one. -/
inductive HCallReach : Store H → Nat → List Val → Prop where
  | host {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H} {hh : H}
      (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) : HCallReach s a args
  | body {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H} {fn : Func}
      (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
      HReach s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) →
      HCallReach s a args
  | frameTail {s s₁ : Store H} {a a' n : Nat} {args args' : List Val} {fi : FuncInst H}
      {fn : Func} {f₂ : Frame} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
      (hbody : EvalOXP closedCallXP s (Frame.forCall fi.module args fn.locals) []
        (liftInstrs fn.body) (s₁, f₂, .tail a' args' n)) :
      HCallReach s₁ a' args' → HCallReach s a args

end

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
