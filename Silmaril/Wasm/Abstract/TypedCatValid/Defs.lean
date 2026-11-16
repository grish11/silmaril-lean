module

public import Silmaril.Wasm.Abstract.TypedCat.Thms
public import Silmaril.Wasm.Validation.Modules
public import Silmaril.Wasm.Execution.Core.Typing.Store
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# The validation bridge for the typed category (F7)

`ExposePTyped` (#540), `TypedCat` (#543) and `TypedCatFit` (#545) prove the typed subcategory,
its closure, frame rule and answered tensor, with the run-time facts as premises: a typed
state (`Realizes Γ I s f stk`, hence `Coh Γ I`), typed code (`TMor Γ I J ft es`) and an
arity-respecting oracle (`ArityResp Γ (fitP closedCallXP)`). This topic discharges them for the
body of a Wasm function invoked in a Core-typed store (`StoreOk`) on typed arguments (`InvokeOk`).

**The store context** `storeCtx tags s h`: the tag instances `tags`, the store's functions, and
the checker's acceptance `h : StoreChkE (ehExt tags) s.funcs` (a field of `Ctx`).

**A validated body** `BodyOk s fi fn C ps rs lts`: what `StoreOk`'s `Funcinst_ok` says of a store
function `fi` whose code is the Wasm function `fn`: its module instance has the context `C`
(`ModuleInstOk`); `fn`'s type index names, in `C`, a defined type `d` expanding to `ps → rs` that
is a subtype of the store's type `fi.type`; the declared locals have the local types `lts`
(`Local_ok`), and the body is valid (`Expr_ok`) in `Func_ok`'s body context
`C.funcBody ps rs lts` (locals: the parameters, set, then `lts`; label and return: `rs`).

**The interfaces of a body.** `bodyIface mi C ps rs lts`: the instance `mi`, the body context and
the empty stack (a callee starts on the empty stack). `bodyEnd`: the same instance and context
(no local initialisation is recorded: `Func_ok` types the body `[] →_{[]} rs`) and the stack `rs`.

**A typed body** `TypedBody Γ I J ft s f es`: everything the typed category says of the code `es`
at the state `s`, `f` on the empty stack: the state is typed (`Realizes`) and so coherent at both
ends, `es` is a typed morphism `I → J` (falling through at `J` when `ft`, never otherwise), a typed
problem (`Interp.TypedP`), typed with any valid value types below (the frame rule), and the
closure `closedCallXP` is an oracle for the answered tensor at this state: the runs on a passive
stack `rest` read at the targets' arities are the whiskered runs on the empty stack.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.TypedCatValid

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Validation (Context CValType LocalType LocalOk ExprOk Expand Sub Ty ResultOk)

variable {H : Type}

/-- **The store context** of `s`: the tag instances `tags` and the store's functions, accepted by
the exception checker. -/
def storeCtx (tags : List TagInst) (s : Store H) (h : StoreChkE (ehExt tags) s.funcs) : Ctx H :=
  ⟨tags, s.funcs, h⟩

/-- **A validated function body**: `Funcinst_ok` of a store function with Wasm code `fn`, with
the module context `C`, the function type `ps → rs` of `fn` and the local types `lts`. -/
structure BodyOk (s : Store H) (fi : FuncInst H) (fn : Func) (C : Context)
    (ps rs : Ty (.list .val)) (lts : List LocalType) : Prop where
  /-- The store function's code is `fn`. -/
  code : fi.code = .wasm fn
  /-- The module instance has the context `C`. -/
  module : ModuleInstOk s fi.module C
  /-- `fn`'s type expands to `ps → rs`, a subtype of the store's type. -/
  type : ∃ d, C.type? fn.type = some d ∧ Expand d (.func ps rs) ∧ Sub C.toTypeCtx d fi.type
  /-- The declared locals have the local types `lts`. -/
  locals : List.Forall₂ (LocalOk C) fn.locals lts
  /-- The body is valid in `Func_ok`'s body context, at the results `rs`. -/
  body : ExprOk (C.funcBody ps.toList rs.toList lts) fn.body rs.toList

/-- **The entry interface of a body**: the instance, `Func_ok`'s body context, the empty stack. -/
def bodyIface (mi : ModuleInst) (C : Context) (ps rs : List CValType) (lts : List LocalType) :
    TIface :=
  ⟨mi, C.funcBody ps rs lts, []⟩

/-- **The exit interface of a body**: the instance, the body context, the result stack. -/
def bodyEnd (mi : ModuleInst) (C : Context) (ps rs : List CValType) (lts : List LocalType) :
    TIface :=
  ⟨mi, (C.funcBody ps rs lts).initLocals [], rs⟩

/-- **A typed body**: a typed entry state, a typed morphism with its frame rule, a typed problem,
and the closure an oracle for the answered tensor at the entry state. -/
structure TypedBody (Γ : Ctx H) (I J : TIface) (ft : Bool) (s : Store H) (f : Frame)
    (es : List BExpr) : Prop where
  /-- The entry state is typed. -/
  realizes : Realizes Γ I s f []
  /-- The entry interface is coherent with the store context. -/
  coh : Coh Γ I
  /-- The code is a typed morphism. -/
  tmor : TMor Γ I J ft es
  /-- The exit interface is coherent with the store context. -/
  cohEnd : Coh Γ J
  /-- The code is a typed problem at the entry state. -/
  typedP : TypedP Γ.tags s f [] es
  /-- The typed frame rule. -/
  frame : ∀ R : List CValType, ResultOk I.C.toTypeCtx R →
    TMor Γ (I.withBelow R) (J.withBelow R) ft es
  /-- The closure on fitting calls respects arities. -/
  oracle : ArityResp Γ (fitP closedCallXP)
  /-- The answered tensor under the closure, at the entry state. -/
  tensor : ∀ (rest : List Val) (s' : Store H) (f' : Frame) (X : POut),
    (∃ o', EvalOXP closedCallXP s f rest es (s', f', o') ∧ trimO I.env.labels I.env.ret o' = X) ↔
      ∃ o, EvalOXP closedCallXP s f [] es (s', f', o) ∧
        trimO I.env.labels I.env.ret (whiskO rest o) = X

end Silmaril.Wasm.Abstract.TypedCatValid
