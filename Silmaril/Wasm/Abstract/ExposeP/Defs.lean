module

public import Silmaril.Wasm.Abstract.ExposeE.Defs
public import Silmaril.Wasm.Abstract.CallXP.Defs

/-!
# The exposed body of the relation with pending tail calls (F5, exposure)

`denXP`/`denListXP` are the exposed `BodyM` body of `CallXP.EvalOXP`, in the monad of
`ExposeE` (`M (CallSig H) H`, every ordinary call a call event answered where it is made):

* the result object carries a body result `POut` (`ResP`): a flow, or a **pending tail call**
  `.tail fa args n`. A pending tail call is a value of the body, not an effect: it passes operator
  sequencing (`thenKP`), every `block` and `loop` (`blockKP`, `loopKP`), every `if` and every
  handler (`tryKP` resolves only a thrown exception) untouched, as Core 3.0's
  `return_call_ref-label` and `return_call_ref-handler` leave labels and handlers;
* the flat instructions, the exception operators and `call` are `ExposeE.opCXE`'s; `call_indirect`
  and `call_ref` are `CallX`'s, at the annotated type (`calleeTyped`, as `EvalOXP`'s typed rules);
* a tail call (`tailPendEv`) resolves its callee as `CallX.tailEv` does (`resolveTail`) and its
  type (with `tailTyped`, as `EvalOXP.tail`), and **returns** the pending call: no call event is
  made in the body. A tail call that does not resolve traps;
* the frame (`frameXP`) runs a callee body and only then makes the pending tail call's call event,
  ending as the callee does (`frameAns`, `FrameP.tail`), as Core 3.0's
  `return_call_ref-frame-addr` replaces the frame. A frame result is the store and the flow.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.ExposeP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.ExposeE
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.Body (getState setState trap callImport)

variable {H : Type}

/-- The result object with pending tail calls: the frame and the body result. -/
abbrev ResP : Type 1 := ULift.{1} (Frame × POut)

/-- A flow result as a body result. -/
def ofRes (r : Res) : ResP := ⟨(r.down.1, .flow r.down.2)⟩

/-- A computation with a flow result, read with body results. -/
noncomputable def liftP (x : M (CallSig H) H Res) : M (CallSig H) H ResP :=
  x >>= fun r => pure (ofRes r)

/-- Continue with `k` after a fallthrough; other flows and pending tail calls pass. -/
noncomputable def thenKP (k : Frame → List Val → M (CallSig H) H ResP) :
    ResP → M (CallSig H) H ResP
  | ⟨(f, .flow (.normal stk))⟩ => k f stk
  | r => pure r

/-- The exits of a `block`/`if` body (`StoreCall.blockK`); a pending tail call passes. -/
noncomputable def blockKP (np nr : Nat) (stk : List Val) : ResP → M (CallSig H) H ResP
  | ⟨(f, .flow (.normal vs))⟩ => pure ⟨(f, .flow (.normal (vs.take nr ++ stk.drop np)))⟩
  | ⟨(f, .flow (.brk 0 vs))⟩ => pure ⟨(f, .flow (.normal (vs.take nr ++ stk.drop np)))⟩
  | ⟨(f, .flow (.brk (k + 1) vs))⟩ => pure ⟨(f, .flow (.brk k vs))⟩
  | r => pure r

/-- The exits of a `loop` body (`StoreCall.loopK`); a pending tail call leaves. -/
noncomputable def loopKP (np nr : Nat) (stk : List Val) :
    ResP → M (CallSig H) H (ResP ⊕ ULift.{1} (Frame × List Val))
  | ⟨(f, .flow (.normal vs))⟩ => pure (.inl ⟨(f, .flow (.normal (vs.take nr ++ stk.drop np)))⟩)
  | ⟨(f, .flow (.brk 0 vs))⟩ => pure (.inr ⟨(f, vs.take np ++ stk.drop np)⟩)
  | ⟨(f, .flow (.brk (k + 1) vs))⟩ => pure (.inl ⟨(f, .flow (.brk k vs))⟩)
  | r => pure (.inl r)

/-- The exits of a `try_table` body (`ExposeE.tryK`): only a thrown exception is resolved by the
clauses `cs`; every other exit, a pending tail call included, is a block's. -/
noncomputable def tryKP (np nr : Nat) (stk : List Val) (cs : List Catch) :
    ResP → M (CallSig H) H ResP
  | ⟨(f, .flow (.throw a))⟩ =>
    getState >>= fun s =>
      match resolveCatch s.down f a cs with
      | some (some (us, l)) => pure ⟨(f, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))⟩
      | some none => pure ⟨(f, .flow (.throw a))⟩
      | none => stuck
  | r => blockKP np nr stk r

/-- The callee at `fa` has the parameter and result counts of the annotated type `y`. -/
def calleeTyped (s : Store H) (f : Frame) (y : TypeIdx) (fa : Nat) : Prop :=
  ∀ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[fa]? = some fi →
    Validation.DefType.funcType? fi.type = some (ps, rs) →
      typeArity f.module y = some (ps.length, rs.length)

open Classical in
/-- A call event to the function at `fa` (`CallX.callAt`), at the annotated type `y`. -/
noncomputable def callAtT (y : TypeIdx) (fa : Nat) (f : Frame) (stk : List Val) :
    M (CallSig H) H Res :=
  getState >>= fun s => if calleeTyped s.down f y fa then callAt fa f stk else stuck

/-- `call_indirect x y`, exposed at the annotated type (`CallX.indEv`). -/
noncomputable def indEvT (x : TableIdx) (y : TypeIdx) (f : Frame) (stk : List Val) :
    M (CallSig H) H Res :=
  getState >>= fun s =>
    match resolveInd s.down f x y stk with
    | some (some fa, stk₁) => callAtT y fa f stk₁
    | some (none, _) => trap ⟨⟩
    | none => stuck

/-- `call_ref y`, exposed at the annotated type (`CallX.refEv`). -/
noncomputable def refEvT (y : TypeIdx) (f : Frame) : List Val → M (CallSig H) H Res
  | .ref (.func fa) :: stk₁ => callAtT y fa f stk₁
  | .ref .null :: _ => trap ⟨⟩
  | _ => stuck

/-- The tail call `i` agrees with its annotated type, if any (`EvalOXP.tail`). -/
def tailTyped (i : Instr) (f : Frame) (ps rs : List Validation.CValType) : Prop :=
  ∀ y, tailAnn i = some y → typeArity f.module y = some (ps.length, rs.length)

open Classical in
/-- **A tail call, pending.** The callee is resolved (`resolveTail`) and typed, and the body
ends in the pending tail call, its arguments bottom first and its result arity: no call event
is made here. A tail call that does not resolve traps. -/
noncomputable def tailPendEv (i : Instr) (f : Frame) (stk : List Val) : M (CallSig H) H ResP :=
  getState >>= fun s =>
    match resolveTail s.down f i stk with
    | some (some (fa, stk₁)) =>
      match s.down.funcs[fa]? with
      | some fi =>
        match Validation.DefType.funcType? fi.type with
        | some (ps, rs) =>
          if tailTyped i f ps rs then pure ⟨(f, .tail fa (stk₁.take ps.length).reverse rs.length)⟩
          else stuck
        | none => stuck
      | none => stuck
    | some none => trap ⟨⟩
    | none => stuck

/-- An operator, exposed with pending tail calls: a tail call is pending (`tailPendEv`), the
indirect and reference calls are typed (`indEvT`, `refEvT`), every other operator is
`ExposeE.opCXE`'s. -/
noncomputable def opCXP (i : Instr) (f : Frame) (stk : List Val) : M (CallSig H) H ResP :=
  match i with
  | .returnCall _ | .returnCallIndirect _ _ | .returnCallRef _ => tailPendEv i f stk
  | .callIndirect x y => liftP (indEvT x y f stk)
  | .callRef y => liftP (refEvT y f stk)
  | _ => liftP (opCXE i f stk)

mutual

/-- The exposed abstract body of a folded tree, with pending tail calls. -/
noncomputable def denXP : BExpr → Frame → List Val → M (CallSig H) H ResP
  | .op i args, f, stk => denListXP args f stk >>= thenKP (opCXP i)
  | .block bt body, f, stk =>
    match arity f bt with
    | some (np, nr) => denListXP body f (stk.take np) >>= blockKP np nr stk
    | none => stuck
  | .loop bt body, f, stk =>
    Silmaril.Elgot.iter (fun c : ULift.{1} (Frame × List Val) =>
      match arity c.down.1 bt with
      | some (np, nr) => denListXP body c.down.1 (c.down.2.take np) >>= loopKP np nr c.down.2
      | none => stuck) ⟨(f, stk)⟩
  | .if_ bt c t el, f, stk =>
    denListXP c f stk >>= fun r =>
      match r with
      | ⟨(f₁, .flow (.normal (cv :: stk₁)))⟩ =>
        match truthy cv, arity f₁ bt with
        | some b, some (np, nr) =>
          (if b then denListXP t f₁ (stk₁.take np) else denListXP el f₁ (stk₁.take np)) >>=
            blockKP np nr stk₁
        | _, _ => stuck
      | ⟨(_, .flow (.normal []))⟩ => stuck
      | r => pure r
  | .tryTable bt cs body, f, stk =>
    match arity f bt with
    | some (np, nr) => denListXP body f (stk.take np) >>= tryKP np nr stk cs
    | none => stuck

/-- The exposed abstract body of a list of trees, with pending tail calls. -/
noncomputable def denListXP : List BExpr → Frame → List Val → M (CallSig H) H ResP
  | [], f, stk => pure ⟨(f, .flow (.normal stk))⟩
  | e :: es, f, stk => denXP e f stk >>= thenKP (denListXP es)

end

/-- The body of one loop iteration, exposed, with pending tail calls. -/
noncomputable def loopBodyXP (bt : BlockType) (body : List BExpr) :
    ULift.{1} (Frame × List Val) → M (CallSig H) H (ResP ⊕ ULift.{1} (Frame × List Val)) :=
  fun c =>
    match arity c.down.1 bt with
    | some (np, nr) => denListXP body c.down.1 (c.down.2.take np) >>= loopKP np nr c.down.2
    | none => stuck

/-! ## The frame -/

/-- The answer `(s₂, fl)` of a pending tail call of result arity `n`, ending the frame as
`FrameP.tail`: the callee's `n` result values returned, or its trap or exception
(`CallX.tailFlow`); any other answer has no rule (`stuck`). -/
noncomputable def frameAns (n : Nat) : Store H × Flow → M (CallSig H) H (ULift.{1} Flow)
  | (_, .trap) => trap ⟨⟩
  | (s₂, .throw t) => setState ⟨s₂⟩ >>= fun _ => pure ⟨.throw t⟩
  | (s₂, fl) =>
    match fl.retVals with
    | some vs => setState ⟨s₂⟩ >>= fun _ => pure ⟨.ret (vs.take n)⟩
    | none => stuck

/-- **Leaving the frame** (`FrameP`): a flow ends the frame as it is; a pending tail call is made
here, and only here, as a call event in the current store, and the frame ends as the callee
does (`frameAns`). -/
noncomputable def frameK : ResP → M (CallSig H) H (ULift.{1} Flow)
  | ⟨(_, .flow fl)⟩ => pure ⟨fl⟩
  | ⟨(_, .tail fa args n)⟩ =>
    getState >>= fun s =>
      callImport (E := CallSig H) (fa, args, s.down) >>= fun ans => frameAns n ans.down

/-- **The exposed frame** of the function at address `a` on bottom-first arguments `args`
(`CallXP.bodyCallXP`): its body run with pending tail calls in the callee frame, then the frame
left (`frameK`). A frame result is the final store and flow. -/
noncomputable def frameXP (a : Nat) (args : List Val) : M (CallSig H) H (ULift.{1} Flow) :=
  getState >>= fun s =>
    match s.down.funcs[a]? with
    | some fi =>
      match fi.code, Validation.DefType.funcType? fi.type with
      | .wasm fn, some _ =>
        denListXP (liftInstrs fn.body) (Frame.forCall fi.module args fn.locals) [] >>= frameK
      | _, _ => stuck
    | none => stuck

/-- The path end of an `EvalOXP` outcome: a trap is the trap effect. -/
def endRP : Store H × Frame × POut →
    Silmaril.Wasm.Abstract.BodyTrace.PathEnd (Except PUnit.{2} (ResP × St H))
  | (_, _, .flow .trap) => .val (.error ⟨⟩)
  | (s', f', o) => .val (.ok (⟨(f', o)⟩, ⟨s'⟩))

/-- The path end of a frame outcome: a trap is the trap effect. -/
def endF : Store H × Flow →
    Silmaril.Wasm.Abstract.BodyTrace.PathEnd (Except PUnit.{2} (ULift.{1} Flow × St H))
  | (_, .trap) => .val (.error ⟨⟩)
  | (s', fl) => .val (.ok (⟨fl⟩, ⟨s'⟩))

end Silmaril.Wasm.Abstract.ExposeP
