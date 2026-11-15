module

public import Silmaril.Wasm.Abstract.StoreBody.Defs
public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Wasm.Abstract.Closing.Defs

/-!
# Store bodies with internal calls as events (F4, exposure)

The store-body denotation of `Silmaril.Wasm.Abstract.StoreBody` with a `call`
handler `cK` (`denC cK`): every construct is denoted as in `StoreBody.den`,
and `call x` on the evaluated operands is `cK x`. Instantiated with
`callEv`, an internal call is a **visible event** of the body: the event
`(a, args, s)` (callee address, bottom-first arguments, current store) of the
signature `CallSig H`, answered by the store and body flow `(s', fl)` the call
ends in. This is exactly the oracle interface of
`Silmaril.Wasm.Abstract.Recursion.EvalO` (`CallRel H`), not a second call
semantics: the answer is read as `EvalO`'s call rules read their oracle
(`callOk`: the values `fl.retVals`; `callTrap`: the trap; `callThrow`: the
exception), and a call to a function the frame does not resolve, or of
unknown type, is `stuck`, as in `EvalO` (no rule).

`Answered C cs`: every call event of the trace `cs` is answered as the oracle
`C` allows. `endR r`: the path end of an `EvalO` outcome (a trap is the trap
effect).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.StoreCall

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody

variable {E : Sig.{0}} {H : Type}

/-- The callee of a direct call. -/
def callIdx? : Instr → Option FuncIdx
  | .call x => some x
  | _ => none

/-- An operator on its evaluated operands: a call through `cK`, otherwise the
lifted primitive. -/
noncomputable def opC (cK : FuncIdx → Frame → List Val → M E H Res) (i : Instr) :
    Frame → List Val → M E H Res := fun f stk =>
  match callIdx? i with
  | some x => cK x f stk
  | none => flatK i f stk

mutual

/-- The abstract body of a folded tree, internal calls through `cK`. -/
noncomputable def denC (cK : FuncIdx → Frame → List Val → M E H Res) :
    BExpr → Frame → List Val → M E H Res
  | .op i args, f, stk => denListC cK args f stk >>= thenK (opC cK i)
  | .block bt body, f, stk =>
    match arity f bt with
    | some (np, nr) => denListC cK body f (stk.take np) >>= blockK np nr stk
    | none => stuck
  | .loop bt body, f, stk =>
    Silmaril.Elgot.iter (fun c : ULift.{1} (Frame × List Val) =>
      match arity c.down.1 bt with
      | some (np, nr) => denListC cK body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
      | none => stuck) ⟨(f, stk)⟩
  | .if_ bt c t el, f, stk =>
    denListC cK c f stk >>= fun r =>
      match r with
      | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
        match truthy cv, arity f₁ bt with
        | some b, some (np, nr) =>
          (if b then denListC cK t f₁ (stk₁.take np) else denListC cK el f₁ (stk₁.take np)) >>=
            blockK np nr stk₁
        | _, _ => stuck
      | ⟨(_, .normal [])⟩ => stuck
      | r => pure r
  | .tryTable .., _, _ => stuck

/-- The abstract body of a list of trees, internal calls through `cK`. -/
noncomputable def denListC (cK : FuncIdx → Frame → List Val → M E H Res) :
    List BExpr → Frame → List Val → M E H Res
  | [], f, stk => pure ⟨(f, .normal stk)⟩
  | e :: es, f, stk => denC cK e f stk >>= thenK (denListC cK es)

end

/-- The body of one loop iteration, internal calls through `cK`. -/
noncomputable def loopBodyC (cK : FuncIdx → Frame → List Val → M E H Res) (bt : BlockType)
    (body : List BExpr) :
    ULift.{1} (Frame × List Val) → M E H (Res ⊕ ULift.{1} (Frame × List Val)) :=
  fun c =>
    match arity c.down.1 bt with
    | some (np, nr) => denListC cK body c.down.1 (c.down.2.take np) >>= loopK np nr c.down.2
    | none => stuck

/-- Internal calls as events: a call of the function at address `a` on
bottom-first arguments `args` in store `s`, answered by the final store and
body flow. -/
def CallSig (H : Type) : Sig.{0} := ⟨Nat × List Val × Store H, fun _ => Store H × Flow⟩

/-- The answer `(s', fl)` of a call event, read as `EvalO`'s call rules read
their oracle: a trap, an exception, or the returned values over the passive stack. -/
noncomputable def callAns (f : Frame) (stk : List Val) (ps rs : List Validation.CValType) :
    Store H × Flow → M (CallSig H) H Res
  | (_, .trap) => trap ⟨⟩
  | (s₂, .throw t) => setState ⟨s₂⟩ >>= fun _ => pure ⟨(f, .throw t)⟩
  | (s₂, fl) =>
    match fl.retVals with
    | some vs =>
      setState ⟨s₂⟩ >>= fun _ => pure ⟨(f, .normal (vs.take rs.length ++ stk.drop ps.length))⟩
    | none => stuck

/-- **A call, exposed.** Resolve the callee in the frame, issue the call event,
and read the answer (`callAns`). -/
noncomputable def callEv (x : FuncIdx) (f : Frame) (stk : List Val) : M (CallSig H) H Res :=
  getState >>= fun s =>
    match s.down.func? f x with
    | some (a, fi) =>
      match Validation.DefType.funcType? fi.type with
      | some (ps, rs) =>
        callImport (E := CallSig H) (a, (stk.take ps.length).reverse, s.down) >>= fun ans =>
          callAns f stk ps rs ans.down
      | none => stuck
    | none => stuck

/-- The exposed abstract body of a list of trees. -/
noncomputable abbrev denListE : List BExpr → Frame → List Val → M (CallSig H) H Res :=
  denListC callEv

/-- Every call event of the trace is answered as the oracle `C` allows. -/
def Answered (C : CallRel H) (cs : List (Silmaril.Games.Abstract.Call (CallSig H))) : Prop :=
  ∀ c ∈ cs, C c.1.2.2 c.1.1 c.1.2.1 c.2

/-- The path end of an `EvalO` outcome: a trap is the trap effect. -/
def endR : Store H × Frame × Flow →
    Silmaril.Wasm.Abstract.BodyTrace.PathEnd (Except PUnit.{2} (Res × St H))
  | (_, _, .trap) => .val (.error ⟨⟩)
  | (s', f', fl) => .val (.ok (⟨(f', fl)⟩, ⟨s'⟩))

/-! ## Descents through call events -/

/-- The call event of a call of the open module (callee, arguments, store). -/
def callOp (y : (wasmOShape H).self.Op) : (CallSig H).Op := (y.1, y.2.1, y.2.2)

/-- **An exposed descent**: the exposed body of the call `x` makes the pending
call event of `y` after call events answered by `closedCall`. -/
def ExposedReach (x y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), x.2.2.funcs[x.1]? = some fi ∧ fi.code = .wasm fn ∧
    ∃ cs, Answered closedCall cs ∧
      Silmaril.Wasm.Abstract.BodyTrace.Pend
        (((denListE (liftInstrs fn.body) (Frame.forCall fi.module x.2.1 fn.locals) [] :
          M (CallSig H) H Res).run ⟨x.2.2⟩).run) cs (callOp y)

/-- Finite chains of exposed descents. -/
inductive ExposedPath : (wasmOShape H).self.Op → (wasmOShape H).self.Op → Prop
  | refl (x : (wasmOShape H).self.Op) : ExposedPath x x
  | step {x y z : (wasmOShape H).self.Op} : ExposedReach x y → ExposedPath y z → ExposedPath x z

/-- Every call event of the stream is answered as `C` allows. -/
def AnsweredS (C : CallRel H) (ω : Nat → Silmaril.Games.Abstract.Call (CallSig H)) : Prop :=
  ∀ n, C (ω n).1.2.2 (ω n).1.1 (ω n).1.2.1 (ω n).2

/-- The exposed body of the call `z` (its function's code, callee frame). -/
noncomputable def exposedTree (z : (wasmOShape H).self.Op) (fn : Func) (fi : FuncInst H) :
    Silmaril.Elgot.ITree.Tree (Silmaril.Wasm.Abstract.Body.SigEv (CallSig H))
      (Except PUnit.{2} (Res × St H)) :=
  ((denListE (liftInstrs fn.body) (Frame.forCall fi.module z.2.1 fn.locals) [] :
    M (CallSig H) H Res).run ⟨z.2.2⟩).run

/-- **Productive local divergence, exposed**: the exposed body of `z` has an
infinite run whose call events are all answered by `closedCall` (infinitely many
returning internal calls). -/
def ExposedInf (z : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
    ∃ ω, AnsweredS closedCall ω ∧ Silmaril.Wasm.Abstract.BodyTrace.InfPath (exposedTree z fn fi) ω

/-- **Silent divergence, exposed**: after `closedCall`-answered call events, the
exposed body of `z` diverges silently. -/
def ExposedSilent (z : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
    ∃ cs, Answered closedCall cs ∧ Silmaril.Wasm.Abstract.BodyTrace.Path (exposedTree z fn fi) cs .div

end Silmaril.Wasm.Abstract.StoreCall
