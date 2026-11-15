module

public import Silmaril.Wasm.Abstract.ExposePStruct.Thms
public import Mathlib.CategoryTheory.SingleObj

/-!
# Operational observations of the canonical F5 semantics, and the denotation functor (F7)

`ExposeP.denListXP` is the exact `BodyM` denotation of `CallXP.EvalOXP`; `ExposePStruct` reads it
as a structure-preserving map `denL` from code into morphisms `PHom`. This topic states what the
denotation observes **operationally**, and proves (`Silmaril.Wasm.Abstract.FunctorP.Thms`) that the
denotation is faithful for exactly that observation.

**Logged runs.** An oracle `C : CallRel H` answers call events relationally. A run of code against
`C` is recorded with its **log**: the list of answered call events (`ACall H`: the event, callee
address, arguments bottom first and store, with the answer, store and flow) in the order they are
made. The relations below are the operational semantics of `EvalOXP` with that log made explicit,
stated compositionally (one rule per construct, the continuation by `cons`):

* `EvalLXP C s f stk es cs r`: from the store `s`, frame `f` and top-first stack `stk`, the code
  `es` makes exactly the answered call events `cs`, each answered as `C` allows, and ends in `r`
  (a flow, exceptions and traps included, or a pending tail call). An operator that makes no call
  event (`callEvInstr`: everything but `call`, `call_indirect` and `call_ref`; tail calls are
  pending results, `throw` and `throw_ref` are values) runs by `EvalOXP` itself (`HeadL.quiet`);
  a call makes one event and reads its answer as `StoreCall.callAns` does (`ansOut`).
* `ReachXP C s f stk es cs y`: the run makes the answered events `cs` and then the call event `y`
  (callee, arguments, store), not yet answered: the **pending observation**, which sees an infinite
  productive run through its finite prefixes.
* The frame: `FrameLXP C s a args cs out` (the callee body, then a pending tail call made as a call
  event at the frame, `frameOut` as `ExposeP.frameAns`), `FrameReachXP` (a pending call of the body,
  or the pending tail call's event at the frame).

**Why logs.** Without its log a pending or finished observation does not determine the path it
was made on: an oracle is a relation, not a history, so the same call event answered the same way
at two positions of a run is indistinguishable to it. For trees in general the unlogged
observations over all oracles are not faithful (`vis c (fun _ => ret v)` and
`vis c (fun _ => vis c (fun _ => ret v))` have, for every oracle, the same reachable call events
and the same outcomes); the logged ones are.

**Equivalences.** `OpEquivP H es es'`: for every oracle, store, frame, stack and log, the same
non-trap logged outcomes (store, frame and result), the same logged traps (a trap's store and
frame are not observed: the denotation's trap effect forgets them), and the same logged pending
calls. `OpCollapseEquivP H es es'`: the same with a trap identified with divergence, that is, only
the non-trap logged outcomes and the logged pending calls are compared (at a reachable log, "traps
or diverges" is "no non-trap outcome and no pending call").
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.FunctorP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreCall (CallSig)
open Silmaril.Wasm.Abstract.CallX (IndResS)
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.CallXT (typeArity)

variable {H : Type}

/-- An answered call event: the event (callee address, arguments bottom first, store) and the
answer (store, flow). -/
abbrev ACall (H : Type) : Type := Silmaril.Games.Abstract.Call (CallSig H)

/-- The operators that make a call event where they are made: `call`, `call_indirect`,
`call_ref`. (A tail call is a pending result, made at the frame.) -/
def callEvInstr : Instr → Bool
  | .call _ | .callIndirect _ _ | .callRef _ => true
  | _ => false

/-- The exits of a block, an `if` arm, a loop body that does not branch back, or a `try_table`
body that does not throw (`ExposeP.blockKP`): a fallthrough or `br 0` keeps the block's results
over the passive stack, an outer branch is one label further out, every other result passes. -/
def blockOutP (np nr : Nat) (stk : List Val) : POut → POut
  | .flow (.normal vs) => .flow (.normal (vs.take nr ++ stk.drop np))
  | .flow (.brk 0 vs) => .flow (.normal (vs.take nr ++ stk.drop np))
  | .flow (.brk (k + 1) vs) => .flow (.brk k vs)
  | o => o

/-- The result of a call's answer `(s₂, fl)` at the frame `f` over the stack `stk`
(`StoreCall.callAns`): a trap, an exception raised at the call, or the callee's returned values
over the passive stack; any other answer has no rule. -/
def ansOut (f : Frame) (stk : List Val) (ps rs : List Validation.CValType) :
    Store H × Flow → Option (Store H × Frame × POut)
  | (s₂, .trap) => some (s₂, f, .flow .trap)
  | (s₂, .throw t) => some (s₂, f, .flow (.throw t))
  | (s₂, fl) =>
    fl.retVals.map fun vs => (s₂, f, .flow (.normal (vs.take rs.length ++ stk.drop ps.length)))

/-- The exits of a `try_table` body ending in `o` (`ExposeP.tryKP`): what is not a thrown
exception is a block's exit; a thrown exception is resolved by the clauses `cls` in the store `s`
and frame `f` (`Cfg.Region.Catches`): a branch with the clause's values, or a rethrow. -/
def TryOut (s : Store H) (f : Frame) (np nr : Nat) (stk : List Val) (cls : List Catch)
    (o o' : POut) : Prop :=
  (o.NotThrow ∧ o' = blockOutP np nr stk o) ∨
    ∃ a, o = .flow (.throw a) ∧
      ((∃ us l, Cfg.Region.Catches s f a cls (some (us, l)) ∧
          o' = .flow (.brk l.toNat (us.reverse ++ stk.drop np))) ∨
        (Cfg.Region.Catches s f a cls none ∧ o' = .flow (.throw a)))

/-- **An operator on the stack its operands left**, with the answered call events it makes. -/
inductive HeadL (C : CallRel H) (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) :
    Instr → List (ACall H) → Store H × Frame × POut → Prop
  /-- An operator that makes no call event runs as in `EvalOXP` (the oracle is not consulted). -/
  | quiet {i : Instr} {r : Store H × Frame × POut} (hi : callEvInstr i = false)
      (h : EvalOXP C s₁ f₁ stk₁ [.op i []] r) : HeadL C s₁ f₁ stk₁ i [] r
  /-- `call x`: one call event, answered by `C`. -/
  | call {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {ans : Store H × Flow} {r : Store H × Frame × POut}
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ a (stk₁.take ps.length).reverse ans) (hr : ansOut f₁ stk₁ ps rs ans = some r) :
      HeadL C s₁ f₁ stk₁ (.call x) [⟨(a, (stk₁.take ps.length).reverse, s₁), ans⟩] r
  /-- A resolved `call_indirect x y` to a callee of the annotated type: one call event. -/
  | ind {x : TableIdx} {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {ans : Store H × Flow} {r : Store H × Frame × POut}
      (hres : IndResS s₁ f₁ x y stk₁ (some fa, stk')) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hC : C s₁ fa (stk'.take ps.length).reverse ans) (hr : ansOut f₁ stk' ps rs ans = some r) :
      HeadL C s₁ f₁ stk₁ (.callIndirect x y) [⟨(fa, (stk'.take ps.length).reverse, s₁), ans⟩] r
  /-- An unresolved `call_indirect` traps, making no call event. -/
  | indNone {x : TableIdx} {y : TypeIdx} {stk' : List Val}
      (hres : IndResS s₁ f₁ x y stk₁ (none, stk')) :
      HeadL C s₁ f₁ stk₁ (.callIndirect x y) [] (s₁, f₁, .flow .trap)
  /-- `call_ref y` on a function reference of the annotated type: one call event. -/
  | ref {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {ans : Store H × Flow} {r : Store H × Frame × POut}
      (hstk : stk₁ = .ref (.func fa) :: stk') (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hC : C s₁ fa (stk'.take ps.length).reverse ans) (hr : ansOut f₁ stk' ps rs ans = some r) :
      HeadL C s₁ f₁ stk₁ (.callRef y) [⟨(fa, (stk'.take ps.length).reverse, s₁), ans⟩] r
  /-- `call_ref` on null traps, making no call event. -/
  | refNull {y : TypeIdx} {stk' : List Val} (hstk : stk₁ = .ref .null :: stk') :
      HeadL C s₁ f₁ stk₁ (.callRef y) [] (s₁, f₁, .flow .trap)

/-- **Logged runs**: `EvalLXP C s f stk es cs r` — the code `es` makes exactly the answered call
events `cs` (each answered as `C` allows) and ends in `r`. One rule per construct on a one-tree
sequence; `cons`/`stop` sequence a tree with the rest. -/
inductive EvalLXP (C : CallRel H) :
    Store H → Frame → List Val → List BExpr → List (ACall H) → Store H × Frame × POut → Prop
  | nil {s : Store H} {f : Frame} {stk : List Val} : EvalLXP C s f stk [] [] (s, f, .flow (.normal stk))
  /-- A tree falls through; the rest runs on. -/
  | cons {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {e : BExpr} {es : List BExpr}
      {cs₁ cs₂ : List (ACall H)} {r : Store H × Frame × POut}
      (h₁ : EvalLXP C s f stk [e] cs₁ (s₁, f₁, .flow (.normal stk₁)))
      (h₂ : EvalLXP C s₁ f₁ stk₁ es cs₂ r) : EvalLXP C s f stk (e :: es) (cs₁ ++ cs₂) r
  /-- A tree does not fall through; the rest is skipped. -/
  | stop {s : Store H} {f : Frame} {stk : List Val} {e : BExpr} {es : List BExpr}
      {cs : List (ACall H)} {r : Store H × Frame × POut} (h : EvalLXP C s f stk [e] cs r)
      (hn : ¬ r.2.2.IsNormal) : EvalLXP C s f stk (e :: es) cs r
  /-- The operands of an operator do not fall through. -/
  | argsStop {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args : List BExpr}
      {cs : List (ACall H)} {o : POut} (h : EvalLXP C s f stk args cs (s₁, f₁, o))
      (ho : ¬ o.IsNormal) : EvalLXP C s f stk [.op i args] cs (s₁, f₁, o)
  /-- The operands, then the operator. -/
  | head {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr} {args : List BExpr}
      {cs₁ cs₂ : List (ACall H)} {r : Store H × Frame × POut}
      (h : EvalLXP C s f stk args cs₁ (s₁, f₁, .flow (.normal stk₁)))
      (hh : HeadL C s₁ f₁ stk₁ i cs₂ r) : EvalLXP C s f stk [.op i args] (cs₁ ++ cs₂) r
  /-- A block: its body on the parameters, then its exits. -/
  | block {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType} {body : List BExpr}
      {np nr : Nat} {cs : List (ACall H)} {o : POut} (har : arity f bt = some (np, nr))
      (h : EvalLXP C s f (stk.take np) body cs (s₁, f₁, o)) :
      EvalLXP C s f stk [.block bt body] cs (s₁, f₁, blockOutP np nr stk o)
  /-- A loop body branching back with `br 0`: the loop runs again. -/
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body : List BExpr} {np nr : Nat} {cs₁ cs₂ : List (ACall H)} {r : Store H × Frame × POut}
      (har : arity f bt = some (np, nr))
      (h : EvalLXP C s f (stk.take np) body cs₁ (s₁, f₁, .flow (.brk 0 vs)))
      (hk : EvalLXP C s₁ f₁ (vs.take np ++ stk.drop np) [.loop bt body] cs₂ r) :
      EvalLXP C s f stk [.loop bt body] (cs₁ ++ cs₂) r
  /-- A loop body ending otherwise: the loop's exits. -/
  | loopExit {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body : List BExpr} {np nr : Nat} {cs : List (ACall H)} {o : POut}
      (har : arity f bt = some (np, nr)) (h : EvalLXP C s f (stk.take np) body cs (s₁, f₁, o))
      (hb : ∀ vs, o ≠ .flow (.brk 0 vs)) :
      EvalLXP C s f stk [.loop bt body] cs (s₁, f₁, blockOutP np nr stk o)
  /-- The condition of an `if` does not fall through. -/
  | ifStop {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el : List BExpr} {cs : List (ACall H)} {o : POut}
      (h : EvalLXP C s f stk c cs (s₁, f₁, o)) (ho : ¬ o.IsNormal) :
      EvalLXP C s f stk [.if_ bt c t el] cs (s₁, f₁, o)
  /-- The condition, then the arm it selects on the parameters, then its exits. -/
  | ifArm {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el : List BExpr} {np nr : Nat} {cs₁ cs₂ : List (ACall H)}
      {o : POut} (h : EvalLXP C s f stk c cs₁ (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXP C s₁ f₁ (stk₁.take np) (if b then t else el) cs₂ (s₂, f₂, o)) :
      EvalLXP C s f stk [.if_ bt c t el] (cs₁ ++ cs₂) (s₂, f₂, blockOutP np nr stk₁ o)
  /-- A `try_table`: its body on the parameters, then the handler's exits (`TryOut`). -/
  | tryT {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType} {cls : List Catch}
      {body : List BExpr} {np nr : Nat} {cs : List (ACall H)} {o o' : POut}
      (har : arity f bt = some (np, nr)) (h : EvalLXP C s f (stk.take np) body cs (s₁, f₁, o))
      (ht : TryOut s₁ f₁ np nr stk cls o o') :
      EvalLXP C s f stk [.tryTable bt cls body] cs (s₁, f₁, o')

/-- The call event an operator makes on the stack its operands left (callee address, arguments
bottom first, store), before its answer. -/
inductive HeadEv (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) :
    Instr → Nat × List Val × Store H → Prop
  | call {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      HeadEv s₁ f₁ stk₁ (.call x) (a, (stk₁.take ps.length).reverse, s₁)
  | ind {x : TableIdx} {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} (hres : IndResS s₁ f₁ x y stk₁ (some fa, stk'))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      HeadEv s₁ f₁ stk₁ (.callIndirect x y) (fa, (stk'.take ps.length).reverse, s₁)
  | ref {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} (hstk : stk₁ = .ref (.func fa) :: stk')
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      HeadEv s₁ f₁ stk₁ (.callRef y) (fa, (stk'.take ps.length).reverse, s₁)

/-- **Pending observations**: `ReachXP C s f stk es cs y` — the run of `es` makes the answered
call events `cs` (each answered as `C` allows) and then the call event `y`, not yet answered. -/
inductive ReachXP (C : CallRel H) :
    Store H → Frame → List Val → List BExpr → List (ACall H) → Nat × List Val × Store H → Prop
  /-- In the first tree. -/
  | head {s : Store H} {f : Frame} {stk : List Val} {e : BExpr} {es : List BExpr}
      {cs : List (ACall H)} {y : Nat × List Val × Store H} (h : ReachXP C s f stk [e] cs y) :
      ReachXP C s f stk (e :: es) cs y
  /-- After the first tree fell through. -/
  | cons {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {e : BExpr} {es : List BExpr}
      {cs₁ cs₂ : List (ACall H)} {y : Nat × List Val × Store H}
      (h₁ : EvalLXP C s f stk [e] cs₁ (s₁, f₁, .flow (.normal stk₁)))
      (h₂ : ReachXP C s₁ f₁ stk₁ es cs₂ y) : ReachXP C s f stk (e :: es) (cs₁ ++ cs₂) y
  /-- In the operands. -/
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args : List BExpr}
      {cs : List (ACall H)} {y : Nat × List Val × Store H} (h : ReachXP C s f stk args cs y) :
      ReachXP C s f stk [.op i args] cs y
  /-- The operator's own call event. -/
  | call {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr} {args : List BExpr}
      {cs : List (ACall H)} {y : Nat × List Val × Store H}
      (h : EvalLXP C s f stk args cs (s₁, f₁, .flow (.normal stk₁)))
      (hy : HeadEv s₁ f₁ stk₁ i y) : ReachXP C s f stk [.op i args] cs y
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body : List BExpr}
      {np nr : Nat} {cs : List (ACall H)} {y : Nat × List Val × Store H}
      (har : arity f bt = some (np, nr)) (h : ReachXP C s f (stk.take np) body cs y) :
      ReachXP C s f stk [.block bt body] cs y
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body : List BExpr}
      {np nr : Nat} {cs : List (ACall H)} {y : Nat × List Val × Store H}
      (har : arity f bt = some (np, nr)) (h : ReachXP C s f (stk.take np) body cs y) :
      ReachXP C s f stk [.loop bt body] cs y
  /-- In a later iteration of a loop. -/
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body : List BExpr} {np nr : Nat} {cs₁ cs₂ : List (ACall H)} {y : Nat × List Val × Store H}
      (har : arity f bt = some (np, nr))
      (h : EvalLXP C s f (stk.take np) body cs₁ (s₁, f₁, .flow (.brk 0 vs)))
      (hk : ReachXP C s₁ f₁ (vs.take np ++ stk.drop np) [.loop bt body] cs₂ y) :
      ReachXP C s f stk [.loop bt body] (cs₁ ++ cs₂) y
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el : List BExpr}
      {cs : List (ACall H)} {y : Nat × List Val × Store H} (h : ReachXP C s f stk c cs y) :
      ReachXP C s f stk [.if_ bt c t el] cs y
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el : List BExpr} {np nr : Nat} {cs₁ cs₂ : List (ACall H)}
      {y : Nat × List Val × Store H}
      (h : EvalLXP C s f stk c cs₁ (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : arity f₁ bt = some (np, nr))
      (harm : ReachXP C s₁ f₁ (stk₁.take np) (if b then t else el) cs₂ y) :
      ReachXP C s f stk [.if_ bt c t el] (cs₁ ++ cs₂) y
  | tryT {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cls : List Catch}
      {body : List BExpr} {np nr : Nat} {cs : List (ACall H)} {y : Nat × List Val × Store H}
      (har : arity f bt = some (np, nr)) (h : ReachXP C s f (stk.take np) body cs y) :
      ReachXP C s f stk [.tryTable bt cls body] cs y

/-! ## The frame -/

/-- The answer `(s₂, fl)` of a pending tail call of result arity `n`, ending the frame
(`ExposeP.frameAns`, `CallXP.FrameP.tail`): a trap, an exception, or the callee's `n` result
values returned; any other answer has no rule. -/
def frameOut (n : Nat) : Store H × Flow → Option (Store H × Flow)
  | (s₂, .trap) => some (s₂, .trap)
  | (s₂, .throw t) => some (s₂, .throw t)
  | (s₂, fl) => fl.retVals.map fun vs => (s₂, .ret (vs.take n))

/-- Leaving the frame from the store `s₁` with the body result `o`, logged: a flow ends the frame
as it is; a pending tail call makes its call event here, answered by `C`. -/
inductive FrameKL (C : CallRel H) (s₁ : Store H) : POut → List (ACall H) → Store H × Flow → Prop
  | flow {fl : Flow} : FrameKL C s₁ (.flow fl) [] (s₁, fl)
  | tail {fa n : Nat} {args : List Val} {ans : Store H × Flow} {out : Store H × Flow}
      (hC : C s₁ fa args ans) (hr : frameOut n ans = some out) :
      FrameKL C s₁ (.tail fa args n) [⟨(fa, args, s₁), ans⟩] out

/-- **A logged frame** of the function at `a` on bottom-first arguments `args`
(`CallXP.bodyCallXP`, `ExposeP.frameXP`): its body logged in the callee frame, then the frame left,
a pending tail call's event made at the frame. -/
def FrameLXP (C : CallRel H) (s : Store H) (a : Nat) (args : List Val) (cs : List (ACall H))
    (out : Store H × Flow) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s₁ : Store H) (f₂ : Frame)
    (o : POut) (cs₁ cs₂ : List (ACall H)),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    EvalLXP C s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) cs₁ (s₁, f₂, o) ∧
    FrameKL C s₁ o cs₂ out ∧ cs = cs₁ ++ cs₂

/-- **Pending observations of a frame**: a pending call of the callee body, or, the body having
ended in a pending tail call, that call's event, made at the frame. -/
def FrameReachXP (C : CallRel H) (s : Store H) (a : Nat) (args : List Val) (cs : List (ACall H))
    (y : Nat × List Val × Store H) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType),
    s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    (ReachXP C s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) cs y ∨
      ∃ (s₁ : Store H) (f₂ : Frame) (fa n : Nat) (args' : List Val),
        EvalLXP C s (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) cs
          (s₁, f₂, .tail fa args' n) ∧ y = (fa, args', s₁))

/-! ## Operational equivalences -/

/-- **Exact operational equivalence** of two code lists, at every oracle, store, frame, stack and
log: the same non-trap logged outcomes, the same logged traps (a trap's store and frame are not
observed), and the same logged pending calls. -/
def OpEquivP (H : Type) (es es' : List BExpr) : Prop :=
  ∀ (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (cs : List (ACall H)),
    (∀ s' f' o, o ≠ .flow .trap →
      (EvalLXP C s f stk es cs (s', f', o) ↔ EvalLXP C s f stk es' cs (s', f', o))) ∧
    ((∃ s' f', EvalLXP C s f stk es cs (s', f', .flow .trap)) ↔
      ∃ s' f', EvalLXP C s f stk es' cs (s', f', .flow .trap)) ∧
    ∀ y, ReachXP C s f stk es cs y ↔ ReachXP C s f stk es' cs y

/-- **Operational equivalence up to trap ≈ divergence**: the same non-trap logged outcomes and the
same logged pending calls. Traps are not compared: at a reachable log, a run traps or diverges
exactly when it has neither a non-trap outcome nor a pending call there. -/
def OpCollapseEquivP (H : Type) (es es' : List BExpr) : Prop :=
  ∀ (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (cs : List (ACall H)),
    (∀ s' f' o, o ≠ .flow .trap →
      (EvalLXP C s f stk es cs (s', f', o) ↔ EvalLXP C s f stk es' cs (s', f', o))) ∧
    ∀ y, ReachXP C s f stk es cs y ↔ ReachXP C s f stk es' cs y

/-! ## The denotation functor

The checked subcategory of `ExposePStruct` (objects `Iface`, morphisms code `Hom Γ I J es` typed
from `I` falling through at `J` in a store context `Γ`) is a category under concatenation, and
`denL` is a functor from it into the monoid of exposed bodies under exit-aware composition
(`ExposePStruct.seqP`, unit `idP`), read as a one-object category. -/

open Silmaril.Wasm.Abstract.ExposePStruct

/-- The objects of the checked category in the store context `Γ`: interfaces. -/
def CObj (_Γ : ExposePStruct.Ctx H) : Type := ExposePStruct.Iface

/-- **The checked category**: morphisms are checked code (`ExposePStruct.Hom`), the identity
the empty sequence, composition concatenation (`hom_id`, `hom_comp`). -/
instance (Γ : ExposePStruct.Ctx H) : CategoryTheory.Category (CObj Γ) where
  Hom I J := {es : List BExpr // ExposePStruct.Hom Γ I J es}
  id I := ⟨[], hom_id I⟩
  comp m₁ m₂ := ⟨m₁.1 ++ m₂.1, hom_comp m₁.2 m₂.2⟩
  id_comp _ := Subtype.ext (List.nil_append _)
  comp_id _ := Subtype.ext (List.append_nil _)
  assoc _ _ _ := Subtype.ext (List.append_assoc _ _ _)

/-- Exposed bodies on configurations, as a monoid under exit-aware composition: `g * g'` runs
`g'` then `g` (so that composition in the one-object category `SingleObj` is `seqP`). -/
def PMon (H : Type) : Type 1 := PHom H Cfg ExposeP.ResP

noncomputable instance : Monoid (PMon H) where
  mul g g' := (seqP (H := H) g' g : PHom H Cfg ExposeP.ResP)
  one := (idP : PHom H Cfg ExposeP.ResP)
  mul_assoc _ _ _ := (seqP_assoc _ _ _).symm
  one_mul := seqP_id_right
  mul_one := seqP_id_left

/-- **The denotation functor**: checked code `es : I ⟶ J` is sent to its exposed body `denL es`
(`denL_nil`, `denL_append`). -/
noncomputable def denFunctor (Γ : ExposePStruct.Ctx H) :
    CategoryTheory.Functor (CObj Γ) (CategoryTheory.SingleObj (PMon H)) where
  obj _ := CategoryTheory.SingleObj.star _
  map m := (denL m.1 : PHom H Cfg ExposeP.ResP)
  map_id _ := denL_nil
  map_comp m₁ m₂ := by
    change denL (m₁.1 ++ m₂.1) = seqP (denL m₁.1) (denL m₂.1)
    exact denL_append _ _

end Silmaril.Wasm.Abstract.FunctorP
