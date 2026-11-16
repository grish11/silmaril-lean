module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Abstract.XDivergeP.Defs
public import Silmaril.Games.Abstract.ModuleDLog.Defs
public import Silmaril.Games.Abstract.ModuleInf.Defs
public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# Divergence after a log and productive runs of the canonical closure: definitions

The canonical analogue of `Silmaril.Wasm.Abstract.HostClosingInf`, for the logged canonical
relation `EvalLXPh` (exceptions, every call form, tail calls pending until the frame is left) and
its open module `wasmHOpenXP` (`Silmaril.Wasm.Abstract.HostClosingXP`). `wasmEvFunXP` observes
finished behaviours only; here are its divergent and productive runs.

**A finite host-event log, then host-free divergence**:

* `LogDivXP s f stk es l`: the trees perform the logged open calls `l` (an `EvalLXPh` prefix; the
  constructors are those of `ReachLXP`: at `call`, a resolved `call_indirect` or `call_ref`
  answered by values, inside blocks, loops, conditionals and `try_table` handlers, after a head
  tree run to completion, including one left by a caught exception branching out) and then
  diverge **host-free** (`div`): `XDivergeP.EvalDivXP`, the coinductive divergence of the closed
  canonical semantics `EvalOXP closedCallXP`. The closed call relation answers Wasm functions
  only, so no host call is made after the log. Its loops re-enter after a body ending in a
  branch to the loop, which includes an exception thrown in the body and caught by a `try_table`
  clause branching to the loop's label; traps are never caught (`EvalOXP` passes them through
  every handler, as `EvalLXPh` does);
* `LDLwXP z u`: the body of the Wasm function called by `z` does so, `u` its log as calls of
  `wasmHOpenXP`;
* `wasmEvFunDXP := Shape.closeDLog wasmHOpenXP LDLwXP`: `wasmEvFunXP` with divergence after the
  import calls of descent paths and infinite descent chains with finitely many import calls
  (`Shape.closeD`; a descent includes a frame-level tail call), and after logged host-free
  divergence of a body reached by a descent path.

**Productive runs**:

* `InfLXP s f stk es ω`: the trees run forever within their function, making the open calls `ω`
  (each with its answer). The constructors are those of `LogDivXP` with the finite parts run by
  `EvalLXPh` put in front of the stream, and `loopInf`, a loop iterating forever whose stream is
  the concatenation of its iteration logs, **of unbounded length**: a loop whose iterations make
  no call (or finitely many) claims no stream. Iterations may end in a caught exception branching
  back to the loop. Productive runs inside callees, and after a frame-level tail call, are
  descents of the module (`Shape.closeInfL`);
* `InfLwXP`: the productive open runs of a Wasm body, as calls of `wasmHOpenXP`;
* `wasmEvInfNXP := Shape.closeInfL wasmHOpenXP InfLwXP`.

No host semantics occurs in these definitions. Every call is recorded with its answer; a log is
never shortened, so productive interaction is never read as `div` (`div` requires a finite log
and no further host call).

Theorems in `Silmaril.Wasm.Abstract.HostClosingInfXP.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.CallXT (typeArity)

variable {H : Type}

/-! ## A finite host-event log, then host-free divergence -/

/-- **The trees perform the logged calls `l`, then diverge host-free.** The prefix is an
`EvalLXPh` prefix; the constructors are those of `ReachLXP`, with host-free divergence of the
closed canonical semantics (`XDivergeP.EvalDivXP`) in place of the reached call. -/
inductive LogDivXP : Store H → Frame → List Val → List BExpr → List (OCall H) → Prop where
  /-- Host-free divergence, with an empty log. -/
  | div {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
      XDivergeP.EvalDivXP s f stk es → LogDivXP s f stk es []
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {l : List (OCall H)} :
      LogDivXP s f stk args l → LogDivXP s f stk (.op i args :: es) l
  | callK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      LogDivXP s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ →
      LogDivXP s f stk (.op (.call x) args :: es)
        (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂)
  | indK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ l₂ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁
        (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      LogDivXP s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ →
      LogDivXP s f stk (.op (.callIndirect x y) args :: es)
        (l₁ ++ OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂)
  | refK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ l₂ : List (OCall H)}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      LogDivXP s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ →
      LogDivXP s f stk (.op (.callRef y) args :: es)
        (l₁ ++ OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂)
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (OCall H)}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      LogDivXP s₂ f₂ stk₂ es l₂ → LogDivXP s f stk (.op i args :: es) (l₁ ++ l₂)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (OCall H)} (har : arity f bt = some (np, nr)) :
      LogDivXP s f (stk.take np) body l → LogDivXP s f stk (.block bt body :: es) l
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) :
      LogDivXP s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ →
      LogDivXP s f stk (.block bt body :: es) (l₁ ++ l₂)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (OCall H)} (har : arity f bt = some (np, nr)) :
      LogDivXP s f (stk.take np) body l → LogDivXP s f stk (.loop bt body :: es) l
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow (.normal vs))) :
      LogDivXP s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ →
      LogDivXP s f stk (.loop bt body :: es) (l₁ ++ l₂)
  /-- An iteration branching back (possibly by a caught exception), then the loop again. -/
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow (.brk 0 vs))) :
      LogDivXP s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ →
      LogDivXP s f stk (.loop bt body :: es) (l₁ ++ l₂)
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {l : List (OCall H)} :
      LogDivXP s f stk c l → LogDivXP s f stk (.if_ bt c t el :: es) l
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)}
      (hc : EvalLXPh s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : arity f₁ bt = some (np, nr)) :
      LogDivXP s₁ f₁ (stk₁.take np) (if b then t else el) l₂ →
      LogDivXP s f stk (.if_ bt c t el :: es) (l₁ ++ l₂)
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (OCall H)}
      (hc : EvalLXPh s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPh s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, .flow fl))
      (hvs : fl.blockVals = some vs) :
      LogDivXP s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ →
      LogDivXP s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃)
  /-- Inside a `try_table` handler. -/
  | handler {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {l : List (OCall H)}
      (har : arity f bt = some (np, nr)) :
      LogDivXP s f (stk.take np) body l → LogDivXP s f stk (.tryTable bt cs body :: es) l
  /-- After a `try_table` left normally or by a branch, including a caught exception. -/
  | tryK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) :
      LogDivXP s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ →
      LogDivXP s f stk (.tryTable bt cs body :: es) (l₁ ++ l₂)

/-- **Logged host-free divergence of a call**: the body of the Wasm function called by `z`
performs the open calls `u` and then diverges host-free. -/
def LDLwXP (z : (wasmHShape H).self.Op) (u : List (HCall H)) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (l : List (OCall H)), z.2.2.funcs[z.1]? = some fi ∧
    fi.code = .wasm fn ∧
    LogDivXP z.2.2 (Frame.forCall fi.module z.2.1 fn.locals) [] (liftInstrs fn.body) l ∧
    u = l.map OCall.lift

/-- **The logged canonical semantics of an invocation, with divergence**: `wasmEvFunXP` plus
`div` after descent chains and after logged host-free divergence (`Shape.closeDLog`). -/
def wasmEvFunDXP : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.closeDLog wasmHOpenXP LDLwXP p.1 s p.2

/-! ## Productive runs inside one function -/

open Shape (streamAppend StreamConcat) in
/-- **The trees run forever within the function, making the open calls `ω`.** The constructors
are those of `LogDivXP`: finite parts run by `EvalLXPh` put their logs in front of the stream, a
completed call is recorded with its answer. The only way back into a tree is a loop's back edge,
so the definition is inductive except for `loopInf`: a loop iterating forever, the stream the
concatenation of the iteration logs, **of unbounded length**. -/
inductive InfLXP : Store H → Frame → List Val → List BExpr → (Nat → OCall H) → Prop where
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {ω : Nat → OCall H} :
      InfLXP s f stk args ω → InfLXP s f stk (.op i args :: es) ω
  | callK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      InfLXP s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es ω →
      InfLXP s f stk (.op (.call x) args :: es)
        ((l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]) ++ω ω)
  | indK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : TableIdx}
      {y : TypeIdx} {args es : List BExpr} {ad : AddrType} {i : BitVec ad.intType.width}
      {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {l₁ : List (OCall H)}
      {ω : Nat → OCall H}
      (hargs : EvalLXPh s f stk args l₁
        (s₁, f₁, .flow (.normal (.num ⟨.int ad.intType, i⟩ :: stk₁))))
      (hres : CallRes.IndRes s₁ f₁ x y ad i (some fa)) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      InfLXP s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es ω →
      InfLXP s f stk (.op (.callIndirect x y) args :: es)
        ((l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]) ++ω ω)
  | refK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {y : TypeIdx}
      {args es : List BExpr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal (.ref (.func fa) :: stk₁))))
      (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length)) :
      InfLXP s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es ω →
      InfLXP s f stk (.op (.callRef y) args :: es)
        ((l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]) ++ω ω)
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalLXPh s f stk args l₁ (s₁, f₁, .flow (.normal stk₁)))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      InfLXP s₂ f₂ stk₂ es ω → InfLXP s f stk (.op i args :: es) (l₁ ++ω ω)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {ω : Nat → OCall H} (har : arity f bt = some (np, nr)) :
      InfLXP s f (stk.take np) body ω → InfLXP s f stk (.block bt body :: es) ω
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ : List (OCall H)}
      {ω : Nat → OCall H} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) :
      InfLXP s₁ f₁ (vs.take nr ++ stk.drop np) es ω →
      InfLXP s f stk (.block bt body :: es) (l₁ ++ω ω)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {ω : Nat → OCall H} (har : arity f bt = some (np, nr)) :
      InfLXP s f (stk.take np) body ω → InfLXP s f stk (.loop bt body :: es) ω
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow (.normal vs))) :
      InfLXP s₁ f₁ (vs.take nr ++ stk.drop np) es ω →
      InfLXP s f stk (.loop bt body :: es) (l₁ ++ω ω)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow (.brk 0 vs))) :
      InfLXP s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) ω →
      InfLXP s f stk (.loop bt body :: es) (l₁ ++ω ω)
  /-- A loop iterating forever: the states `st n` at the loop head, the iteration logs `l n`
  (each iteration branching back, possibly by a caught exception), the stream their
  concatenation, of unbounded length. -/
  | loopInf {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {ω : Nat → OCall H} (st : Nat → Store H × Frame × List Val)
      (l : Nat → List (OCall H)) (h0 : st 0 = (s, f, stk))
      (har : ∀ n, arity (st n).2.1 bt = some (np, nr))
      (hit : ∀ n, ∃ vs, EvalLXPh (st n).1 (st n).2.1 ((st n).2.2.take np) body (l n)
          ((st (n + 1)).1, (st (n + 1)).2.1, .flow (.brk 0 vs)) ∧
        (st (n + 1)).2.2 = vs.take np ++ (st n).2.2.drop np)
      (hω : StreamConcat l ω) :
      InfLXP s f stk (.loop bt body :: es) ω
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {ω : Nat → OCall H} :
      InfLXP s f stk c ω → InfLXP s f stk (.if_ bt c t el :: es) ω
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {l₁ : List (OCall H)}
      {ω : Nat → OCall H}
      (hc : EvalLXPh s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : arity f₁ bt = some (np, nr)) :
      InfLXP s₁ f₁ (stk₁.take np) (if b then t else el) ω →
      InfLXP s f stk (.if_ bt c t el :: es) (l₁ ++ω ω)
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ : List (OCall H)} {ω : Nat → OCall H}
      (hc : EvalLXPh s f stk c l₁ (s₁, f₁, .flow (.normal (cv :: stk₁))))
      (hb : truthy cv = some b) (har : arity f₁ bt = some (np, nr))
      (harm : EvalLXPh s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, .flow fl))
      (hvs : fl.blockVals = some vs) :
      InfLXP s₂ f₂ (vs.take nr ++ stk₁.drop np) es ω →
      InfLXP s f stk (.if_ bt c t el :: es) ((l₁ ++ l₂) ++ω ω)
  /-- Inside a `try_table` handler. -/
  | handler {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {ω : Nat → OCall H}
      (har : arity f bt = some (np, nr)) :
      InfLXP s f (stk.take np) body ω → InfLXP s f stk (.tryTable bt cs body :: es) ω
  /-- After a `try_table` left normally or by a branch, including a caught exception. -/
  | tryK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {cs : List Catch}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ : List (OCall H)}
      {ω : Nat → OCall H} (har : arity f bt = some (np, nr))
      (hbody : EvalLXPh s f (stk.take np) body l₁ (s₁, f₁, .flow fl))
      (hvs : fl.blockVals = some vs) :
      InfLXP s₁ f₁ (vs.take nr ++ stk.drop np) es ω →
      InfLXP s f stk (.tryTable bt cs body :: es) (l₁ ++ω ω)

/-- **The productive open runs of a Wasm body**: the body of the Wasm function called runs
forever within its function (`InfLXP`), its open calls lifted to calls of `wasmHOpenXP`. A host
function has none. Host-independent. -/
def InfLwXP : Shape.OpenInf (wasmHShape H) := fun a s vs =>
  {ν | ∃ (fi : FuncInst H) (fn : Func) (ω : Nat → OCall H), s.funcs[a]? = some fi ∧
    fi.code = .wasm fn ∧
    InfLXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) ω ∧
    ν = fun i => (ω i).lift}

/-- **The productive runs of an invocation under the canonical relation**: the closure of
`wasmHOpenXP` with productive runs through unbounded recursion (including tail calls) and inside
one function after a descent path (`Shape.closeInfL`). No host semantics occurs. -/
def wasmEvInfNXP : PInf (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => Shape.closeInfL wasmHOpenXP InfLwXP p.1 s p.2

end Silmaril.Wasm.Abstract
