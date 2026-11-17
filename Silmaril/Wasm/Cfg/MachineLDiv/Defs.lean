module

public import Silmaril.Wasm.Cfg.MachineL.Defs
public import Silmaril.Wasm.Abstract.XDivergeP.Defs
public import Silmaril.Games.Abstract.ModuleInf.Defs

/-!
# Quiescent divergence of the logged block-CFG machine (H2, definitions)

The logged machine `MachineL.MStepL` records every call it makes, with an arbitrary answer. **Host-free
divergence** is divergence where every recorded call is answered by the closed native oracle
`XRecursionP.closedCallXP` (`MachineL.CloseOk`: its values trimmed to the callee's result arity,
or its exception, or its trap, with the store it leaves). It has three distinct forms, kept apart:

* `InfK body st`: **infinite local steps**, an infinite run of the machine on `body` from `st` whose
  every step is answered by the oracle (`StepK`). The steps run straight-line code, enter arms and
  branch, possibly calling and returning from finitely-answered callees; nothing diverges inside a
  callee.
* `CalleeDivK body st`: **a diverging callee**, a finite oracle-answered run to a block reaching
  an internal call (`MachineL.ReachL`, after an oracle-answered prefix of the block) whose callee
  diverges at the frame (`XDivergeP.FunDivXP`).
* `TailDivK body st`: **a diverging tail callee**, a finite oracle-answered run to a block whose
  straight-line code ends in a pending tail call (`MachineL.TailL`), made when the function's frame
  is left, whose callee diverges at the frame. This is a function-level form: a body ending in a
  pending tail call has ended, and its own run does not diverge.

`MDivL body st := InfK body st ∨ CalleeDivK body st` is the divergence of the body from `st`.
`FunDivL s a args` is the divergence of a call at its frame, as `XDivergeP.funDivXP_iff` states it:
the callee is a Wasm function whose body diverges from the CFG entry (`MDivL`), or reaches a
diverging tail callee (`TailDivK`).

**After a log** (`MLogDivL body st l`): logged steps with arbitrary answers, then, from a boundary
inside a step, host-free divergence (`MDivL`, or a reached call whose callee diverges). The log is
the calls before the boundary. The logged calls of the canonical semantics (`Abstract.OCall`, as
`Abstract.LogDivXP` records them) are read as session calls by `Abstract.OCall.toS`.

**Productive runs** (`ProdL body st ω`): an infinite logged run whose logs concatenate to the
stream `ω` with infinitely many calls, each with an arbitrary answer.

The diverging callees are named by native frame divergence (`FunDivXP`), as the closed answers are
the native oracle's: this is the machine's divergence over the native closed semantics, not a
recursive CFG closure (H3).

Theorems in `Silmaril.Wasm.Cfg.MachineLDiv.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (SCall)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (FunDivXP)

variable {H : Type}

/-- **A step answered by the closed oracle**: a logged step every call of which is a
`closedCallXP`-answer. -/
def StepK (body : Expr) (st st' : MState H) : Prop :=
  ∃ l, MStepL body st l st' ∧ ∀ e ∈ l, CloseOk closedCallXP e

/-- **Infinite local steps**: an infinite run of oracle-answered steps from `st`. -/
def InfK (body : Expr) (st : MState H) : Prop :=
  ∃ g : ℕ → MState H, g 0 = st ∧ ∀ n, StepK body (g n) (g (n + 1))

/-- **A diverging callee**: finitely many oracle-answered steps to a block reaching an internal call,
after an oracle-answered prefix, whose callee diverges at the frame. -/
def CalleeDivK (body : Expr) (st : MState H) : Prop :=
  ∃ (st' : MState H) (l : List (SCall H)) (z : (Abstract.wasmOShape H).self.Op),
    Relation.ReflTransGen (StepK body) st st' ∧ ReachL body st' l z ∧
      (∀ e ∈ l, CloseOk closedCallXP e) ∧ FunDivXP z.2.2 z.1 z.2.1

/-- **A diverging tail callee**: finitely many oracle-answered steps to a block whose
oracle-answered straight-line code ends in a pending tail call whose callee diverges at the
frame. -/
def TailDivK (body : Expr) (st : MState H) : Prop :=
  ∃ (st' : MState H) (l : List (SCall H)) (s₁ : Store H) (f₁ : Frame) (a n : Nat)
    (args : List Val),
    Relation.ReflTransGen (StepK body) st st' ∧ TailL body st' l (s₁, f₁, .tail a args n) ∧
      (∀ e ∈ l, CloseOk closedCallXP e) ∧ FunDivXP s₁ a args

/-- **Divergence of the body from `st`**: infinite local steps, or a diverging callee. -/
def MDivL (body : Expr) (st : MState H) : Prop :=
  InfK body st ∨ CalleeDivK body st

/-- **Divergence of a call at its frame, on the machine**: the callee is a Wasm function whose body
diverges from the CFG entry in the call's frame, or reaches a diverging tail callee. -/
def FunDivL (s : Store H) (a : Nat) (args : List Val) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    (MDivL fn.body (initial fn.body s (Frame.forCall fi.module args fn.locals)) ∨
      TailDivK fn.body (initial fn.body s (Frame.forCall fi.module args fn.locals)))

/-- **Divergence after a log, on the machine**: logged steps with the log `l₁`, then from `st₁` a
step whose log is `l₂` followed by oracle-answered entries `l₃`, after which the body diverges
(`MDivL`); or a block reaching, after `l₂` then oracle-answered entries, an internal call whose
callee diverges at the frame. The log is `l₁ ++ l₂`: the calls before the boundary, which may
fall inside a step. -/
def MLogDivL (body : Expr) (st : MState H) (l : List (SCall H)) : Prop :=
  ∃ (st₁ : MState H) (l₁ l₂ l₃ : List (SCall H)), MRunL body st l₁ st₁ ∧ l = l₁ ++ l₂ ∧
    (∀ e ∈ l₃, CloseOk closedCallXP e) ∧
    ((∃ st₂, MStepL body st₁ (l₂ ++ l₃) st₂ ∧ MDivL body st₂) ∨
      (∃ z, ReachL body st₁ (l₂ ++ l₃) z ∧ FunDivXP z.2.2 z.1 z.2.1))

/-- **A productive run of the machine**: an infinite logged run from `st` (every answer
arbitrary) whose step logs concatenate to the stream `ω`, of unbounded length: infinitely many
calls. -/
def ProdL (body : Expr) (st : MState H) (ω : ℕ → SCall H) : Prop :=
  ∃ (g : ℕ → MState H) (lg : ℕ → List (SCall H)), g 0 = st ∧
    (∀ n, MStepL body (g n) (lg n) (g (n + 1))) ∧ Games.Abstract.Shape.StreamConcat lg ω

end Silmaril.Wasm.Cfg.MachineL
