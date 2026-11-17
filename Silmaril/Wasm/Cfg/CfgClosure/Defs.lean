module

public import Silmaril.Wasm.Cfg.CfgSession.Defs

/-!
# The self-contained recursive CFG closure: definitions (H3)

`CfgSession.cfgSessionTriple` runs every body on the logged CFG machine, but its divergent part
(`CfgSession.LDLcfg`, through `MachineL.MLogDivL`) names the **native** closed oracle
(`XRecursionP.closedCallXP`, through `CloseOk`) for the calls answered after the log, and native
frame divergence (`XDivergeP.FunDivXP`) for diverging callees. This module removes both
dependencies: the oracle and the callee divergence become **parameters** of the machine's
divergence, which is then closed by CFG-defined objects only.

**Divergence over a call-answer predicate `A` and a callee divergence `D`** (`MachineLDiv`'s
definitions with the native objects as parameters): `StepKG A` (a logged step every entry of
which satisfies `A`), `InfKG A`, `CalleeDivKG A D`, `TailDivKG A D`, `MDivLG A D`, `FunDivLG A D`,
`MLogDivLG A D`. At `A = CloseOk closedCallXP`, `D = FunDivXP` they are `MachineLDiv`'s by
definition (`CfgClosure.Thms`, `stepK_eq` … `mLogDivL_eq`).

**The CFG instances:**

* `cfgAns`: the call answers of the CFG closure: an internal call `SCall.mk g args s b s₂` is
  answered when `([], ret b s₂)` is a behaviour of `CfgSession.cfgEvFunXPS` (`Shape.close
  cfgHOpenXPS`, every body on the logged machine) at `g`, `args`, `s`: a host-free finished
  behaviour. A host call is never closed-answered.
* `cfgFunDiv`: the **greatest fixpoint** of `D ↦ FunDivLG cfgAns D`: a call diverges on the
  machine when it is in some relation `R` every member of which diverges at its frame by
  `cfgAns`-answered machine steps, forever (`InfKG`), or to a call or pending tail call into a
  member of `R` (mutual, coinductive callee divergence, defined on the machine).
* `LDLcfgC`, `cfgEvFunDXPC`, `cfgEvFunDXPSC`: `CfgSession`'s divergent parts over `MLogDivLG cfgAns
  cfgFunDiv`, and `cfgSessionTripleC := (cfgEvFunDXPSC, cfgEvPendXPS, cfgEvInfNXP)`.

No definition in this module or in the parts of `CfgSession` it uses names `closedCallXP`,
`FunDivXP`, `EvalDivXP`, `LogDivXP`, `InfLXP`, `wasmEvFunXPS` or `sessionTripleXP`. The machine's
straight-line segments are run by the open logged relation `Abstract.EvalLXPS` on a segment's code
(`MachineL.MStepL`), with every call open (logged with an arbitrary answer), not answered by an
oracle. Theorems in `Silmaril.Wasm.Cfg.CfgClosure.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgClosure

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (SCall OCall HCall wasmHostSig wasmHShape)

variable {H : Type}

/-! ## Divergence over a call-answer predicate and a callee divergence -/

/-- **A step whose calls are answered by `A`.** -/
def StepKG (A : SCall H → Prop) (body : Expr) (st st' : MState H) : Prop :=
  ∃ l, MStepL body st l st' ∧ ∀ e ∈ l, A e

/-- **Infinite `A`-answered local steps** from `st`. -/
def InfKG (A : SCall H → Prop) (body : Expr) (st : MState H) : Prop :=
  ∃ g : ℕ → MState H, g 0 = st ∧ ∀ n, StepKG A body (g n) (g (n + 1))

/-- **A callee diverging by `D`**, reached by `A`-answered steps and an `A`-answered prefix. -/
def CalleeDivKG (A : SCall H → Prop) (D : Store H → Nat → List Val → Prop) (body : Expr)
    (st : MState H) : Prop :=
  ∃ (st' : MState H) (l : List (SCall H)) (z : (Abstract.wasmOShape H).self.Op),
    Relation.ReflTransGen (StepKG A body) st st' ∧ ReachL body st' l z ∧ (∀ e ∈ l, A e) ∧
      D z.2.2 z.1 z.2.1

/-- **A pending tail callee diverging by `D`**, reached by `A`-answered steps. -/
def TailDivKG (A : SCall H → Prop) (D : Store H → Nat → List Val → Prop) (body : Expr)
    (st : MState H) : Prop :=
  ∃ (st' : MState H) (l : List (SCall H)) (s₁ : Store H) (f₁ : Frame) (a n : Nat)
    (args : List Val),
    Relation.ReflTransGen (StepKG A body) st st' ∧ TailL body st' l (s₁, f₁, .tail a args n) ∧
      (∀ e ∈ l, A e) ∧ D s₁ a args

/-- **Divergence of the body from `st`**: infinite local steps, or a diverging callee. -/
def MDivLG (A : SCall H → Prop) (D : Store H → Nat → List Val → Prop) (body : Expr)
    (st : MState H) : Prop :=
  InfKG A body st ∨ CalleeDivKG A D body st

/-- **Divergence of a call at its frame**: the callee is a Wasm function whose body diverges from
the CFG entry, or reaches a diverging pending tail callee. -/
def FunDivLG (A : SCall H → Prop) (D : Store H → Nat → List Val → Prop) (s : Store H) (a : Nat)
    (args : List Val) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
    (MDivLG A D fn.body (initial fn.body s (Frame.forCall fi.module args fn.locals)) ∨
      TailDivKG A D fn.body (initial fn.body s (Frame.forCall fi.module args fn.locals)))

/-- **Divergence after the log `l`**, as `MachineL.MLogDivL` over `A` and `D`. -/
def MLogDivLG (A : SCall H → Prop) (D : Store H → Nat → List Val → Prop) (body : Expr)
    (st : MState H) (l : List (SCall H)) : Prop :=
  ∃ (st₁ : MState H) (l₁ l₂ l₃ : List (SCall H)), MRunL body st l₁ st₁ ∧ l = l₁ ++ l₂ ∧
    (∀ e ∈ l₃, A e) ∧
    ((∃ st₂, MStepL body st₁ (l₂ ++ l₃) st₂ ∧ MDivLG A D body st₂) ∨
      (∃ z, ReachL body st₁ (l₂ ++ l₃) z ∧ D z.2.2 z.1 z.2.1))

/-! ## The CFG instances -/

/-- **The call answers of the CFG closure**: an internal call is answered by `b` leaving `s₂` when
`([], ret b s₂)` is a behaviour of `cfgEvFunXPS` (bodies run on the logged machine). -/
def cfgAns : SCall H → Prop
  | ⟨.inr ⟨g, (args, s)⟩, (b, s₂)⟩ =>
    (([] : List (Call (wasmHostSig H))), End.ret b s₂) ∈ cfgEvFunXPS s (g, args)
  | ⟨.inl _, _⟩ => False

/-- **Callee divergence of the CFG closure**, coinductively: the greatest relation `R` every
member of which diverges at its frame by `cfgAns`-answered machine steps, calls and tail calls
into `R` diverging. -/
def cfgFunDiv (s : Store H) (a : Nat) (args : List Val) : Prop :=
  ∃ R : Store H → Nat → List Val → Prop,
    (∀ s' a' args', R s' a' args' → FunDivLG cfgAns R s' a' args') ∧ R s a args

/-- **Logged divergence of a call on the machine, CFG-closed**: as `CfgSession.LDLcfg`, over
`cfgAns` and `cfgFunDiv`. -/
def LDLcfgC (z : (wasmHShape H).self.Op) (u : List (HCall H)) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (L : List (OCall H)), z.2.2.funcs[z.1]? = some fi ∧
    fi.code = .wasm fn ∧
    MLogDivLG cfgAns cfgFunDiv fn.body
      (initial fn.body z.2.2 (Frame.forCall fi.module z.2.1 fn.locals)) (L.map OCall.toS) ∧
    u = L.map OCall.lift

/-- **The canonical CFG closure with CFG-closed divergence.** -/
def cfgEvFunDXPC : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.closeDLog cfgHOpenXP LDLcfgC p.1 s p.2

/-- **The CFG session closure with CFG-closed divergence.** -/
def cfgEvFunDXPSC :
    AFun (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  fun s p => cfgEvFunXPS s p ∪ {y | y.2 = .div ∧ (y.1, End.div) ∈ cfgEvFunDXPC s p}

/-- **The self-contained CFG session triple**: finished, divergent, pending and productive parts,
every body run on the logged machine, every closed answer and callee divergence CFG-defined. -/
def cfgSessionTripleC :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  (cfgEvFunDXPSC, cfgEvPendXPS, cfgEvInfNXP)

end Silmaril.Wasm.Cfg.CfgClosure
