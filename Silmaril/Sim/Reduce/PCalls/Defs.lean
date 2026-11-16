module

public import Silmaril.Sim.X86.GCert.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.Wasm.Game.Signature.Defs

/-!
# P-calls soundness for the certified G fragment: definitions

The program representation **P-calls** (`docs/projects/wasm-sim-abi.md`): an x86-64 straight-line
program becomes a Wasm function body that **calls** one simulator method per instruction. Here
the methods have *per-instruction granularity*: each is a full step `emit i len` of the
G simulator (`Silmaril.Sim.X86.G.emit`, RIP update included; `wasm-sim reduce --granularity insn`),
so every state between two calls is an x86 state and P-calls soundness is a plain induction.

* `callsCode xs`: the P-calls body, `call x₁; …; call xₙ`.
* `StepCtx P host s f mi p xs`: call `k` reaches, through the caller's instance, a function
  instance of the simulator instance `mi` meeting the every-run step specification
  (`Silmaril.Sim.X86.GCert.stepSpec`) of the `k`-th instruction of `p`. These are the **method
  pieces** (each one a Wasm problem about one simulator function; `step_valid` solves them for
  bodies `emit i len`).
* `StepFns s f mi p xs`: call `k` reaches a function instance of `mi` whose code *is*
  `emit i len` of the `k`-th instruction (a concrete simulator; implies `StepCtx`).
* **`Piece P host p xs Pre Post`** — the Wasm problem of the P-calls body, the piece a Wasm
  solver attacks: under `StepCtx` (the methods' contracts, as for imports), from every store
  holding registers `R` (`GRegs`) with `Pre R`, every run of the body that stops falls through
  with registers `R'` satisfying `Post R R'`.

`Silmaril.Sim.Reduce.PCalls.Thms`: `xproblem_of_piece` (a solved piece and a concrete simulator instance
solve the x86 problem `Silmaril.Sim.X86.G.XProblem p Pre Post`).
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.PCalls

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GCert
open Silmaril.Wasm.Logic.Hoare (FSpecValid HWP)
open Silmaril.X86 (Reg)

variable {H : Type}

/-- The P-calls body: one call per instruction. -/
def callsCode (xs : List FuncIdx) : List Instr := xs.map .call

/-- The simulator's frame view for instance `mi`. -/
abbrev simFrame (mi : ModuleInst) : Frame := Frame.forCall mi [] []

/-- Call `k` reaches a function of `mi` meeting the step specification of instruction `k`. -/
def StepCtx (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (mi : ModuleInst) :
    XProg → List FuncIdx → Prop
  | [], [] => True
  | (i, len) :: p, x :: xs =>
    (∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧ fi.module = mi ∧
      FSpecValid P host a (stepSpec fi a i len)) ∧ StepCtx P host s f mi p xs
  | _, _ => False

/-- Call `k` reaches a function of `mi` whose code is the step method of instruction `k`. -/
def StepFns (s : Store H) (f : Frame) (mi : ModuleInst) : XProg → List FuncIdx → Prop
  | [], [] => True
  | (i, len) :: p, x :: xs =>
    (∃ a fi func, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧ fi.module = mi ∧
      fi.code = .wasm func ∧ Silmaril.Wasm.Game.FnType.ofDefType? fi.type = some ⟨[], []⟩ ∧
      func.locals = [] ∧ emit i len = some func.body) ∧ StepFns s f mi p xs
  | _, _ => False

/-- **The Wasm piece of a P-calls body.** -/
def Piece (P : Profile) (host : HostSemantics H) (p : XProg) (xs : List FuncIdx)
    (Pre : (Reg → BitVec 64) → Prop) (Post : (Reg → BitVec 64) → (Reg → BitVec 64) → Prop) :
    Prop :=
  ∀ (s : Store H) (f : Frame) (mi : ModuleInst) (R : Reg → BitVec 64),
    StepCtx P host s f mi p xs → GRegs s (simFrame mi) R → Pre R →
    HWP P host s f (expression (callsCode xs)) fun s' _ o => o = .normal [] ∧
      ∀ R' : Reg → BitVec 64, (∀ r, gval s' (simFrame mi) (.reg r) = some (Val.i64 (R' r))) →
        Post R R'

end Silmaril.Sim.Reduce.PCalls
