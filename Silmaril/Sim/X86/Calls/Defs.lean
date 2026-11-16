module

public import Silmaril.Sim.X86.G.Defs
public import Silmaril.Wasm.Logic.VC.Defs

/-!
# The P-calls `max` of the G simulator, verified modularly: definitions

`Silmaril.Sim.X86.G.simModule` holds the G simulator's methods for a few instruction instances
and the program `max` in the **P-calls** representation: its body is only calls of the methods
(`i_mov_rax_rdi`, `i_next 3`, `i_cmp_rax_rsi`, `i_next 3`, `i_cmovl_rax_rsi`, `i_next 4`).
Here every method gets a Wasm-level specification (`mspec`): from a store whose instance
globals `0‥22` hold `i64`s (`AllI64`), the call returns nothing, keeps the functions and maps
the global file `regs` by a Lean function (`Fmov`, `Fcmp`, `Fcmovl`, `Fnext`, transcribing the
Wasm code). `maxSpecs` is the **spec context** for `max`'s calls
(`Silmaril.Wasm.Logic.VC.VCSpecs`), `maxSpec` the specification of `max` itself: the global file
after the call is the composition of the method functions.

Global numbering (as `simModule`): `0‥15` the GPRs (`rax = 0`, `rsi = 6`, `rdi = 7`), `16` RIP,
`17` CF, `18` PF, `19` AF, `20` ZF, `21` SF, `22` OF. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Calls

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.VC (globalVal VCSpecs)
open Silmaril.Wasm.Logic.Hoare (FSpec)

variable {H : Type}

/-- The global file: the `i64` value of global `k` of the instance (`0` if not an `i64`). -/
def regs (s : Store H) (mi : ModuleInst) (k : Nat) : BitVec 64 :=
  match globalVal s mi k with
  | some (.num ⟨.int .i64, v⟩) => v
  | _ => 0

/-- Globals `0‥22` of the instance exist and hold `i64`s. -/
def AllI64 (s : Store H) (mi : ModuleInst) : Prop :=
  ∀ k < 23, ∃ v : BitVec 64, globalVal s mi k = some (.num ⟨.int .i64, v⟩)

/-- **A method specification**: the function instance `fi` at address `a`, called on arguments
satisfying `Arg` from a store with `AllI64`, returns nothing, keeps the functions and `AllI64`,
and maps the global file by `F args`. -/
def mspec (mi : ModuleInst) (fi : FuncInst H) (a : Nat) (Arg : List Val → Prop)
    (F : List Val → (Nat → BitVec 64) → (Nat → BitVec 64)) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ Arg args ∧ AllI64 s mi
  post s args s' o := o = .normal [] ∧ s'.funcs = s.funcs ∧ AllI64 s' mi ∧
    regs s' mi = F args (regs s mi)

/-- `i_mov_rax_rdi`. -/
def Fmov : List Val → (Nat → BitVec 64) → (Nat → BitVec 64) := fun _ g =>
  Function.update g 0 (g 7)

/-- `i_cmp_rax_rsi`: CF, OF, ZF, SF of `rax - rsi` (silmaril's bit formulas, as in `aluCode`). -/
def Fcmp : List Val → (Nat → BitVec 64) → (Nat → BitVec 64) := fun _ g =>
  let x := g 0; let y := g 6
  Function.update (Function.update (Function.update (Function.update g
    17 ((((x ^^^ -1) &&& y) ||| (((x ^^^ y) ^^^ -1) &&& (x - y))) >>> 63))
    22 (((x ^^^ y) &&& (x ^^^ (x - y))) >>> 63))
    20 (1 ^^^ (((x - y) ||| (0 - (x - y))) >>> 63)))
    21 ((x - y) >>> 63)

/-- `i_cmovl_rax_rsi`: `rax := rax xor ((rax xor rsi) and (0 - (SF xor OF)))`. -/
def Fcmovl : List Val → (Nat → BitVec 64) → (Nat → BitVec 64) := fun _ g =>
  Function.update g 0 (g 0 ^^^ ((g 0 ^^^ g 6) &&& (0 - (g 21 ^^^ g 22))))

/-- `i_next len`: `rip += len`. -/
def Fnext : List Val → (Nat → BitVec 64) → (Nat → BitVec 64) := fun args g =>
  match args with
  | [.num ⟨.int .i64, len⟩] => Function.update g 16 (g 16 + (show BitVec 64 from len))
  | _ => g

/-- The arguments of `i_next`. -/
def NextArg (args : List Val) : Prop := ∃ len : BitVec 64, args = [Val.i64 len]

/-- **The spec context of `max`**: the methods at addresses `a0` (`mov`), `a4` (`cmp`), `a5`
(`cmovl`), `a6` (`next`), function instances `f0 … f6`. -/
@[reducible] def maxSpecs (mi : ModuleInst) (a0 a4 a5 a6 : Nat) (f0 f4 f5 f6 : FuncInst H) :
    VCSpecs H :=
  ⟨fun a => if a = a0 then some (0, mspec mi f0 a0 (· = []) Fmov)
    else if a = a4 then some (0, mspec mi f4 a4 (· = []) Fcmp)
    else if a = a5 then some (0, mspec mi f5 a5 (· = []) Fcmovl)
    else if a = a6 then some (1, mspec mi f6 a6 NextArg Fnext)
    else none⟩

/-- **The specification of `max`** (function instance `fi` at address `a`): the global file
after the call is that of the method sequence. -/
def maxSpec (mi : ModuleInst) (fi : FuncInst H) (a a0 a4 a5 a6 : Nat)
    (f0 f4 f5 f6 : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ args = [] ∧ AllI64 s mi ∧ s.funcs[a0]? = some f0 ∧
    s.funcs[a4]? = some f4 ∧ s.funcs[a5]? = some f5 ∧ s.funcs[a6]? = some f6
  post s _ s' o := o = .normal [] ∧
    regs s' mi = Fnext [Val.i64 4] (Fcmovl [] (Fnext [Val.i64 3]
      (Fcmp [] (Fnext [Val.i64 3] (Fmov [] (regs s mi))))))

end Silmaril.Sim.X86.Calls
