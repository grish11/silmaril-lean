module

public import Silmaril.Sim.X86.G.Defs
public import Silmaril.Sim.Wasm.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs

/-!
# The G simulator as a `Silmaril.Sim` simulator (header)

The G simulator stated in the simulator framework (`Silmaril.Sim.Wasm.ExportSim`,
`Silmaril.Sim.Wasm.ExportSim.Cert`, `Silmaril.Sim.Sound`):

* `xRef cmd`: the **reference machine**. Commands `C` name decoded instructions with lengths
  (`cmd c`); a state is an `Silmaril.X86.State` with memory whose modelled flags (CF, ZF, SF, OF)
  are defined; a step runs `Silmaril.X86.Ext.exec` and **concretizes** the result: flags the
  model leaves undefined take any value (`Concretizes`), as on a real processor. Its view
  (`xview`) shows registers, RIP and the four flags (`0`/`1`).
* `gview mi`: the simulator's view of a store: the `i64` values of the location globals of the
  instance `mi`.
* `exportSim P host mi addr`: the simulator as an `ExportSim`: command `c` is the export at
  address `addr c`, called without arguments, returning nothing.
* `stepSpec`: the every-run specification of a full step method (body `emit i len`, RIP
  included).

The certificate (`Silmaril.Proofs.Sim.X86.GCert.Cert`) assumes a store layout: the instance's
globals are `0..22` (`List.range 23`, as after instantiating `simModule`-like modules with no
imported globals), and the store holds at `addr c` a function instance running `emit (cmd c)`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GCert

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim Silmaril.Sim.Wasm Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Hoare (FSpec)
open Silmaril.X86 (State Flags Reg)

/-- A concrete flag refines a model flag: equal unless the model leaves it undefined. -/
def FlagRefines (m c : Option Bool) : Prop := m = none ∨ c = m

/-- `τ` is a concretization of the model result `σ'`: same registers, RIP and FS base; every
flag the model defines is kept, the others are arbitrary; the modelled flags are defined. -/
def Concretizes (σ' τ : State) : Prop :=
  τ.regs = σ'.regs ∧ τ.rip = σ'.rip ∧ τ.fsBase = σ'.fsBase ∧
    FlagRefines σ'.flags.carry τ.flags.carry ∧ FlagRefines σ'.flags.parity τ.flags.parity ∧
    FlagRefines σ'.flags.adjust τ.flags.adjust ∧ FlagRefines σ'.flags.zero τ.flags.zero ∧
    FlagRefines σ'.flags.sign τ.flags.sign ∧ FlagRefines σ'.flags.overflow τ.flags.overflow ∧
    Defined τ.flags

/-- The reference view of an x86 state on the modelled locations. -/
def xview (σ : State) : PState Loc (BitVec 64)
  | .reg r => some (σ.read r)
  | .rip => some σ.rip
  | .cf => σ.flags.carry.map b64
  | .zf => σ.flags.zero.map b64
  | .sf => σ.flags.sign.map b64
  | .of => σ.flags.overflow.map b64

/-- **The reference machine**: `Silmaril.X86.Ext.exec` of the command's instruction, results
concretized, on states with defined modelled flags. -/
def xRef {C : Type} (cmd : C → Silmaril.X86.Ext.Instr × Nat) : Machine C Loc (BitVec 64) where
  St := {b : State × Silmaril.Process.Memory // Defined b.1.flags}
  view b := xview b.1.1
  step c b b' := ∃ σ', Silmaril.X86.Ext.exec (cmd c).1 b.1.1 b.1.2 (cmd c).2 = .ok σ' b'.1.2 ∧
    Concretizes σ' b'.1.1

/-- The bits of an `i64` value. -/
def valBits : Option Val → Option (BitVec 64)
  | some (.num ⟨.int .i64, x⟩) => some x
  | _ => none

variable {H : Type}

/-- The simulator's view of a store through the instance `mi`. -/
def gview (mi : ModuleInst) (s : Store H) : PState Loc (BitVec 64) :=
  fun l => valBits (gval s (Frame.forCall mi [] []) l)

/-- **The G simulator as an `ExportSim`**: command `c` calls the export at `addr c` with the
arguments `args c`; a successful call returns nothing. -/
def exportSim {C : Type} (P : Profile) (host : HostSemantics H) (mi : ModuleInst)
    (addr : C → Nat) (args : C → List Val) : ExportSim C Loc (BitVec 64) H :=
  ⟨P, host, gview mi, addr, args, fun _ res => res = []⟩

/-- The precondition of a command's export: the function instance, the arguments, and a store
holding registers, RIP and flag bits. -/
def cmdPre (fi : FuncInst H) (a : Nat) (args : List Val) (s : Store H) (args' : List Val) :
    Prop :=
  s.funcs[a]? = some fi ∧ args' = args ∧ ∃ R, GRegs s (Frame.forCall fi.module [] []) R

/-- The postcondition of a command's export (on the new store): only modelled globals change,
and the new store encodes `Ext.exec i σ m len` for every state `σ` the old one encodes on which
`i` retires. -/
def cmdPost (fi : FuncInst H) (i : Silmaril.X86.Ext.Instr) (len : Nat) (s s' : Store H) :
    Prop :=
  Frames s s' (Frame.forCall fi.module [] []) ∧
    ∀ (σ σ' : State) (m m' : Silmaril.Process.Memory),
      Enc s (Frame.forCall fi.module [] []) σ → Silmaril.X86.Ext.exec i σ m len = .ok σ' m' →
      Enc s' (Frame.forCall fi.module [] []) σ'

/-- The every-run specification of the export of a command `(i, len)` with arguments `args`:
every call returns nothing, and `cmdPost` holds. -/
def cmdSpec (fi : FuncInst H) (a : Nat) (args : List Val) (i : Silmaril.X86.Ext.Instr)
    (len : Nat) : FSpec H where
  pre := cmdPre fi a args
  post s _ s' o := o = .normal [] ∧ cmdPost fi i len s s'

/-- The specification of a **full step** method (body `emit i len`, no arguments). -/
abbrev stepSpec (fi : FuncInst H) (a : Nat) (i : Silmaril.X86.Ext.Instr) (len : Nat) : FSpec H :=
  cmdSpec fi a [] i len

/-! ## A concrete instance: the step methods of `max` -/

/-- The commands of `max`'s body. -/
def maxCmd : Fin 3 → Silmaril.X86.Ext.Instr × Nat
  | 0 => (.mov .q (.reg .rax) .rdi, 3)
  | 1 => (.alu .q .cmp (.reg .rax) .rsi, 3)
  | 2 => (.cmov .q .l .rax (.reg .rsi), 4)

/-- **Full step methods** (`emit i len`, RIP included) for the three instructions of `max`, as a
`wat3!` quotation. -/
def stepModule : Module := wat3! r#"
(module
  (global $rax (mut i64) (i64.const 0))
  (global $rcx (mut i64) (i64.const 0))
  (global $rdx (mut i64) (i64.const 0))
  (global $rbx (mut i64) (i64.const 0))
  (global $rsp (mut i64) (i64.const 0))
  (global $rbp (mut i64) (i64.const 0))
  (global $rsi (mut i64) (i64.const 0))
  (global $rdi (mut i64) (i64.const 0))
  (global $r8 (mut i64) (i64.const 0))
  (global $r9 (mut i64) (i64.const 0))
  (global $r10 (mut i64) (i64.const 0))
  (global $r11 (mut i64) (i64.const 0))
  (global $r12 (mut i64) (i64.const 0))
  (global $r13 (mut i64) (i64.const 0))
  (global $r14 (mut i64) (i64.const 0))
  (global $r15 (mut i64) (i64.const 0))
  (global $rip (mut i64) (i64.const 0))
  (global $cf (mut i64) (i64.const 0))
  (global $pf (mut i64) (i64.const 0))
  (global $af (mut i64) (i64.const 0))
  (global $zf (mut i64) (i64.const 0))
  (global $sf (mut i64) (i64.const 0))
  (global $of (mut i64) (i64.const 0))
  (func $s_mov_rax_rdi (export "s_mov_rax_rdi")
    (global.set $rax (global.get $rdi))
    (global.set $rip (i64.add (global.get $rip) (i64.const 3))))
  (func $s_cmp_rax_rsi (export "s_cmp_rax_rsi")
    (global.set $cf (i64.shr_u (i64.or (i64.and (i64.xor (global.get $rax) (i64.const -1)) (global.get $rsi)) (i64.and (i64.xor (i64.xor (global.get $rax) (global.get $rsi)) (i64.const -1)) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63)))
    (global.set $of (i64.shr_u (i64.and (i64.xor (global.get $rax) (global.get $rsi)) (i64.xor (global.get $rax) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63)))
    (global.set $zf (i64.xor (i64.const 1) (i64.shr_u (i64.or (i64.sub (global.get $rax) (global.get $rsi)) (i64.sub (i64.const 0) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63))))
    (global.set $sf (i64.shr_u (i64.sub (global.get $rax) (global.get $rsi)) (i64.const 63)))
    (global.set $rip (i64.add (global.get $rip) (i64.const 3))))
  (func $s_cmovl_rax_rsi (export "s_cmovl_rax_rsi")
    (global.set $rax (i64.xor (global.get $rax) (i64.and (i64.xor (global.get $rax) (global.get $rsi))
      (i64.sub (i64.const 0) (i64.xor (global.get $sf) (global.get $of))))))
    (global.set $rip (i64.add (global.get $rip) (i64.const 4)))))
"#

/-- The instantiation of `stepModule` against no imports. -/
def stepRun : Option (Store Nat × Frame × Option FuncIdx) :=
  instantiateOnce? (Silmaril.Wasm.Game.importStore []) stepModule []

/-- The store after instantiation. -/
def stepStore : Store Nat :=
  match stepRun with
  | some (s, _, _) => s
  | none => {}

/-- The module instance. -/
def stepMI : ModuleInst :=
  match stepRun with
  | some (_, f, _) => f.module
  | none => {}

/-! ## The ABI-style simulator `simModule` as an `ExportSim` -/

/-- The commands of `Silmaril.Sim.X86.G.simModule`: its six methods (`i_mov_rax_rdi`,
`i_add_rax_rsi`, `i_sub_rax_rsi`, `i_xor_rax_rsi`, `i_cmp_rax_rsi`, `i_cmovl_rax_rsi`) and
`i_next n`. -/
inductive SCmd where
  | m (k : Fin 6)
  | next (n : BitVec 64)

/-- The instruction of method `k`. -/
def simInstr : Fin 6 → Silmaril.X86.Ext.Instr
  | 0 => .mov .q (.reg .rax) .rdi
  | 1 => .alu .q .add (.reg .rax) .rsi
  | 2 => .alu .q .sub (.reg .rax) .rsi
  | 3 => .alu .q .xor (.reg .rax) .rsi
  | 4 => .alu .q .cmp (.reg .rax) .rsi
  | 5 => .cmov .q .l .rax (.reg .rsi)

/-- **The x86 meaning of a simulator command**: a method is its instruction executed with
length `0` (its effect; `Ext.exec` then leaves RIP unchanged), `i_next n` is a NOP of length
`n` (RIP advances by `n`). `Ext.exec i σ m len` is method-then-`i_next len` (`exec_split`). -/
def simCmd : SCmd → Silmaril.X86.Ext.Instr × Nat
  | .m k => (simInstr k, 0)
  | .next n => (.nop 0, n.toNat)

/-- The export address of a command in the instantiated `simModule`. -/
def simAddr : SCmd → Nat
  | .m k => k.val
  | .next _ => 6

/-- The arguments of a command's export call. -/
def simArgs : SCmd → List Val
  | .m _ => []
  | .next n => [Val.i64 n]

/-- The assumptions of the certificate: the instance `mi` has the location globals at addresses
`0..22`, the base store `s₀` holds at `addr c` a function instance `fi c` of `mi` whose every
call meets `cmdSpec` for the command's instruction and arguments, and every command retires from
states with defined modelled flags. -/
structure Hyps {C : Type} (P : Profile) (host : HostSemantics H)
    (cmd : C → Silmaril.X86.Ext.Instr × Nat) (mi : ModuleInst) (addr : C → Nat)
    (args : C → List Val) (s₀ : Store H) (fi : C → FuncInst H) : Prop where
  globals : mi.globals = List.range 23
  funcs : ∀ c, s₀.funcs[addr c]? = some (fi c)
  module : ∀ c, (fi c).module = mi
  valid : ∀ c, Silmaril.Wasm.Logic.Hoare.FSpecValid P host (addr c) (cmdSpec (fi c) (addr c) (args c) (cmd c).1 (cmd c).2)
  progress : ∀ c (σ : State) m, Defined σ.flags →
    ∃ σ', Silmaril.X86.Ext.exec (cmd c).1 σ m (cmd c).2 = .ok σ' m

end Silmaril.Sim.X86.GCert
