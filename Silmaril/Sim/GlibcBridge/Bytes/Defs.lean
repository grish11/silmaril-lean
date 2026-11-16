module

public import Silmaril.Sim.GlibcBridge.Defs
public import Silmaril.Sim.X86.GM.Defs
public import Silmaril.X86.Ext9.Defs

/-!
# The glibc hello's actual bytes on the GM simulator (header)

`main` and the `puts@plt` stub of `examples/wasm-sim/glibc-bridge/progs/hello-glibc` (`gcc -O2
-no-pie`, glibc 2.39), run by a **dispatcher** over a code table on the GM simulator (`Silmaril.Sim.X86.GM`)
(guest stack in a window of Wasm memory 0, `Silmaril.Sim.X86.GM`), with the foreign addresses of
`glibcrun.wat` answered by import contracts.

* `ghelloTab`: the nine instructions at their addresses, as decoded from the bytes
  (`mainBytes`, `pltBytes`; `Silmaril.Proofs.Sim.GlibcBridge.Bytes.tabAt_ghello`):
  `puts@plt`: `endbr64; jmp *0x2fb6(%rip)` (GOT `0x404000`); `main`: `endbr64; sub $8,%rsp;
  lea 0xfa5(%rip),%rdi; call puts@plt; xor %eax,%eax; add $8,%rsp; ret`.
* **Methods added to GM** (this extension module; the GM files unchanged), `emitB W r i n`
  for the instruction `i` of length `n` at address `r`:
  `endbr64` ↦ GM's method of `jmp8 0` (`rip += n`); `lea r, [rip + d]` ↦ GM's method of
  `movabs r, (r + n + d)` (the address is known when the method is generated, as in the
  dispatcher's table); everything else GM's `emitM`.
* `jmp *[rip + d]` (`BI.jmpInd`, an `Ext9` form, not in `Ext`): `rip :=` the answer of the
  guest-memory import `ld` at `r + n + d` (the GOT lies outside the stack window; at runtime this
  is `mem.load64`). Its x86 meaning is `Ext9.execNew (.jmpInd (.mem (Mem.ofRip d)))`.
* Foreign addresses (`glibcrun.wat`): `putsF = 0x7f00_0000_0000` (eager-bound `GOT[puts]`) is
  import 0 (`puts`, System V arguments) and `mainRet = 0x7f00_0000_0ff0` import 1 (`exit(rax)`).
  At an import that returns, the driver performs `rax :=` result, clobbers the scratch
  registers (`extStore0`) and **returns with GM's `ret` method** (pops the return address
  from the stack window).
* **`BRun C mem W ld fm tab`**: runs of the dispatcher; `blinkObs`: its observables.
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G
open Silmaril.Sim.X86.GM
open Silmaril.Sim.WasiBridge

variable {H : Type}

/-- A table instruction: an `Ext` instruction or `jmp *[rip + d]`. -/
inductive BI where
  | x (i : Silmaril.X86.Ext.Instr)
  | jmpInd (d : BitVec 32)

/-- A code table: address, instruction, length. -/
abbrev BTab := List (Word × BI × Nat)

/-- The entry at an address. -/
def lookupB (tab : BTab) (r : Word) : Option (BI × Nat) :=
  (tab.find? fun e => e.1 == r).map (·.2)

/-- **The methods**: GM's, plus `endbr64` and RIP-relative `lea`. -/
def emitB (W : Win) (r : Word) (i : Silmaril.X86.Ext.Instr) (n : Nat) : Option (List Instr) :=
  match i with
  | .endbr64 => emitM W (.jmp8 0) n
  | .lea .q d m =>
    if m.base = .rip then emitM W (.movabs d (r + BitVec.ofNat 64 n + m.disp.signExtend 64)) n
    else none
  | i => emitM W i n

/-- The store after an import returned `v`, scratch registers `ws` (before the driver's `ret`). -/
def extStore0 (s : Store H) (f : Frame) (v : Word) (ws : Reg → Word) : Store H :=
  updRegs (upd s f (.reg .rax) (Val.i64 v)) f (scratch.map fun q => (q, ws q))

/-- **Dispatcher runs** with import contracts `C`, contract memory `mem`, stack window `W`,
guest loads `ld` outside the window, foreign addresses `fm`, code table `tab`. -/
inductive BRun (C : Nat → ImportC) (mem : Memory) (W : Win) (ld : Word → Option Word)
    (fm : Word → Option (Nat × List Reg)) (tab : BTab) : Store H → Frame → List LEv → Prop
  | stop (s : Store H) (f : Frame) : BRun C mem W ld fm tab s f []
  | ins {s s' : Store H} {f : Frame} {r : Word} {i : Silmaril.X86.Ext.Instr} {n : Nat}
      {code : List Instr} {evs : List LEv} :
      gval s f .rip = some (Val.i64 r) → fm r = none → lookupB tab r = some (.x i, n) →
      emitB W r i n = some code → exec s f [] code = some (s', f, []) →
      BRun C mem W ld fm tab s' f evs → BRun C mem W ld fm tab s f evs
  | jmpInd {s : Store H} {f : Frame} {r v : Word} {d : BitVec 32} {n : Nat} {evs : List LEv} :
      gval s f .rip = some (Val.i64 r) → fm r = none → lookupB tab r = some (.jmpInd d, n) →
      ld (r + BitVec.ofNat 64 n + d.signExtend 64) = some v →
      BRun C mem W ld fm tab (upd s f .rip (Val.i64 v)) f evs → BRun C mem W ld fm tab s f evs
  | ext {s s' : Store H} {f : Frame} {r v : Word} {k : Nat} {regs : List Reg} {args : List Word}
      {o : List Obs} {ws : Reg → Word} {rc : List Instr} {evs : List LEv} :
      gval s f .rip = some (Val.i64 r) → fm r = some (k, regs) → regArgs s f regs = some args →
      C k mem args o (some v) → emitM W .ret 1 = some rc →
      exec (extStore0 s f v ws) f [] rc = some (s', f, []) →
      BRun C mem W ld fm tab s' f evs →
      BRun C mem W ld fm tab s f (.ext k args o (some v) :: evs)
  | halt {s : Store H} {f : Frame} {r : Word} {k : Nat} {regs : List Reg} {args : List Word}
      {o : List Obs} :
      gval s f .rip = some (Val.i64 r) → fm r = some (k, regs) → regArgs s f regs = some args →
      C k mem args o none → BRun C mem W ld fm tab s f [.ext k args o none]

/-- The observable traces of dispatcher runs (prefix-closed). -/
def blinkObs (C : Nat → ImportC) (mem : Memory) (W : Win) (ld : Word → Option Word)
    (fm : Word → Option (Nat × List Reg)) (tab : BTab) (s : Store H) (f : Frame) :
    List Obs → Prop :=
  fun o => ∃ evs, BRun C mem W ld fm tab s f evs ∧ o <+: levsObs mem evs

/-! ## The glibc hello -/

/-- `GOT[puts]` after eager binding: the foreign address of import 0 (`glibcrun.wat`). -/
def putsF : Word := 0x7f0000000000#64

/-- The start-up contract's return address for `main` (`glibcrun.wat`'s `MAINRET`). -/
def mainRet : Word := 0x7f0000000ff0#64

/-- The GOT slot of `puts`. -/
def gotPuts : Word := 0x404000#64

/-- The foreign addresses: `puts` (System V arguments) and `exit(rax)`. -/
def ghelloFm (r : Word) : Option (Nat × List Reg) :=
  if r = putsF then some (0, sysvArgs) else if r = mainRet then some (1, [.rax]) else none

/-- `puts@plt` at `0x401040`: `endbr64; jmp *0x2fb6(%rip)`. -/
def pltBytes : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0xb6, 0x2f, 0x00, 0x00]

/-- `main` at `0x401050`. -/
def mainBytes : List Byte :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8d, 0x3d, 0xa5, 0x0f, 0x00, 0x00,
   0xe8, 0xdc, 0xff, 0xff, 0xff, 0x31, 0xc0, 0x48, 0x83, 0xc4, 0x08, 0xc3]

/-- The code table of `puts@plt` and `main`. -/
def ghelloTab : BTab :=
  [(0x401040#64, .x .endbr64, 4), (0x401044#64, .jmpInd 0x2fb6#32, 6),
   (0x401050#64, .x .endbr64, 4), (0x401054#64, .x (.aluI8 .q .sub (.reg .rsp) 8#8), 4),
   (0x401058#64, .x (.lea .q .rdi (Silmaril.X86.Ext.Mem.ofRip 0xfa5#32)), 7),
   (0x40105f#64, .x (.call 0xffffffdc#32), 5), (0x401064#64, .x (.alu .d .xor (.reg .rax) .rax), 2),
   (0x401066#64, .x (.aluI8 .q .add (.reg .rsp) 8#8), 4), (0x40106a#64, .x .ret, 1)]

/-- The table is the bytes: every `Ext` entry fetches and decodes from `mem` at its address;
the `jmp *` entry's bytes are in `mem` and `Ext9.decodeNew` reads them as
`jmp *[rip + d]`. -/
def TabAt (mem : Memory) (tab : BTab) : Prop :=
  ∀ e ∈ tab, match e.2.1 with
    | .x i => Silmaril.X86.Ext.fetch mem e.1.toNat = .decoded i e.2.2
    | .jmpInd d => ∃ bs, mem.fetchBytes e.1.toNat e.2.2 = some bs ∧
        Silmaril.X86.Ext9.decodeNew bs =
          some (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip d)), e.2.2)

end Silmaril.Sim.GlibcBridge
