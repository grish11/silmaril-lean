module

public import Silmaril.Sim.WasiBridge.G.Thms
public import Silmaril.Libc.Puts.Defs

/-!
# glibc functions as Wasm imports: linked runs relative to import contracts (header)

runtime `examples/wasm-sim/glibc-bridge`. A dynamically
linked program's calls into glibc become **foreign calls**: the simulator calls an import
(`ext.call`, System V by value) instead of running glibc's code. Each import has a contract;
the linked whole is analysed *relative to* the contracts (assume-guarantee), and a contract is
discharged separately — by a Wasm implementation (route (a), e.g. `glibc.wat`'s WASI-backed
`puts`) or by glibc's own x86 code run in the simulator (route (b)).

* `ImportC`: a contract — process memory at the call, the argument registers, the observables
  the call emits, and its return value (`none`: it does not return, e.g. `exit`). The callee
  leaves the process memory unchanged (enough for `puts`/`exit`; `memcpy`-like imports need a
  memory effect, not modelled here).
* `cstr mem p`: the C string at `p` (at most 65536 bytes, as `glibc.wat` reads it).
* **`putsC`**: the `puts` spec `Silmaril.Libc.putsGlibc` (glibc 2.39's return value),
  on bytes: the call emits the bytes `w` on fd 1 and returns `r` in `eax`. `putsC1`: moreover
  `w ≠ []` (every `puts` whose output reaches a `sys2wasi`/WASI `fd_write`, which delivers at
  least one byte). `exitC`: emits `exit (rdi & 255)` and does not return.
* Items `LItem`: G instructions, `syscall`, and **`ext k regs len`**, a call of import `k`
  with the argument registers `regs`, replacing a `call f@plt` (+ the PLT stub and the
  callee's `ret`) of length `len`. Its effect is the System V call boundary (`Silmaril.Sim.SysV`):
  `rax :=` the result, the caller-saved scratch registers `rcx rdx rsi rdi r8–r11` and the
  flags arbitrary (`ws`, undefined flags), callee-saved registers and `rsp` kept, `rip += len`.
* **`LRun C Ans mem`**: interaction runs of the simulator code of the items, syscalls answered
  by `Ans` (WasiBridge's `WRun`), import `k` answered by its contract `C k`. Observables
  `levsObs`; `linkObs`: the prefix-closed observable traces of the linked program.
* `Meets I C` (implementation `I` meets contract `C`), `extCode`: the Wasm method of `ext`.
* glibc hello: `ghelloItems` — `main` of `progs/hello.c` (`puts("Hello, world!"); return 0`)
  after the start-up contract (`__libc_start_main = exit ∘ main`):
  `mov rdi, msg; call puts@plt; xor eax, eax; ret ⇒ exit(rax)`. `putsImpl`: the behaviour of
  `glibc.wat`'s `puts` (one `fd_write` of `s ++ "\n"` answered `k`; result `|s| + 1` or `EOF`).
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Sim.X86.G
open Silmaril.Sim.WasiBridge
open Silmaril.Sim.WasiBridge.G

variable {H : Type}

/-! ## Contracts -/

/-- An import contract: memory, arguments, emitted observables, return value. -/
abbrev ImportC := Memory → List Word → List Obs → Option Word → Prop

/-- `I` meets `C`. -/
def Meets (I C : ImportC) : Prop := ∀ mem args o r, I mem args o r → C mem args o r

/-- A C string (fuel-bounded). -/
def cstrAux (rd : Word → Option Byte) (p : Word) : Nat → Option (List Byte)
  | 0 => none
  | n + 1 => match rd p with
    | none => none
    | some b => if b = 0 then some [] else (cstrAux rd (p + 1) n).map (b :: ·)

/-- The C string at `p` (readable bytes up to a `NUL`, at most 65536). -/
def cstr (mem : Memory) (p : Word) : Option (List Byte) := cstrAux (viewByte mem .read) p 65536

/-- Bytes as a `CStr` (one `Char` per byte). -/
def toChars (l : List Byte) : Silmaril.Libc.CStr := l.map fun b => Char.ofNat b.toNat

/-- `eax` holds the `int` `r`. -/
def RetInt (v : Word) (r : Int) : Prop := v.setWidth 32 = BitVec.ofInt 32 r

/-- **The `puts` contract**: `Silmaril.Libc.putsGlibc` on the bytes of the string at `rdi`,
the written bytes `w` observed on fd 1, the result in `eax`. -/
def putsC : ImportC := fun mem args o ret =>
  ∃ p s w r v, args.head? = some p ∧ cstr mem p = some s ∧
    Silmaril.Libc.putsGlibc (toChars s) (toChars w) r ∧ o = w.map (.wr 1) ∧ ret = some v ∧
    RetInt v r

/-- `putsC` with a non-empty output. -/
def putsC1 : ImportC := fun mem args o ret => putsC mem args o ret ∧ o ≠ []

/-- The `exit` contract: `exit (a & 255)`, no return. -/
def exitC : ImportC := fun _ args o ret =>
  ∃ a, args.head? = some a ∧ o = [.exit (a &&& 255).toNat] ∧ ret = none

/-! ## Linked programs -/

/-- A program item: a G instruction, `syscall`, or a call of import `k`. -/
inductive LItem where
  | ins (i : Silmaril.X86.Ext.Instr) (len : Nat)
  | sys
  | ext (k : Nat) (regs : List Reg) (len : Nat)

/-- The System V integer argument registers. -/
def sysvArgs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- The caller-saved registers an import may clobber (besides `rax`). -/
def scratch : List Reg := [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- The values of registers. -/
def regArgs (s : Store H) (f : Frame) (regs : List Reg) : Option (List Word) :=
  regs.mapM fun r => match gval s f (.reg r) with
    | some (.num ⟨.int .i64, v⟩) => some v
    | _ => none

/-- Register updates, in order. -/
def updRegs (s : Store H) (f : Frame) : List (Reg × Word) → Store H
  | [] => s
  | (r, v) :: l => updRegs (upd s f (.reg r) (Val.i64 v)) f l

/-- The store after an import returned `v`, scratch registers `ws`, `rip = r` before. -/
def extStore (s : Store H) (f : Frame) (r v : Word) (ws : Reg → Word) (len : Nat) : Store H :=
  upd (updRegs (upd s f (.reg .rax) (Val.i64 v)) f (scratch.map fun q => (q, ws q))) f .rip
    (Val.i64 (r + BitVec.ofNat 64 len))

/-- An event of a linked run. -/
inductive LEv where
  | sys (e : HostEv)
  | ext (k : Nat) (args : List Word) (o : List Obs) (ret : Option Word)

/-- Its observables. -/
def LEv.obs (mem : Memory) : LEv → List Obs
  | .sys e => (liftEv mem e).flatMap sysObs
  | .ext _ _ o _ => o

/-- The observables of a run. -/
def levsObs (mem : Memory) (evs : List LEv) : List Obs := evs.flatMap (LEv.obs mem)

/-- **Linked runs**: the simulator code of the items, syscalls answered by `Ans`, import `k` by
its contract `C k`. -/
inductive LRun (C : Nat → ImportC) (Ans : List Word → Word → Prop) (mem : Memory) :
    Store H → Frame → List LItem → List LEv → List LItem → Prop
  | stop (s : Store H) (f : Frame) (p : List LItem) : LRun C Ans mem s f p [] p
  | ins {s s' : Store H} {f : Frame} {i : Silmaril.X86.Ext.Instr} {n : Nat} {code : List Instr}
      {p rest : List LItem} {evs : List LEv} :
      emit i n = some code → exec s f [] code = some (s', f, []) → LRun C Ans mem s' f p evs rest →
      LRun C Ans mem s f (.ins i n :: p) evs rest
  | sys {s : Store H} {f : Frame} {args : List Word} {r v w : Word} {p rest : List LItem}
      {evs : List LEv} :
      sysArgs s f = some args → gval s f .rip = some (Val.i64 r) → Ans args v →
      LRun C Ans mem (sysStore s f r v w) f p evs rest →
      LRun C Ans mem s f (.sys :: p) (.sys ⟨args, some v⟩ :: evs) rest
  | pending {s : Store H} {f : Frame} {args : List Word} {p : List LItem} :
      sysArgs s f = some args → LRun C Ans mem s f (.sys :: p) [.sys ⟨args, none⟩] (.sys :: p)
  | ext {s : Store H} {f : Frame} {k : Nat} {regs : List Reg} {len : Nat} {args : List Word}
      {o : List Obs} {r v : Word} {ws : Reg → Word} {p rest : List LItem} {evs : List LEv} :
      regArgs s f regs = some args → gval s f .rip = some (Val.i64 r) → C k mem args o (some v) →
      LRun C Ans mem (extStore s f r v ws len) f p evs rest →
      LRun C Ans mem s f (.ext k regs len :: p) (.ext k args o (some v) :: evs) rest
  | halt {s : Store H} {f : Frame} {k : Nat} {regs : List Reg} {len : Nat} {args : List Word}
      {o : List Obs} {p : List LItem} :
      regArgs s f regs = some args → C k mem args o none →
      LRun C Ans mem s f (.ext k regs len :: p) [.ext k args o none] (.ext k regs len :: p)

/-- The observable traces of a linked program (prefix-closed). -/
def linkObs (C : Nat → ImportC) (Ans : List Word → Word → Prop) (mem : Memory) (s : Store H)
    (f : Frame) (items : List LItem) : List Obs → Prop :=
  fun o => ∃ evs rest, LRun C Ans mem s f items evs rest ∧ o <+: levsObs mem evs

/-- **The method of `ext`**: the argument registers, `call ext.call`, `rax :=` the result,
each scratch register `:= nd.undef(i)`, `rip += len` (flags: left as they are, which the
abstraction reads as undefined). -/
def extCode (ex ux : FuncIdx) (regs : List Reg) (len : Nat) : List Instr :=
  regs.map (fun r => gget (.reg r)) ++ [.call ex, gset (.reg .rax)] ++
    scratch.flatMap (fun q => [.intConst .i32 (BitVec.ofNat 32 q.toBitVec.toNat), .call ux,
      gset (.reg q)]) ++ nextCode len

/-! ## glibc hello -/

/-- `"Hello, world!"` (the string `puts` gets). -/
def msgS : List Byte := helloMsg.take 13

/-- The two imports of the glibc hello: `0 = puts`, `1 = exit` (the start-up contract's
`exit(main(...))`). -/
def ghelloC (P : ImportC) : Nat → ImportC
  | 0 => P
  | _ => exitC

/-- `main` after the start-up contract: `mov rdi, msg; call puts@plt; xor eax, eax;
ret ⇒ exit(rax)`. -/
def ghelloItems : List LItem :=
  [.ins (.movabs .rdi msgAddr) 10, .ext 0 sysvArgs 5, .ins (.alu .d .xor (.reg .rax) .rax) 2,
   .ext 1 [.rax] 1]

/-- **`glibc.wat`'s `puts`**: one `fd_write(1, s ++ "\n")` answered `k` (`1 ≤ k`, as `S1Ans`);
the result is `|s| + 1` if it wrote everything, else `EOF`. -/
def putsImpl : ImportC := fun mem args o ret =>
  ∃ p s k v, args.head? = some p ∧ cstr mem p = some s ∧ 1 ≤ k ∧ k ≤ s.length + 1 ∧
    o = ((s ++ [10]).take k).map (.wr 1) ∧ ret = some v ∧
    RetInt v (if k = s.length + 1 then (s.length + 1 : Int) else -1)

end Silmaril.Sim.GlibcBridge
