module

public import Silmaril.Sim.WasiBridge.Defs
public import Silmaril.Sim.X86.G.Thms

/-!
# The G simulator with a `syscall` method, and hello world on it

Extends the proved G fragment (`Silmaril.Sim.X86.G`) by the System V `syscall` instruction,
whose method calls the opaque import `sys.syscall` (the environment) and `nd.undef` (for `r11`,
which Linux sets to RFLAGS, including flags G does not model):

```
rax := sys.syscall(rax, rdi, rsi, rdx, r10, r8, r9); rcx := rip + 2; r11 := nd.undef(11);
rip := rip + 2
```

* `sysCode sx ux`: the method body (`sx`, `ux` the function indices of the two imports).
* `Item`: a program item, a G instruction with its length or `syscall`; `ItemsAt` places a
  program in memory (G instructions decode; `syscall` is the bytes `0f 05`).
* **`WRun Ans s f items evs rest`**: the interaction semantics of the simulator code of `items`
  from the store `s`: G instructions evaluate (`exec`), and each `syscall` calls the environment
  with the seven argument registers and continues with an answer allowed by `Ans`, or stops at
  an unanswered call; `evs` lists the calls (`HostEv`), `rest` the items not executed.
  `Silmaril.Proofs.Sim.WasiBridge.G.Steps` shows that a `syscall` piece is the Wasm small-step
  semantics of `sysCode` with a host function answering by `Ans`.
* The process side: `lpsStep` (the user step of LPS's x86 machine: stuck at `0f 05`,
  `Silmaril.X86.Ext.stepOpt` elsewhere), `sysResume` (the core after a syscall, as
  `LpsBridge.resume` computes it), and **`EnvS1 E Ok`**: the environment answers `write`, `read`
  and `exit`/`exit_group` as LPS's proved arms do (`lpsEnv_S1`: `IoSpec.lpsEnv` meets it with
  `LpsOk`, the descriptor-to-channel binding of LPS's initial model).
* Observables: `liftEv mem` reads a call as a lifted syscall event (`write` delivers `wsrc`, the
  readable prefix of its buffer in the process memory `mem`), `evsObs`.
* `S1Ans mem`: the answers of the `sys2wasi` adapter to `write` (`1 ≤ k ≤ |wsrc|`); `exit` has
  no answer. `S1ReadAns`: its `read` answers, prepared for `cat`.
* **Hello**: `helloBytes`/`helloItems` (`examples/wasm-sim/wasi-bridge/progs/hello-g.S`:
  `mov rax,1; mov rdi,1; movabs rsi,0x402000; mov rdx,14; syscall; mov rax,60; mov rdi,0;
  syscall`), `helloMsg`, and the WASI program `helloWasi` (`progs/hello-wasi.wat`:
  `fd_write(1, [msg]) = ok k; proc_exit 0`).
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS (Event)
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Sim.X86.G

variable {H : Type}

/-! ## The `syscall` method -/

/-- The argument registers of a syscall, in `sys.syscall` order. -/
def sysRegs : List Reg := [.rax, .rdi, .rsi, .rdx, .r10, .r8, .r9]

/-- **The `syscall` method.** -/
def sysCode (sx ux : FuncIdx) : List Instr :=
  sysRegs.map (fun r => gget (.reg r)) ++ [.call sx, gset (.reg .rax),
    gget .rip, c64 2, b64op .add, gset (.reg .rcx),
    .intConst .i32 11, .call ux, gset (.reg .r11)] ++ nextCode 2

/-- A program item. -/
inductive Item where
  | ins (i : Silmaril.X86.Ext.Instr) (len : Nat)
  | sys

/-- The length of an item. -/
def Item.len : Item → Nat
  | .ins _ n => n
  | .sys => 2

/-- The bytes `0f 05` at `a`. -/
def SysAt (mem : Memory) (a : Word) : Prop := mem.fetchBytes a.toNat 2 = some [0x0f, 0x05]

/-- A program placed at `a`. -/
def ItemsAt (mem : Memory) : Word → List Item → Prop
  | _, [] => True
  | a, .ins i n :: p => Silmaril.X86.Ext.fetch mem a.toNat = .decoded i n ∧ ¬ SysAt mem a ∧
      ItemsAt mem (a + BitVec.ofNat 64 n) p
  | a, .sys :: p => SysAt mem a ∧ ItemsAt mem (a + 2) p

/-- The simulator code of a program (`none` if an instruction is not in the G fragment). -/
def emitItems (sx ux : FuncIdx) : List Item → Option (List Instr)
  | [] => some []
  | .ins i n :: p => do
    let c ← emit i n
    let cs ← emitItems sx ux p
    pure (c ++ cs)
  | .sys :: p => (emitItems sx ux p).map (sysCode sx ux ++ ·)

/-- The values of the argument registers. -/
def sysArgs (s : Store H) (f : Frame) : Option (List Word) :=
  sysRegs.mapM fun r => match gval s f (.reg r) with
    | some (.num ⟨.int .i64, v⟩) => some v
    | _ => none

/-- The store after a syscall answered `v`, `r11 := w`, with `rip = r` before. -/
def sysStore (s : Store H) (f : Frame) (r v w : Word) : Store H :=
  upd (upd (upd (upd s f (.reg .rax) (Val.i64 v)) f (.reg .rcx) (Val.i64 (r + 2)))
    f (.reg .r11) (Val.i64 w)) f .rip (Val.i64 (r + 2))

/-- A call of the environment: the argument values and the answer (`none`: unanswered). -/
structure HostEv where
  args : List Word
  ret : Option Word

/-- **Interaction runs of the simulator code**, with the environment answering by `Ans`. -/
inductive WRun (Ans : List Word → Word → Prop) :
    Store H → Frame → List Item → List HostEv → List Item → Prop
  | stop (s : Store H) (f : Frame) (p : List Item) : WRun Ans s f p [] p
  | ins {s s' : Store H} {f : Frame} {i : Silmaril.X86.Ext.Instr} {n : Nat} {code : List Instr}
      {p rest : List Item} {evs : List HostEv} :
      emit i n = some code → exec s f [] code = some (s', f, []) → WRun Ans s' f p evs rest →
      WRun Ans s f (.ins i n :: p) evs rest
  | sys {s : Store H} {f : Frame} {args : List Word} {r v w : Word} {p rest : List Item}
      {evs : List HostEv} :
      sysArgs s f = some args → gval s f .rip = some (Val.i64 r) → Ans args v →
      WRun Ans (sysStore s f r v w) f p evs rest →
      WRun Ans s f (.sys :: p) (⟨args, some v⟩ :: evs) rest
  | pending {s : Store H} {f : Frame} {args : List Word} {p : List Item} :
      sysArgs s f = some args → WRun Ans s f (.sys :: p) [⟨args, none⟩] (.sys :: p)

/-! ## The process side -/

/-- The user step of LPS's x86 machine: stuck at `syscall`, `Ext` elsewhere. -/
def lpsStep (m : MState) : Option MState :=
  if m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05] then none
  else Silmaril.X86.Ext.stepOpt 0 m

/-- The core after a syscall answered `ret`, at flag completion `ch` (`LpsBridge.resume`). -/
def sysResume (σ : State) (ch : X86FlagChoices.Choice) (ret : Word) : State :=
  let fl := X86FlagChoices.completeFlags σ.flags ch
  { ((σ.write .rax ret).write .rcx (σ.rip + 2)).write .r11 ((rflagsImage fl).getD 0) with
    rip := σ.rip + 2, flags := fl }

/-- The bytes a `write(fd, buf, n)` can deliver: LPS's `writeSource` (the readable prefix of the
buffer, at most `MAX_RW_COUNT`). -/
def wsrc (mem : Memory) (buf n : Word) : List Byte :=
  Silmaril.Process.LPS.writeSource (viewByte mem .read) buf n

/-- An environment's model binds every descriptor it knows to the channel with the same number
(true of LPS's initial model: `0, 1, 2 ↦ 0, 1, 2`). -/
def LpsOk (e : Silmaril.Process.LPS.Model) : Prop :=
  ∀ fd c, Silmaril.Process.LPS.fdLookup e.fds fd = some (.channel c) → c = fd

/-- `fd` is bound to the live channel `fd`. -/
def LpsChan (e : Silmaril.Process.LPS.Model) (fd : Word) : Prop :=
  Silmaril.Process.LPS.fdLookup e.fds fd = some (.channel fd) ∧ fd ≠ 0

/-- **The environment answers like LPS's proved arms** on models satisfying `Ok` (preserved):
`write` delivers a non-empty prefix `ds` of `wsrc` on the channel `fd32 rdi`, rax = |ds|, memory
unchanged; `read` (stdin) stores bytes `bs` (rax = |bs|) through a memory effect; `exit` and
`exit_group` halt with `rdi & 255`. Every `write` answer allowed by LPS's `writeArm`
preconditions is admitted (`Chan e fd`: `fd` is bound to the live channel `fd`), and so is
`exit`. -/
structure EnvS1 (E : SysEnv) (Ok : E.Model → Prop) (Chan : E.Model → Word → Prop) : Prop where
  answers : ∀ m e ch o, Ok e → AtSyscall m → E.arm (trapped ⟨m, none⟩ ch) e o →
    (m.core.read .rax = 1 ∧ ∃ (ds : List Byte) (e' : E.Model), Ok e' ∧ ds ≠ [] ∧
      ds <+: wsrc m.memory (m.core.read .rsi) (m.core.read .rdx) ∧
      o = .resume ⟨sysResume m.core ch (Silmaril.Process.LPS.lenWord ds), m.memory⟩ e'
        (ds.map (.writeEv (Silmaril.Process.LPS.fd32 (m.core.read .rdi))))) ∨
    (m.core.read .rax = 0 ∧ ∃ (bs : List Byte) (e' : E.Model) (eff : Silmaril.Process.LPS.SyscallEffect),
      Ok e' ∧ eff.ret = Silmaril.Process.LPS.lenWord bs ∧
      (eff = Silmaril.Process.LPS.mkEffect (Silmaril.Process.LPS.lenWord bs) [(m.core.read .rsi, bs)] [] ∨
        (bs = [] ∧ eff = Silmaril.Process.LPS.mkEffect 0 [] [])) ∧
      o = .resume ⟨sysResume m.core ch eff.ret, applyMemoryEffect m.memory eff⟩ e'
        (bs.map (.readEv (Silmaril.Process.LPS.fd32 (m.core.read .rdi))))) ∨
    ((m.core.read .rax = 60 ∨ m.core.read .rax = 231) ∧ ∃ fs,
      o = .halt [.exitEv (m.core.read .rdi &&& 255) fs])
  admitsWrite : ∀ m e ch (k : Nat), Ok e → AtSyscall m → m.core.read .rax = 1 →
    Chan e (Silmaril.Process.LPS.fd32 (m.core.read .rdi)) →
    Silmaril.Process.LPS.modeledRwRangeWith Silmaril.Process.LPS.accessOkb (m.core.read .rsi)
      (m.core.read .rdx) = true →
    m.core.read .rdx ≠ 0 → 1 ≤ k → k ≤ (wsrc m.memory (m.core.read .rsi) (m.core.read .rdx)).length →
    ∃ e', Ok e' ∧ E.arm (trapped ⟨m, none⟩ ch) e
      (.resume ⟨sysResume m.core ch (Silmaril.Process.LPS.lenWord
          ((wsrc m.memory (m.core.read .rsi) (m.core.read .rdx)).take k)), m.memory⟩ e'
        (((wsrc m.memory (m.core.read .rsi) (m.core.read .rdx)).take k).map
          (.writeEv (Silmaril.Process.LPS.fd32 (m.core.read .rdi)))))
  admitsExit : ∀ m e ch, Ok e → AtSyscall m → (m.core.read .rax = 60 ∨ m.core.read .rax = 231) →
    ∃ fs, E.arm (trapped ⟨m, none⟩ ch) e (.halt [.exitEv (m.core.read .rdi &&& 255) fs])

/-! ## Observables of simulator runs -/

/-- A call as a lifted syscall event (buffers read from the process memory `mem`). -/
def liftEv (mem : Memory) : HostEv → List SysEv
  | ⟨nr :: fd :: buf :: n :: _, some k⟩ =>
    if nr = 1 then [.write (Silmaril.Process.LPS.fd32 fd).toNat (wsrc mem buf n) k.toNat] else []
  | ⟨nr :: code :: _, none⟩ =>
    if nr = 60 ∨ nr = 231 then [.exit (code &&& 255).toNat] else []
  | _ => []

/-- The observables of a list of calls. -/
def evsObs (mem : Memory) (evs : List HostEv) : List Obs := (evs.flatMap (liftEv mem)).flatMap sysObs

/-- The answers of `sys2wasi` to `write`: a non-empty prefix of the deliverable bytes. -/
def S1Ans (mem : Memory) : List Word → Word → Prop
  | nr :: _ :: buf :: n :: _, v => nr = 1 ∧ 1 ≤ v.toNat ∧ v.toNat ≤ (wsrc mem buf n).length
  | _, _ => False

/-- **Prepared for `cat`**: the answers of `sys2wasi` to `read(fd, buf, n)` with the process
memory as the environment's state: `bs` (at most `n` bytes, the WASI `fd_read` result) stored
at `buf`, as LPS's `readArm` effect does. Interaction runs with reads need the memory in the
simulator's environment (`mem.*` imports). -/
def S1ReadAns (mem : Memory) : List Word → List Byte → Word → Memory → Prop
  | nr :: _ :: buf :: n :: _, bs, v, mem' => nr = 0 ∧ bs.length ≤ n.toNat ∧
      v = Silmaril.Process.LPS.lenWord bs ∧
      mem' = applyMemoryEffect mem (Silmaril.Process.LPS.mkEffect v [(buf, bs)] [])
  | _, _, _, _ => False

/-- The observable traces of the simulator code of `items` from `s`, with the environment
answering by `S1Ans mem`. -/
def wasmObs (mem : Memory) (s : Store H) (f : Frame) (items : List Item) : List Obs → Prop :=
  fun o => ∃ evs rest, WRun (S1Ans mem) s f items evs rest ∧ o = evsObs mem evs

/-! ## Hello -/

/-- The message. -/
def helloMsg : List Byte :=
  [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21, 0x0a]

/-- Its address. -/
def msgAddr : Word := 0x402000#64

/-- The program. -/
def helloItems : List Item :=
  [.ins (.movI .q (.reg .rax) 1) 7, .ins (.movI .q (.reg .rdi) 1) 7, .ins (.movabs .rsi msgAddr) 10,
   .ins (.movI .q (.reg .rdx) 14) 7, .sys, .ins (.movI .q (.reg .rax) 60) 7,
   .ins (.movI .q (.reg .rdi) 0) 7, .sys]

/-- Its bytes, one list per item. -/
def helloBytes : List (List Byte) :=
  [[0x48, 0xc7, 0xc0, 0x01, 0, 0, 0], [0x48, 0xc7, 0xc7, 0x01, 0, 0, 0],
   [0x48, 0xbe, 0x00, 0x20, 0x40, 0, 0, 0, 0, 0], [0x48, 0xc7, 0xc2, 0x0e, 0, 0, 0], [0x0f, 0x05],
   [0x48, 0xc7, 0xc0, 0x3c, 0, 0, 0], [0x48, 0xc7, 0xc7, 0, 0, 0, 0], [0x0f, 0x05]]

/-- The WASI hello: `fd_write(1, [msg])` answered `ok k` (`1 ≤ k ≤ 14`), then `proc_exit 0`. -/
def helloWasi : P1Sem :=
  ⟨fun t => ∃ k, 1 ≤ k ∧ k ≤ 14 ∧
    t <+: [.imp (Silmaril.Wasi.Versions.P1.fn "fd_write") [.u32 1, .record [Silmaril.Wasi.bytesV helloMsg]]
             (Silmaril.Wasi.Versions.P1.okAns (some (.u32 (BitVec.ofNat 32 k)))),
           .imp (Silmaril.Wasi.Versions.P1.fn "proc_exit") [.u32 0] none]⟩

end Silmaril.Sim.WasiBridge.G
