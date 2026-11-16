module

public import Silmaril.Sim.X86.G.Thms
public import Silmaril.Sim.X86.Max.Defs
public import Silmaril.Machine.X86.FnContract.Defs
public import Silmaril.X86.CallingConvention

/-!
# The System V call wrapper over a Wasm simulator: definitions

The System V wrapper of `docs/projects/wasm-sim-abi.md` (implemented for every simulator in
`examples/wasm-sim/proc/wat/sysv.wat`) calls an x86-64 function on a
simulator: it places the arguments as the System V ABI says, runs the function to the sentinel
return address and checks the callee-saved registers. Here it is defined for the proved G
simulator (`Silmaril.Sim.X86.G`) and its fragment (straight-line register code followed
by `ret`).

**Descriptor** (`SysVCall`, serialization `SysVCall.encode`/`decode`): little-endian `u64`
words `target, nint, int_args[6], nstack, stack_args[nstack]`, then the result area
`rax, rdx, status` (zero in a request), exactly the layout read by `sysv.wat`. Integer
arguments beyond `nint` are zero (`regArgs`).

**x86 side** (`setup`): from a caller state `m` with stack pointer `R`, let
`S = alignDown16 (R - 8 n)` (`n` stack arguments). The stack arguments are pushed in reverse
from `S + 8 n` (so `stack_args[j]` is at `S + 8 j`), then the sentinel `SENTINEL`
(`0xFFFF_FFFF_FFFF_F000`) is pushed: the entry stack pointer is `E = S - 8` (`entrySp`), which
is `≡ 8 (mod 16)`. The integer arguments go to `Silmaril.X86.sysv64.intArgRegs` (rdi rsi rdx rcx r8 r9), and
`rip := target`. Everything else is the caller's.

**Wasm side** (`wrapperCode n code`): the wrapper's code around the simulator code `code` of the
function body (P-inline, `Silmaril.Sim.X86.G.emitProg`), in a frame whose locals are
`0..5` the six register arguments, `6` the target, `7..12` the saved rbx rbp r12 r13 r14 r15,
`13` the saved entry stack pointer, `14` scratch (`ArgLocals`):
* `prologue n`: `rsp := E` computed from the `rsp` global as above, the argument registers and
  `rip` from the locals, then the callee-saved registers and `E` saved in locals 7..13;
* `code`: the function body;
* `epilogue`: pushes `rax`, then the **status word** (`statusOf`): bit 1 iff `rsp ≠ E` and bit
  `2 + j` iff callee-saved register `j` changed, each bit computed branch-free as
  `nz (x xor saved) << k` with `nz v = (v | (0 - v)) >>u 63`. These are the status bits of
  `sysv.wat` (its bit 0, "did not return to the sentinel", cannot occur here: in the fragment the
  final `ret` is structural and returns to the sentinel exactly when `rsp = E`).

The memory part of the setup (stack arguments, sentinel) is not on the Wasm side: the G
simulator has no memory. It is the x86 `setup`; the wrapper over a simulator with `mem.*` imports
performs it with `mem.store64` (`sysv.wat`).

**Problems**: `XGoal` (x86: the set-up state meets `AbiEntry` and returns, first return to the
sentinel on the `Silmaril.X86.Ext` machine, meeting `AbiReturn` with a postcondition on `rax`)
and `WGoal` (Wasm: every run of the wrapper code from a store holding any registers and a frame
holding the arguments ends normally with `[rax, status]`, `status = 0` and the postcondition).
`Silmaril.Proofs.Sim.SysV.Sound` proves `wrapper_sound` and the reduction `WGoal → XGoal`.

`sysvMaxModule`: the wrapper around `max` as a quoted WAT module (`wat3!`); its function body is
`wrapperCode 0 maxCode` (checked by `rfl`).
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Sim.X86.G
open Silmaril.Machine.X86.FnContract (AbiEntry AbiReturn)

/-! ## Descriptors -/

/-- The sentinel return address. -/
def SENTINEL : Word := 0xFFFFFFFFFFFFF000#64

/-- A call: target address, integer register arguments (at most six), stack arguments. -/
structure SysVCall where
  target : Word
  intArgs : List Word
  stackArgs : List Word
  deriving DecidableEq, Repr

namespace SysVCall

/-- Well-formed descriptors: at most six register arguments, and `8 n` fits easily. -/
def Valid (d : SysVCall) : Prop := d.intArgs.length ≤ 6 ∧ d.stackArgs.length < 2 ^ 32

/-- The six argument-register values: the integer arguments, zero beyond `nint`. -/
def regArgs (d : SysVCall) : List Word := d.intArgs ++ List.replicate (6 - d.intArgs.length) 0

/-- The descriptor as words, with the (zeroed) result area. -/
def words (d : SysVCall) : List Word :=
  d.target :: BitVec.ofNat 64 d.intArgs.length :: d.regArgs ++
    BitVec.ofNat 64 d.stackArgs.length :: d.stackArgs ++ [0, 0, 0]

/-- **Serialization**: each word little-endian. -/
def encode (d : SysVCall) : List Byte := d.words.flatMap fun w => encodeWords [w]

/-- Byte offset of the result area (`rax`, then `rdx`, then `status`). -/
def resultOffset (d : SysVCall) : Nat := 8 * (9 + d.stackArgs.length)

end SysVCall

/-- Bytes to little-endian words (`none` unless the length is a multiple of 8). -/
def decodeWords : List Byte → Option (List Word)
  | [] => some []
  | b₀ :: b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: b₆ :: b₇ :: rest => do
    let w ← Silmaril.X86.wordOfBytes? [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇]
    let ws ← decodeWords rest
    pure (w :: ws)
  | _ => none

/-- Words to a descriptor (`none` if `nint > 6` or the lengths do not match). -/
def ofWords : List Word → Option SysVCall
  | t :: k :: rest =>
    if k.toNat ≤ 6 then
      match rest.drop 6 with
      | ns :: tail =>
        if tail.length = ns.toNat + 3 then some ⟨t, (rest.take 6).take k.toNat, tail.take ns.toNat⟩
        else none
      | [] => none
    else none
  | _ => none

/-- **Deserialization.** -/
def SysVCall.decode (bs : List Byte) : Option SysVCall := (decodeWords bs).bind ofWords

/-! ## The x86 side: entry state -/

/-- Round down to a multiple of 16. -/
def alignDown16 (x : Word) : Word := x - (x &&& 15#64)

/-- The entry stack pointer for `n` stack arguments and caller stack pointer `rsp`. -/
def entrySp (n : Nat) (rsp : Word) : Word := alignDown16 (rsp - BitVec.ofNat 64 (8 * n)) - 8#64

/-- Write values to registers, pairwise. -/
def setArgs : List Word → List Reg → State → State
  | a :: as, r :: rs, σ => setArgs as rs (σ.write r a)
  | _, _, σ => σ

/-- Push words in order. -/
def pushAll : List Word → State → Memory → Option (State × Memory)
  | [], σ, m => some (σ, m)
  | v :: vs, σ, m => (Silmaril.X86.pushWord σ m v).bind fun r => pushAll vs r.1 r.2

/-- **The entry state** of a call from the caller state `m`: stack arguments and the sentinel
pushed below the 16-byte aligned `S`, register arguments, `rip := target`. `none` if a push is
not permitted. -/
def setup (d : SysVCall) (m : MState) : Option MState :=
  let n := d.stackArgs.length
  let S := alignDown16 (m.core.read .rsp - BitVec.ofNat 64 (8 * n))
  (pushAll d.stackArgs.reverse (m.core.write .rsp (S + BitVec.ofNat 64 (8 * n))) m.memory).bind
    fun r => (Silmaril.X86.pushWord r.1 r.2 SENTINEL).map fun r' =>
      ⟨{ setArgs d.regArgs Silmaril.X86.sysv64.intArgRegs r'.1 with rip := d.target }, r'.2⟩

/-- The registers and `rip` of the entry state, as a function of the caller's core. -/
def entryCore (d : SysVCall) (σ : State) : State :=
  { setArgs d.regArgs Silmaril.X86.sysv64.intArgRegs (σ.write .rsp (entrySp d.stackArgs.length (σ.read .rsp))) with
    rip := d.target }

/-! ## The Wasm side: the wrapper code over the G simulator -/

/-- Local index `i`. -/
def lidx (i : Fin 16) : LocalIdx := ⟨⟨i.val, by have := i.isLt; omega⟩⟩
/-- `local.get i`. -/
def lget (i : Fin 16) : Instr := .localGet (lidx i)
/-- `local.set i`. -/
def lset (i : Fin 16) : Instr := .localSet (lidx i)
/-- `local.tee i`. -/
def ltee (i : Fin 16) : Instr := .localTee (lidx i)

/-- `rsp := entrySp n rsp` (local 14 is scratch). -/
def spCode (n : Nat) : List Instr :=
  [gget (.reg .rsp), c64 (BitVec.ofNat 64 (8 * n)), b64op .sub, ltee 14, lget 14, c64 15#64,
    b64op .and, b64op .sub, c64 8#64, b64op .sub, gset (.reg .rsp)]

/-- The argument registers from locals 0..5, `rip` from local 6. -/
def argsCode : List Instr :=
  [lget 0, gset (.reg .rdi), lget 1, gset (.reg .rsi), lget 2, gset (.reg .rdx),
    lget 3, gset (.reg .rcx), lget 4, gset (.reg .r8), lget 5, gset (.reg .r9),
    lget 6, gset .rip]

/-- Save rbx rbp r12 r13 r14 r15 and rsp in locals 7..13. -/
def saveCode : List Instr :=
  [gget (.reg .rbx), lset 7, gget (.reg .rbp), lset 8, gget (.reg .r12), lset 9,
    gget (.reg .r13), lset 10, gget (.reg .r14), lset 11, gget (.reg .r15), lset 12,
    gget (.reg .rsp), lset 13]

/-- The wrapper's prologue. -/
def prologue (n : Nat) : List Instr := spCode n ++ argsCode ++ saveCode

/-- `nz` of `e`: `(e | (0 - e)) >>u 63`, i.e. `1` iff `e ≠ 0`. -/
def nzCode (e : List Instr) : List Instr := msbCode (e ++ [c64 0] ++ e ++ [b64op .sub, b64op .or])

/-- Or the bit `nz (l xor local i) << k` into the status on the stack. -/
def chkCode (l : Loc) (i : Fin 16) (k : BitVec 64) : List Instr :=
  nzCode [gget l, lget i, b64op .xor] ++ [c64 k, b64op .shl, b64op .or]

/-- The status word: bit 1 `rsp`, bits 2..7 rbx rbp r12 r13 r14 r15. -/
def statusCode : List Instr :=
  [c64 0] ++ chkCode (.reg .rsp) 13 1 ++ chkCode (.reg .rbx) 7 2 ++ chkCode (.reg .rbp) 8 3 ++
    chkCode (.reg .r12) 9 4 ++ chkCode (.reg .r13) 10 5 ++ chkCode (.reg .r14) 11 6 ++
    chkCode (.reg .r15) 12 7

/-- The wrapper's epilogue: `rax`, then the status word. -/
def epilogue : List Instr := [gget (.reg .rax)] ++ statusCode

/-- **The wrapper code** around the simulator code of a function body. -/
def wrapperCode (n : Nat) (code : List Instr) : List Instr := prologue n ++ code ++ epilogue

/-- `1` iff `x ≠ 0`. -/
def nz (x : BitVec 64) : BitVec 64 := (x ||| (0 - x)) >>> 63

/-- The status word the epilogue computes from the entry registers `e` and the final ones `f`. -/
def statusOf (e f : Reg → Word) : BitVec 64 :=
  (0 : BitVec 64) ||| nz (f .rsp ^^^ e .rsp) <<< 1 ||| nz (f .rbx ^^^ e .rbx) <<< 2 ||| nz (f .rbp ^^^ e .rbp) <<< 3 |||
    nz (f .r12 ^^^ e .r12) <<< 4 ||| nz (f .r13 ^^^ e .r13) <<< 5 ||| nz (f .r14 ^^^ e .r14) <<< 6 |||
    nz (f .r15 ^^^ e .r15) <<< 7

/-- The frame holds the call's arguments: 15 locals, `0..5` the register arguments, `6` the
target (the parameters of the wrapper function), the others any value. -/
def ArgLocals (f : Frame) (d : SysVCall) : Prop :=
  f.locals.length = 15 ∧
    (∀ i : Fin 6, f.locals[i.val]? = some (some (Val.i64 (d.regArgs.getD i.val 0)))) ∧
    f.locals[6]? = some (some (Val.i64 d.target)) ∧ ∀ i < 15, ∃ v, f.locals[i]? = some (some v)

/-! ## The problems -/

/-- **The x86 problem** of a function with body `p` (then `ret`) and `n` stack arguments:
for every descriptor meeting `Pre` and every caller state, if the entry state can be set up, its
return-address slot is readable and the code is in place, and the body retires, then the entry
state meets `AbiEntry`, and the function returns to the sentinel (`Ext.Returns`: the first `ret`
to it) in a state meeting `AbiReturn` whose `rax` meets `Post`. -/
def XGoal (p : XProg) (n : Nat) (Pre : SysVCall → Prop) (Post : SysVCall → Word → Prop) : Prop :=
  ∀ (d : SysVCall) (m e : MState), d.Valid → d.stackArgs.length = n → Pre d →
    setup d m = some e → m.memory.Permitted .read (entrySp n (m.core.read .rsp)).toNat 8 →
    CodeAt e.memory d.target (p ++ [(.ret, 1)]) →
    (∃ σ' m', runExt p e.core e.memory = some (σ', m')) →
    AbiEntry e.core e.memory ∧ ∃ final : MState, Silmaril.X86.Ext.Returns SENTINEL e final ∧
      AbiReturn e.core e.memory final.core ∧ Post d (final.core.read .rax)

/-- **The Wasm problem**: from every store holding registers (any values) and a frame holding a
descriptor meeting `Pre`, every run of the wrapper code that stops ends normally with the values
`[rax, status]`, `status = 0` and `Post d rax`. It mentions no x86 state. -/
def WGoal {H : Type} (P : Profile) (host : HostSemantics H) (code : List Instr) (n : Nat)
    (Pre : SysVCall → Prop) (Post : SysVCall → Word → Prop) : Prop :=
  ∀ (s : Store H) (f : Frame) (R : Reg → Word) (d : SysVCall), d.Valid → d.stackArgs.length = n →
    Pre d → GRegs s f R → ArgLocals f d →
    Silmaril.Wasm.Logic.Hoare.HWP P host s f (expression (wrapperCode n code)) fun _ _ o =>
      ∃ r st : Word, o = .normal [Val.i64 r, Val.i64 st] ∧ st = 0 ∧ Post d r

/-! ## Open tasks: stack arguments -/

/-- **Task (wrapper side)**: the set-up entry state holds stack argument `j` at
`[rsp + 8 + 8 j]` (the System V `stackOffset = 8 j`, `Abi.Argument.stackOffset`), when the
slots were readable in the caller's memory and the stack does not wrap. -/
def Task.stackArgPlaced : Prop :=
  ∀ (d : SysVCall) (m e : MState) (j : Nat) (hj : j < d.stackArgs.length), d.Valid →
    setup d m = some e →
    8 * (d.stackArgs.length + 2) + 16 ≤ (m.core.read .rsp).toNat →
    m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp) + 8#64).toNat
      (8 * d.stackArgs.length) →
    e.memory.readBytes (e.core.read .rsp + 8#64 + BitVec.ofNat 64 (8 * j)).toNat 8 =
      some (encodeWords [d.stackArgs[j]])

/-- The Wasm memory 0 of the instance holds the little-endian word `v` at address `a`. -/
def WMemAt {H : Type} (s : Store H) (f : Frame) (a : Nat) (v : Word) : Prop :=
  ∃ ma mi, s.mem? f ⟨0⟩ = some (ma, mi) ∧ Memory.load mi.bytes a 8 = some v

/-- **Task (simulator side, the G fragment)**: a method for the stack load
`mov d, [rsp + disp]` (`Ext.Instr.load .q d ⟨rsp, -, disp⟩`) reading the Wasm memory, sound
for `Ext.exec` wherever the Wasm memory agrees with the x86 memory at the loaded address
(identity mapping). With `Task.stackArgPlaced` and a store whose memory mirrors the stack, the
G fragment reads stack arguments, and `wrapper_sound`/`xgoal_of_wgoal` extend unchanged (`emitCore` gains
one case; `runExt_progress` holds where the loads are permitted). -/
def Task.gStackLoad : Prop :=
  ∃ ldCode : Reg → BitVec 32 → List Instr,
    ∀ (H : Type) (s : Store H) (f : Frame) (σ σ' : State) (mem : Silmaril.Process.Memory)
      (d : Reg) (disp : BitVec 32) (len : Nat),
      Enc s f σ →
      (∀ v, Silmaril.X86.Ext.loadN mem (σ.read .rsp + disp.signExtend 64) 8 = some v →
        WMemAt s f (σ.read .rsp + disp.signExtend 64).toNat v) →
      Silmaril.X86.Ext.exec (.load .q d ⟨.reg .rsp, none, disp, fun _ => rfl⟩) σ mem len = .ok σ' mem →
      ∃ s', exec s f [] (ldCode d disp) = some (s', f, []) ∧ Enc s' f { σ' with rip := σ.rip } ∧
        Frames s s' f

/-! ## The wrapper around `max` as a WAT module -/

/-- **The System V wrapper around `max`** (G simulator, P-inline), quoted WAT:
the 23 location globals of `Silmaril.Sim.X86.G.simModule` (same order, so the same global
indices), `sysv_call_max` (parameters: the six register arguments and the target; eight more
locals; results `rax`, `status`) whose body is `wrapperCode 0 maxCode` (checked by `rfl` in
`Silmaril.Proofs.Sim.SysV.Module`), and `sysv_call (desc : i32) -> i64`, the ABI entry point:
it reads a descriptor without stack arguments from memory (`SysVCall.encode` layout), calls
`sysv_call_max` and writes `rax`, `rdx`, `status` to the result area at offset 72
(executable; not verified). -/
def sysvMaxModule : Module := wat3! r#"
(module
  (global $rax (export "rax") (mut i64) (i64.const 0))
  (global $rcx (export "rcx") (mut i64) (i64.const 0))
  (global $rdx (export "rdx") (mut i64) (i64.const 0))
  (global $rbx (export "rbx") (mut i64) (i64.const 0))
  (global $rsp (export "rsp") (mut i64) (i64.const 0))
  (global $rbp (export "rbp") (mut i64) (i64.const 0))
  (global $rsi (export "rsi") (mut i64) (i64.const 0))
  (global $rdi (export "rdi") (mut i64) (i64.const 0))
  (global $r8 (export "r8") (mut i64) (i64.const 0))
  (global $r9 (export "r9") (mut i64) (i64.const 0))
  (global $r10 (export "r10") (mut i64) (i64.const 0))
  (global $r11 (export "r11") (mut i64) (i64.const 0))
  (global $r12 (export "r12") (mut i64) (i64.const 0))
  (global $r13 (export "r13") (mut i64) (i64.const 0))
  (global $r14 (export "r14") (mut i64) (i64.const 0))
  (global $r15 (export "r15") (mut i64) (i64.const 0))
  (global $rip (export "rip") (mut i64) (i64.const 0))
  (global $cf (export "cf") (mut i64) (i64.const 0))
  (global $pf (export "pf") (mut i64) (i64.const 0))
  (global $af (export "af") (mut i64) (i64.const 0))
  (global $zf (export "zf") (mut i64) (i64.const 0))
  (global $sf (export "sf") (mut i64) (i64.const 0))
  (global $of (export "of") (mut i64) (i64.const 0))
  (memory (export "memory") 1)
  (func $sysv_call_max (export "sysv_call_max")
    (param $a0 i64) (param $a1 i64) (param $a2 i64) (param $a3 i64) (param $a4 i64) (param $a5 i64)
    (param $target i64) (result i64 i64)
    (local i64 i64 i64 i64 i64 i64 i64 i64)
    global.get $rsp
    i64.const 0
    i64.sub
    local.tee 14
    local.get 14
    i64.const 15
    i64.and
    i64.sub
    i64.const 8
    i64.sub
    global.set $rsp
    local.get 0
    global.set $rdi
    local.get 1
    global.set $rsi
    local.get 2
    global.set $rdx
    local.get 3
    global.set $rcx
    local.get 4
    global.set $r8
    local.get 5
    global.set $r9
    local.get 6
    global.set $rip
    global.get $rbx
    local.set 7
    global.get $rbp
    local.set 8
    global.get $r12
    local.set 9
    global.get $r13
    local.set 10
    global.get $r14
    local.set 11
    global.get $r15
    local.set 12
    global.get $rsp
    local.set 13
    global.get $rdi
    global.set $rax
    global.get $rip
    i64.const 3
    i64.add
    global.set $rip
    global.get $rax
    i64.const -1
    i64.xor
    global.get $rsi
    i64.and
    global.get $rax
    global.get $rsi
    i64.xor
    i64.const -1
    i64.xor
    global.get $rax
    global.get $rsi
    i64.sub
    i64.and
    i64.or
    i64.const 63
    i64.shr_u
    global.set $cf
    global.get $rax
    global.get $rsi
    i64.xor
    global.get $rax
    global.get $rax
    global.get $rsi
    i64.sub
    i64.xor
    i64.and
    i64.const 63
    i64.shr_u
    global.set $of
    i64.const 1
    global.get $rax
    global.get $rsi
    i64.sub
    i64.const 0
    global.get $rax
    global.get $rsi
    i64.sub
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.xor
    global.set $zf
    global.get $rax
    global.get $rsi
    i64.sub
    i64.const 63
    i64.shr_u
    global.set $sf
    global.get $rip
    i64.const 3
    i64.add
    global.set $rip
    global.get $rax
    global.get $rax
    global.get $rsi
    i64.xor
    i64.const 0
    global.get $sf
    global.get $of
    i64.xor
    i64.sub
    i64.and
    i64.xor
    global.set $rax
    global.get $rip
    i64.const 4
    i64.add
    global.set $rip
    global.get $rax
    i64.const 0
    global.get $rsp
    local.get 13
    i64.xor
    i64.const 0
    global.get $rsp
    local.get 13
    i64.xor
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.const 1
    i64.shl
    i64.or
    global.get $rbx
    local.get 7
    i64.xor
    i64.const 0
    global.get $rbx
    local.get 7
    i64.xor
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.const 2
    i64.shl
    i64.or
    global.get $rbp
    local.get 8
    i64.xor
    i64.const 0
    global.get $rbp
    local.get 8
    i64.xor
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.const 3
    i64.shl
    i64.or
    global.get $r12
    local.get 9
    i64.xor
    i64.const 0
    global.get $r12
    local.get 9
    i64.xor
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.const 4
    i64.shl
    i64.or
    global.get $r13
    local.get 10
    i64.xor
    i64.const 0
    global.get $r13
    local.get 10
    i64.xor
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.const 5
    i64.shl
    i64.or
    global.get $r14
    local.get 11
    i64.xor
    i64.const 0
    global.get $r14
    local.get 11
    i64.xor
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.const 6
    i64.shl
    i64.or
    global.get $r15
    local.get 12
    i64.xor
    i64.const 0
    global.get $r15
    local.get 12
    i64.xor
    i64.sub
    i64.or
    i64.const 63
    i64.shr_u
    i64.const 7
    i64.shl
    i64.or)
  (func $sysv_call (export "sysv_call") (param $p i32) (result i64)
    (local $rax i64) (local $st i64)
    (call $sysv_call_max
      (i64.load offset=16 (local.get $p)) (i64.load offset=24 (local.get $p))
      (i64.load offset=32 (local.get $p)) (i64.load offset=40 (local.get $p))
      (i64.load offset=48 (local.get $p)) (i64.load offset=56 (local.get $p))
      (i64.load (local.get $p)))
    (local.set $st)
    (local.set $rax)
    (i64.store offset=72 (local.get $p) (local.get $rax))
    (i64.store offset=80 (local.get $p) (global.get $rdx))
    (i64.store offset=88 (local.get $p) (local.get $st))
    (local.get $rax)))
"#

/-! ## Glue conditions of the wrapper edge -/

/-- The body's precondition holds at every entry state. -/
def PreGlue (Pre : SysVCall → Prop) (BPre : (Reg → Word) → Prop) : Prop :=
  ∀ (d : SysVCall) (σ : State), Pre d → BPre (entryCore d σ).read

/-- The body's postcondition preserves `rsp` and the callee-saved registers and gives `Post`
of `rax`. -/
def PostGlue (Pre : SysVCall → Prop) (BPost : (Reg → Word) → (Reg → Word) → Prop)
    (Post : SysVCall → Word → Prop) : Prop :=
  ∀ (d : SysVCall) (σ : State) (R' : Reg → Word), Pre d → BPost (entryCore d σ).read R' →
    (R' .rsp = (entryCore d σ).read .rsp ∧ R' .rbx = (entryCore d σ).read .rbx ∧
      R' .rbp = (entryCore d σ).read .rbp ∧ R' .r12 = (entryCore d σ).read .r12 ∧
      R' .r13 = (entryCore d σ).read .r13 ∧ R' .r14 = (entryCore d σ).read .r14 ∧
      R' .r15 = (entryCore d σ).read .r15) ∧ Post d (R' .rax)

/-- The result is the signed maximum of the first two register arguments. -/
def MaxCallPost (d : SysVCall) (r : Word) : Prop :=
  r = if (d.regArgs.getD 0 0).slt (d.regArgs.getD 1 0) then d.regArgs.getD 1 0 else d.regArgs.getD 0 0

end Silmaril.Sim.SysV
