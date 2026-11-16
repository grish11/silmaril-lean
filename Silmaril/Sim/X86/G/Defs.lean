module

public import Silmaril.X86.Ext.Semantics
public import Silmaril.Wasm.Logic.Core.Defs
public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.X86.Ext.Machine

/-!
# A Wasm simulator for a register subset of x86-64 (globals representation G)

**What is proved.** The artefact verified here is a *certified translator*: `emit`, `emitX` and
`emitProg` map instructions of a register fragment of x86-64 to Wasm code over the location
globals, and `Silmaril.Sim.X86.G.Thms` proves that code sound against `Silmaril.X86.Ext.exec`.
It is not the runtime simulator `examples/wasm-sim/x86/x86-g.wat` (decoder, generic methods,
`step`/`run`), which is tested only. The ABI and the deviations of this Lean profile from it
are in `docs/projects/wasm-sim-abi.md`.

The simulator state is one mutable `i64` global per location, at the location numbers of the
wasm-sim ABI (`docs/projects/wasm-sim-abi.md`): globals `0..15` are the GPRs in hardware order,
`16` is RIP, `17` CF, `20` ZF, `21` SF, `22` OF. PF (`18`) and AF (`19`) exist in the module
but are **unmodelled**: no method writes them and the abstraction ignores them. Deviation from
the ABI: flags are `i64` globals holding `0`/`1` (not `i32`), so that every method is
straight-line `i64` code. `i32` flags would need `i64.extend_i32_u` for `cmov`, a conversion
that `Silmaril.Wasm.Logic.Core.exec1` (and so `wpc`) does not evaluate.

* `Loc`: the modelled locations; `Loc.idx` their global index.
* `gval s f l`: the value of the global of location `l` in store `s`, seen through the module
  instance of frame `f`.
* `Layout s f`: the module instance maps the modelled locations to distinct, existing global
  addresses.
* **`Enc s f σ`**: the store encodes the `Silmaril.X86.State` `σ` on the modelled locations.
  GPRs and RIP are exact; a flag holds `0` or `1`, which must be σ's value when σ defines the
  flag (`FlagValue.Admits`), and is arbitrary when σ leaves it undefined.
* **`emit i len`**: the Wasm code of the method for the decoded instruction `i`
  (`Silmaril.X86.Ext.Instr`) of byte length `len`: the instruction's register and flag effect
  (`emitCore`) followed by `rip += len` (the ABI's `i_next len`). Defined for
  `mov r64, r64`, `mov r/m64, imm32`, `movabs`, the 64-bit register `add`/`sub`/`and`/`or`/
  `xor`/`cmp`, and `cmovcc r64, r64` (all conditions but `p`/`np`, which read the unmodelled PF).
  Registers are fixed by the instruction: the Lean function `emit` generates one method per
  instruction instance (no `br_table` over register numbers; see "The Lean G profile" in `docs/projects/wasm-sim-abi.md`).
* `emitProg`: a straight-line x86 program (decoded instructions with lengths) translated to
  Wasm ("P-inline": the method bodies concatenated); `runExt` runs it on `Ext.exec`.
* `encStore σ`/`encFrame`: a concrete store encoding `σ`. `GRegs s f R`: the store holds the
  registers `R` (a Wasm-only condition). **`XProblem p Pre Post`** (the x86 problem on
  `runExt`) and **`WProblem P host code Pre Post`** (the Wasm problem on the register globals),
  related by `Silmaril.Sim.X86.G.xproblem_of_wproblem`.
* `CodeAt mem a p` / `BytesAt mem a bss`: code placement (decoded instructions, or byte spans,
  from address `a`), `endAddr a p` the address after it.
* `stateOf R w bc bz bs bo`: the x86 state a store holds; **`methodSpec fi a i`**: the
  `FSpec` of the method of `i` (proved by `method_valid`).
* `simModule`: the simulator for a few instruction instances as a `wat3!` quotation.

The flag formulas are silmaril's bit-level definitions (`addCarryN`, `subBorrowN`, ...)
transcribed to `i64` operations, with `msb v` computed as `v >>u 63`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State Flags AluOp)

/-! ## Locations -/

/-- The modelled locations. -/
inductive Loc where
  | reg (r : Reg)
  | rip
  | cf
  | zf
  | sf
  | of
  deriving DecidableEq, Repr

/-- The global index (= wasm-sim ABI location number) of a location. -/
def Loc.idx : Loc → Nat
  | .reg r => r.toBitVec.toNat
  | .rip => 16
  | .cf => 17
  | .zf => 20
  | .sf => 21
  | .of => 22

theorem Loc.idx_lt (l : Loc) : l.idx < 23 := by
  cases l with
  | reg r => have := r.toBitVec.isLt; simp only [Loc.idx]; omega
  | _ => simp [Loc.idx]

/-- The global index of a location, as a Wasm index. -/
def Loc.gidx (l : Loc) : GlobalIdx := ⟨⟨l.idx, by have := l.idx_lt; omega⟩⟩

/-! ## The abstraction -/

variable {H : Type}

/-- The value of the global of location `l`. -/
def gval (s : Store H) (f : Frame) (l : Loc) : Option Val :=
  (s.global? f l.gidx).map (·.2.value)

/-- Write the global of location `l` (no change if the instance has no such global). -/
def upd (s : Store H) (f : Frame) (l : Loc) (v : Val) : Store H :=
  match f.module.globals[l.idx]? with
  | some a => s.setGlobal a v
  | none => s

/-- The module instance of `f` maps the modelled locations to distinct existing globals. -/
structure Layout (s : Store H) (f : Frame) : Prop where
  addr : ∀ l : Loc, ∃ a, f.module.globals[l.idx]? = some a ∧ a < s.globals.length
  inj : ∀ (l₁ l₂ : Loc) (a : Nat), f.module.globals[l₁.idx]? = some a →
    f.module.globals[l₂.idx]? = some a → l₁ = l₂

/-- A Boolean as an `i64` `0`/`1`. -/
def b64 (b : Bool) : BitVec 64 := if b then 1#64 else 0#64

/-- The modelled flags (CF, ZF, SF, OF) are defined. -/
def Defined (fl : Flags) : Prop :=
  fl.carry.isSome ∧ fl.zero.isSome ∧ fl.sign.isSome ∧ fl.overflow.isSome

/-- A flag global encodes a model flag: it holds `0` or `1`, and that bit is admitted by the
model's (possibly undefined) value. -/
def FlagEnc (v : Option Val) (m : Option Bool) : Prop :=
  ∃ b : Bool, v = some (Val.i64 (b64 b)) ∧ Silmaril.X86.FlagValue.Admits m b

/-- **The abstraction relation**: the store `s` (through `f`'s instance) encodes the x86 state
`σ` on the modelled locations. -/
def Enc (s : Store H) (f : Frame) (σ : State) : Prop :=
  Layout s f ∧ (∀ r : Reg, gval s f (.reg r) = some (Val.i64 (σ.read r))) ∧
    gval s f .rip = some (Val.i64 σ.rip) ∧
    FlagEnc (gval s f .cf) σ.flags.carry ∧ FlagEnc (gval s f .zf) σ.flags.zero ∧
    FlagEnc (gval s f .sf) σ.flags.sign ∧ FlagEnc (gval s f .of) σ.flags.overflow

/-- The globals outside the modelled locations, and everything but the globals, are unchanged
from `s` to `s'`; the global list keeps its length. -/
def Frames (s s' : Store H) (f : Frame) : Prop :=
  s'.globals.length = s.globals.length ∧ s' = { s with globals := s'.globals } ∧
    ∀ a, (∀ l : Loc, f.module.globals[l.idx]? ≠ some a) → s'.globals[a]? = s.globals[a]?

/-! ## Code generation -/

/-- `global.get` of a location. -/
def gget (l : Loc) : Instr := .globalGet l.gidx
/-- `global.set` of a location. -/
def gset (l : Loc) : Instr := .globalSet l.gidx
/-- An `i64` constant. -/
def c64 (c : BitVec 64) : Instr := .intConst .i64 c
/-- An `i64` binary operation. -/
def b64op (op : IntBinOp) : Instr := .intBinOp .i64 op

/-- `e` then `>>u 63`: the most significant bit of `e` as `0`/`1`. -/
def msbCode (e : List Instr) : List Instr := e ++ [c64 63, b64op (.shr .unsigned)]

/-- `~e` (as `e xor -1`). -/
def notCode (e : List Instr) : List Instr := e ++ [c64 (-1), b64op .xor]

/-- `1 xor msb (e | (0 - e))`: `1` iff `e = 0`. -/
def zeroCode (e : List Instr) : List Instr :=
  [c64 1] ++ msbCode (e ++ [c64 0] ++ e ++ [b64op .sub, b64op .or]) ++ [b64op .xor]

/-- The Wasm operation computing an ALU result. -/
def aluWasm : AluOp → IntBinOp
  | .add => .add | .or => .or | .and => .and | .sub => .sub | .xor => .xor | .cmp => .sub

/-- CF and OF of `op x y`, with `X`, `Y` pushing the operands and `R` the result. -/
def carryCode (op : AluOp) (X Y R : List Instr) : List Instr :=
  match op with
  | .add => msbCode (X ++ Y ++ [b64op .and] ++ X ++ Y ++ [b64op .or] ++ notCode R ++ [b64op .and] ++
      [b64op .or])
  | .sub | .cmp => msbCode (notCode X ++ Y ++ [b64op .and] ++ notCode (X ++ Y ++ [b64op .xor]) ++ R ++
      [b64op .and, b64op .or])
  | .and | .or | .xor => [c64 0]

/-- OF of `op x y`. -/
def overflowCode (op : AluOp) (X Y R : List Instr) : List Instr :=
  match op with
  | .add => msbCode (X ++ R ++ [b64op .xor] ++ Y ++ R ++ [b64op .xor, b64op .and])
  | .sub | .cmp => msbCode (X ++ Y ++ [b64op .xor] ++ X ++ R ++ [b64op .xor, b64op .and])
  | .and | .or | .xor => [c64 0]

/-- `op dst, src` on 64-bit registers: the four modelled flags, then the destination (unless
`cmp`). Every flag is computed from the operands before the destination is written. -/
def aluCode (op : AluOp) (d s : Reg) : List Instr :=
  let X := [gget (.reg d)]
  let Y := [gget (.reg s)]
  let R := X ++ Y ++ [b64op (aluWasm op)]
  carryCode op X Y R ++ [gset .cf] ++ overflowCode op X Y R ++ [gset .of] ++
    zeroCode R ++ [gset .zf] ++ msbCode R ++ [gset .sf] ++
    (if op = .cmp then [] else R ++ [gset (.reg d)])

/-- A condition code as an `i64` `0`/`1` computed from the flag globals (`none` for `p`/`np`,
which read the unmodelled PF). -/
def condCode : Silmaril.X86.Ext.Cond → Option (List Instr)
  | .o => some [gget .of]
  | .no => some [gget .of, c64 1, b64op .xor]
  | .b => some [gget .cf]
  | .ae => some [gget .cf, c64 1, b64op .xor]
  | .e => some [gget .zf]
  | .ne => some [gget .zf, c64 1, b64op .xor]
  | .be => some [gget .cf, gget .zf, b64op .or]
  | .a => some [gget .cf, gget .zf, b64op .or, c64 1, b64op .xor]
  | .s => some [gget .sf]
  | .ns => some [gget .sf, c64 1, b64op .xor]
  | .p | .np => none
  | .l => some [gget .sf, gget .of, b64op .xor]
  | .ge => some [gget .sf, gget .of, b64op .xor, c64 1, b64op .xor]
  | .le => some [gget .zf, gget .sf, gget .of, b64op .xor, b64op .or]
  | .g => some [gget .zf, gget .sf, gget .of, b64op .xor, b64op .or, c64 1, b64op .xor]

/-- `cmovcc dst, src`: `dst := dst xor ((dst xor src) and (0 - cc))`. -/
def cmovCode (cc : List Instr) (d s : Reg) : List Instr :=
  [gget (.reg d), gget (.reg d), gget (.reg s), b64op .xor, c64 0] ++ cc ++
    [b64op .sub, b64op .and, b64op .xor, gset (.reg d)]

/-- `test d, s` (64-bit): CF = OF = 0, ZF and SF of `d & s`, no write. -/
def testCode (d s : Reg) : List Instr :=
  let R := [gget (.reg d), gget (.reg s), b64op .and]
  [c64 0, gset .cf, c64 0, gset .of] ++ zeroCode R ++ [gset .zf] ++ msbCode R ++ [gset .sf]

/-- `dec d` (64-bit): OF, ZF, SF of `d - 1` (CF unchanged), then `d := d - 1`. -/
def decCode (d : Reg) : List Instr :=
  let X := [gget (.reg d)]
  let Y := [c64 1]
  let R := X ++ Y ++ [b64op .sub]
  overflowCode .sub X Y R ++ [gset .of] ++ zeroCode R ++ [gset .zf] ++ msbCode R ++ [gset .sf] ++
    R ++ [gset (.reg d)]

/-- `xor r32, r32` (the same register): `r := 0`, CF = OF = SF = 0, ZF = 1. -/
def zero32Code (d : Reg) : List Instr :=
  [c64 0, gset .cf, c64 0, gset .of, c64 1, gset .zf, c64 0, gset .sf, c64 0, gset (.reg d)]

/-- `mov r32, r32`: `d := s & 0xffffffff` (32-bit writes zero-extend), flags unchanged. -/
def mov32Code (d s : Reg) : List Instr :=
  [gget (.reg s), c64 0xffffffff, b64op .and, gset (.reg d)]

/-- `bswap r32`: the low four bytes of `d` reversed, zero-extended; flags unchanged. -/
def bswap32Code (d : Reg) : List Instr :=
  [gget (.reg d), c64 0xff, b64op .and, c64 24, b64op .shl,
   gget (.reg d), c64 8, b64op (.shr .unsigned), c64 0xff, b64op .and, c64 16, b64op .shl,
   b64op .or,
   gget (.reg d), c64 16, b64op (.shr .unsigned), c64 0xff, b64op .and, c64 8, b64op .shl,
   b64op .or,
   gget (.reg d), c64 24, b64op (.shr .unsigned), c64 0xff, b64op .and, b64op .or,
   gset (.reg d)]

/-- `op r32, r32`: the operands are moved to the high half (`<< 32`), where
the 64-bit flag formulas of `aluCode` compute the 32-bit flags; the result is shifted back
(`>>u 32`: zero-extended). -/
def alu32Code (op : AluOp) (d s : Reg) : List Instr :=
  let X := [gget (.reg d), c64 32, b64op .shl]
  let Y := [gget (.reg s), c64 32, b64op .shl]
  let R := X ++ Y ++ [b64op (aluWasm op)]
  carryCode op X Y R ++ [gset .cf] ++ overflowCode op X Y R ++ [gset .of] ++
    zeroCode R ++ [gset .zf] ++ msbCode R ++ [gset .sf] ++
    (if op = .cmp then [] else R ++ [c64 32, b64op (.shr .unsigned), gset (.reg d)])

/-- `test r32, r32`: CF = OF = 0, ZF and SF of the 32-bit `d & s` (in the high half). -/
def test32Code (d s : Reg) : List Instr :=
  let R := [gget (.reg d), c64 32, b64op .shl, gget (.reg s), c64 32, b64op .shl, b64op .and]
  [c64 0, gset .cf, c64 0, gset .of] ++ zeroCode R ++ [gset .zf] ++ msbCode R ++ [gset .sf]

/-- `mov r32, imm32`: `d := zext imm`. -/
def movI32Code (d : Reg) (imm : BitVec 32) : List Instr := [c64 (imm.setWidth 64), gset (.reg d)]

open Silmaril.X86.Ext (Sz RM) in
/-- **The method body** of an instruction, without the RIP update. -/
def emitCore : Silmaril.X86.Ext.Instr → Option (List Instr)
  | .mov .q (.reg d) s => some [gget (.reg s), gset (.reg d)]
  | .movI .q (.reg d) imm => some [c64 (imm.signExtend 64), gset (.reg d)]
  | .movabs d imm => some [c64 imm, gset (.reg d)]
  | .alu .q op (.reg d) s => some (aluCode op d s)
  | .cmov .q c d (.reg s) => (condCode c).map fun cc => cmovCode cc d s
  | .test .q (.reg d) s => some (testCode d s)
  | .incdec .q true (.reg d) => some (decCode d)
  | .alu .d .xor (.reg d) s => if d = s then some (zero32Code d) else some (alu32Code .xor d s)
  | .mov .d (.reg d) s => some (mov32Code d s)
  | .bswap .d d => some (bswap32Code d)
  | .alu .d op (.reg d) s => some (alu32Code op d s)
  | .test .d (.reg d) s => some (test32Code d s)
  | .movI32 d imm => some (movI32Code d imm)
  | _ => none

/-- `i_next len`: `rip += len`. -/
def nextCode (len : Nat) : List Instr :=
  [gget .rip, c64 (BitVec.ofNat 64 len), b64op .add, gset .rip]

/-- **The method** of an instruction of byte length `len`: its effect, then `rip += len`. -/
def emit (i : Silmaril.X86.Ext.Instr) (len : Nat) : Option (List Instr) :=
  (emitCore i).map (· ++ nextCode len)

/-- `jcc rel8` of length `len`: `rip += len + ((0 - cc) & sext rel)`. -/
def jccCode (cc : List Instr) (rel : BitVec 8) (len : Nat) : List Instr :=
  [gget .rip, c64 (BitVec.ofNat 64 len), b64op .add, c64 0] ++ cc ++
    [b64op .sub, c64 (rel.signExtend 64), b64op .and, b64op .add, gset .rip]

/-- `jmp rel8` of length `len`: `rip += len + sext rel`. -/
def jmpCode (rel : BitVec 8) (len : Nat) : List Instr :=
  [gget .rip, c64 (BitVec.ofNat 64 len + rel.signExtend 64), b64op .add, gset .rip]

/-- **The method of an instruction, jumps included**: `jcc rel8` (conditions but `p`/`np`) and
`jmp rel8` update RIP themselves; every other form is `emit`. -/
def emitX (i : Silmaril.X86.Ext.Instr) (len : Nat) : Option (List Instr) :=
  match i with
  | .jcc8 c rel => (condCode c).map fun cc => jccCode cc rel len
  | .jmp8 rel => some (jmpCode rel len)
  | i => emit i len

/-- A straight-line x86 program: decoded instructions with their byte lengths. -/
abbrev XProg := List (Silmaril.X86.Ext.Instr × Nat)

/-- **P-inline**: the Wasm code of a straight-line program, the methods concatenated. -/
def emitProg : XProg → Option (List Instr)
  | [] => some []
  | (i, n) :: p => do
    let c ← emit i n
    let cs ← emitProg p
    pure (c ++ cs)

/-- Run a straight-line program on `Silmaril.X86.Ext.exec`; `none` unless every instruction
retires (`Result.ok`). -/
def runExt : XProg → State → Silmaril.Process.Memory → Option (State × Silmaril.Process.Memory)
  | [], σ, m => some (σ, m)
  | (i, n) :: p, σ, m =>
    match Silmaril.X86.Ext.exec i σ m n with
    | .ok σ' m' => runExt p σ' m'
    | _ => none

/-! ## Canonical encodings and problems -/

/-- The value of global `i` in the canonical encoding of `σ`: the GPRs, RIP and the modelled
flags (an undefined flag holds `0`); the unmodelled PF (`18`) and AF (`19`) hold `0`. There is
no DF global: the encoding has the 23 globals `0..22`. -/
def encVal (σ : State) (i : Fin 23) : BitVec 64 :=
  if i.val < 16 then σ.read (Reg.ofBitVec (BitVec.ofNat 4 i.val))
  else if i.val = 16 then σ.rip
  else if i.val = 17 then b64 (σ.flags.carry.getD false)
  else if i.val = 20 then b64 (σ.flags.zero.getD false)
  else if i.val = 21 then b64 (σ.flags.sign.getD false)
  else if i.val = 22 then b64 (σ.flags.overflow.getD false)
  else 0

/-- The canonical store encoding `σ`: 23 mutable `i64` globals. -/
def encStore (σ : State) : Store H :=
  { globals := List.ofFn fun i => ⟨⟨.var, .num (.int .i64)⟩, Val.i64 (encVal σ i)⟩ }

/-- The frame of the canonical encoding: globals `0..22` at addresses `0..22`. -/
def encFrame : Frame := { module := { globals := List.range 23 } }

/-- A flag global holds a bit. -/
def GBit (s : Store H) (f : Frame) (l : Loc) : Prop := ∃ b, gval s f l = some (Val.i64 (b64 b))

/-- The Wasm reading of a register file (no x86 state involved): the instance lays out the
modelled globals, the register globals hold `R`, the RIP global some `i64` and the modelled flag
globals bits. -/
def GRegs (s : Store H) (f : Frame) (R : Reg → BitVec 64) : Prop :=
  Layout s f ∧ (∀ r, gval s f (.reg r) = some (Val.i64 (R r))) ∧
    (∃ w, gval s f .rip = some (Val.i64 w)) ∧ GBit s f .cf ∧ GBit s f .zf ∧ GBit s f .sf ∧
    GBit s f .of

/-- **The x86 problem**: every run of the straight-line program `p` that retires maps a state
whose registers satisfy `Pre` to one whose registers satisfy `Post`. -/
def XProblem (p : XProg) (Pre : (Reg → BitVec 64) → Prop)
    (Post : (Reg → BitVec 64) → (Reg → BitVec 64) → Prop) : Prop :=
  ∀ (σ σ' : State) (m m' : Silmaril.Process.Memory), Pre σ.read → runExt p σ m = some (σ', m') →
    Post σ.read σ'.read

/-- **The Wasm problem**: from any store holding registers `R` with `Pre R`, every run of the
code that stops falls through with registers `R'` (in the register globals) satisfying
`Post R R'`. -/
def WProblem (P : Profile) (host : HostSemantics H) (code : List Instr)
    (Pre : (Reg → BitVec 64) → Prop) (Post : (Reg → BitVec 64) → (Reg → BitVec 64) → Prop) :
    Prop :=
  ∀ (s : Store H) (f : Frame) (R : Reg → BitVec 64), GRegs s f R → Pre R →
    Silmaril.Wasm.Logic.Hoare.HWP P host s f (expression code) fun s' f' o => o = .normal [] ∧
      ∀ R' : Reg → BitVec 64, (∀ r, gval s' f' (.reg r) = some (Val.i64 (R' r))) → Post R R'


/-! ## Code placement, method specifications -/

section Placement

open Silmaril.X86 (Byte)
open Silmaril.X86.Ext (fetch Fetch)
open Silmaril.Process (Memory)

/-- The memory decodes to the instructions of `p` from address `a` on. -/
def CodeAt (mem : Memory) : Word → XProg → Prop
  | _, [] => True
  | a, (i, n) :: p => fetch mem a.toNat = .decoded i n ∧ CodeAt mem (a + BitVec.ofNat 64 n) p

/-- The address after the code of `p` placed at `a`. -/
def endAddr : Word → XProg → Word
  | a, [] => a
  | a, (_, n) :: p => endAddr (a + BitVec.ofNat 64 n) p

/-- Byte spans placed one after the other from address `a`, each executable and backed. -/
def BytesAt (mem : Memory) : Word → List (List Byte) → Prop
  | _, [] => True
  | a, bs :: bss => mem.fetchBytes a.toNat bs.length = some bs ∧
      BytesAt mem (a + BitVec.ofNat 64 bs.length) bss

end Placement

/-- The x86 state a store holds: its registers and RIP, its modelled flag bits as defined flags,
PF and AF undefined. -/
def stateOf (R : Reg → BitVec 64) (w : BitVec 64) (bc bz bs bo : Bool) : State where
  regs := R
  rip := w
  flags := ⟨some bc, none, none, some bz, some bs, some bo⟩

/-- **The specification of the method of `i`** at address `a` (function instance `fi`): called
without arguments on a store holding registers, RIP and flag bits in `fi`'s instance, it returns
nothing, and the new store encodes the x86 result (RIP excepted) of every state the old one
encodes, changing only modelled globals. -/
def methodSpec (fi : FuncInst H) (a : Nat) (i : Silmaril.X86.Ext.Instr) : Silmaril.Wasm.Logic.Hoare.FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ args = [] ∧
    ∃ R, GRegs s (Frame.forCall fi.module [] []) R
  post s _ s' o := o = .normal [] ∧ Frames s s' (Frame.forCall fi.module [] []) ∧
    ∀ (σ σ' : State) (m m' : Silmaril.Process.Memory) (len : Nat),
      Enc s (Frame.forCall fi.module [] []) σ → Silmaril.X86.Ext.exec i σ m len = .ok σ' m' →
      Enc s' (Frame.forCall fi.module [] []) { σ' with rip := σ.rip }


/-! ## The simulator as a WAT module -/

/-- **The G simulator for a handful of instruction instances**, written in WAT: the 23 location
globals (exported), one method per instruction instance (`i_<form>_<regs>`, no parameters; each
body is `emitCore` of the instruction, checked by `rfl` in
`Silmaril.Proofs.Sim.X86.G.Method`), `i_next` (`rip += len`, `len : i64`) and the program `max`
in the P-calls representation (calls of the methods; executable, not verified: the generator
`wpc` has no call rule; the certified call form is `Silmaril.Sim.X86.GCert`). -/
def simModule : Module := wat3! r#"
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
  (func $i_mov_rax_rdi (export "i_mov_rax_rdi")
    (global.set $rax (global.get $rdi)))
  (func $i_add_rax_rsi (export "i_add_rax_rsi")
    (global.set $cf (i64.shr_u (i64.or (i64.and (global.get $rax) (global.get $rsi)) (i64.and (i64.or (global.get $rax) (global.get $rsi)) (i64.xor (i64.add (global.get $rax) (global.get $rsi)) (i64.const -1)))) (i64.const 63)))
    (global.set $of (i64.shr_u (i64.and (i64.xor (global.get $rax) (i64.add (global.get $rax) (global.get $rsi))) (i64.xor (global.get $rsi) (i64.add (global.get $rax) (global.get $rsi)))) (i64.const 63)))
    (global.set $zf (i64.xor (i64.const 1) (i64.shr_u (i64.or (i64.add (global.get $rax) (global.get $rsi)) (i64.sub (i64.const 0) (i64.add (global.get $rax) (global.get $rsi)))) (i64.const 63))))
    (global.set $sf (i64.shr_u (i64.add (global.get $rax) (global.get $rsi)) (i64.const 63)))
    (global.set $rax (i64.add (global.get $rax) (global.get $rsi))))
  (func $i_sub_rax_rsi (export "i_sub_rax_rsi")
    (global.set $cf (i64.shr_u (i64.or (i64.and (i64.xor (global.get $rax) (i64.const -1)) (global.get $rsi)) (i64.and (i64.xor (i64.xor (global.get $rax) (global.get $rsi)) (i64.const -1)) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63)))
    (global.set $of (i64.shr_u (i64.and (i64.xor (global.get $rax) (global.get $rsi)) (i64.xor (global.get $rax) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63)))
    (global.set $zf (i64.xor (i64.const 1) (i64.shr_u (i64.or (i64.sub (global.get $rax) (global.get $rsi)) (i64.sub (i64.const 0) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63))))
    (global.set $sf (i64.shr_u (i64.sub (global.get $rax) (global.get $rsi)) (i64.const 63)))
    (global.set $rax (i64.sub (global.get $rax) (global.get $rsi))))
  (func $i_xor_rax_rsi (export "i_xor_rax_rsi")
    (global.set $cf (i64.const 0))
    (global.set $of (i64.const 0))
    (global.set $zf (i64.xor (i64.const 1) (i64.shr_u (i64.or (i64.xor (global.get $rax) (global.get $rsi)) (i64.sub (i64.const 0) (i64.xor (global.get $rax) (global.get $rsi)))) (i64.const 63))))
    (global.set $sf (i64.shr_u (i64.xor (global.get $rax) (global.get $rsi)) (i64.const 63)))
    (global.set $rax (i64.xor (global.get $rax) (global.get $rsi))))
  (func $i_cmp_rax_rsi (export "i_cmp_rax_rsi")
    (global.set $cf (i64.shr_u (i64.or (i64.and (i64.xor (global.get $rax) (i64.const -1)) (global.get $rsi)) (i64.and (i64.xor (i64.xor (global.get $rax) (global.get $rsi)) (i64.const -1)) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63)))
    (global.set $of (i64.shr_u (i64.and (i64.xor (global.get $rax) (global.get $rsi)) (i64.xor (global.get $rax) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63)))
    (global.set $zf (i64.xor (i64.const 1) (i64.shr_u (i64.or (i64.sub (global.get $rax) (global.get $rsi)) (i64.sub (i64.const 0) (i64.sub (global.get $rax) (global.get $rsi)))) (i64.const 63))))
    (global.set $sf (i64.shr_u (i64.sub (global.get $rax) (global.get $rsi)) (i64.const 63))))
  (func $i_cmovl_rax_rsi (export "i_cmovl_rax_rsi")
    (global.set $rax (i64.xor (global.get $rax) (i64.and (i64.xor (global.get $rax) (global.get $rsi))
      (i64.sub (i64.const 0) (i64.xor (global.get $sf) (global.get $of)))))))
  (func $i_next (export "i_next") (param $len i64)
    (global.set $rip (i64.add (global.get $rip) (local.get $len))))
  (func $max (export "max")
    (call $i_mov_rax_rdi) (call $i_next (i64.const 3))
    (call $i_cmp_rax_rsi) (call $i_next (i64.const 3))
    (call $i_cmovl_rax_rsi) (call $i_next (i64.const 4))))
"#

end Silmaril.Sim.X86.G
