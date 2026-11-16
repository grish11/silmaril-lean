module

public import Silmaril.Sim.X86.Loop.Defs

/-!
# The G simulator with memory (GM): the guest memory window in Wasm memory 0 (header)

Memory operands and the stack, with the x86 memory (`Silmaril.Process.Memory`) represented by a
**window** of it in the instance's Wasm memory 0:

* `Win`: guest addresses `[lo, lo + size)` (no wrap, `size ≤ 2^32`); guest byte `lo + k` is Wasm
  byte `k`. `MemEnc s f mem W`: every window byte is readable, writable and backed in `mem`,
  and the Wasm memory 0 holds the same byte at the translated address.
* Address code (`addrCode`): the i64 effective address `base + index << scale + disp` from the
  register globals. `offCode`: minus `lo`. `wrapCode`: the low 32 bits as an `i32` address,
  bit by bit with `i64.shr_u`/`i64.and`/`i64.ne` (`i32.wrap_i64` is not evaluated by
  `Silmaril.Wasm.Logic.Core.exec1`). `checkCode`: traps (`i32.div_u` by zero) unless the 8-byte
  access lies inside the window: **the Wasm code checks its own memory safety**, so a Wasm
  proof that the code does not trap establishes the separation side condition.
* `loadCode X`, `storeCode X V`: the checked 64-bit load/store at the address `X` computes.
* `emitM W i len`: methods for `mov r64, [m]`, `mov [m], r64`, `push r64`, `pop r64`,
  `call rel32`, `ret`, `op r64, imm8/imm32` (`add/sub/and/or/xor/cmp`), all of `emitX`, and the
  width-generic forms `formOf` (`emitForm`): narrow loads (`loadCodeK`, zero-extending packed
  `i64` loads, sign extension by `shl`/`shr_s`), compare/test at 8/16/32/64 bits (`flagPush`:
  the operands shifted to the top bits, where the 64-bit flag formulas give the narrow flags),
  `op r64, r/m64`, `nop`. `access` gives each instruction's access (address, byte count).
* `Win.rw`: a read-only window (a read footprint) has no store, push or call methods.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State AluOp)
open Silmaril.X86.Ext (Sz RM Mem Base Index)
open Silmaril.Sim.X86.G

variable {H : Type}

/-! ## The window -/

/-- The guest window `[lo, lo + size)`. -/
structure Win where
  lo : Word
  size : Nat
  /-- The window is writable (stores, pushes and calls have methods only then). -/
  rw : Bool := true

/-- The bytes of Wasm memory 0 of the instance. -/
def wbytes (s : Store H) (f : Frame) : Option ByteArray := (s.mem? f ⟨0⟩).map (·.2.bytes)

/-- **The memory abstraction**: the window is readable (and writable if `W.rw`) and backed in
`mem`, and Wasm memory 0 holds its bytes at offset `- lo`. -/
def MemEnc (s : Store H) (f : Frame) (mem : Silmaril.Process.Memory) (W : Win) : Prop :=
  ∃ B, wbytes s f = some B ∧ W.size ≤ B.size ∧ W.size ≤ 2 ^ 32 ∧
    W.lo.toNat + W.size ≤ 2 ^ 64 ∧
    ∀ k < W.size, mem.permits .read (W.lo.toNat + k) = true ∧
      (W.rw = true → mem.permits .write (W.lo.toNat + k) = true) ∧
      ∃ x, mem.bytes.get? (W.lo.toNat + k) = some x ∧ B.data.toList[k]? = some (UInt8.ofBitVec x)

/-- The 8-byte access at `a` lies in the window. -/
def Win.Holds (W : Win) (a : Word) : Prop := W.lo.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ W.lo.toNat + W.size

/-- The `k`-byte access at `a` lies in the window. -/
def Win.HoldsK (W : Win) (k : Nat) (a : Word) : Prop :=
  W.lo.toNat ≤ a.toNat ∧ a.toNat + k ≤ W.lo.toNat + W.size

/-- The guest addresses of the window (a `FnContract` footprint). -/
def Win.Mem (W : Win) (a : Nat) : Prop := W.lo.toNat ≤ a ∧ a < W.lo.toNat + W.size

/-! ## Code -/

/-- An `i32` constant. -/
def c32 (c : BitVec 32) : Instr := .intConst .i32 c
/-- An `i32` binary operation. -/
def b32op (op : IntBinOp) : Instr := .intBinOp .i32 op

/-- The base of an address (register or none). -/
def baseCode : Base → List Instr
  | .reg b => [gget (.reg b)]
  | _ => [c64 0]

/-- Add the scaled index. -/
def indexCode : Option Index → List Instr
  | some i => [gget (.reg i.reg), c64 (BitVec.ofNat 64 i.scale.toNat), b64op .shl, b64op .add]
  | none => []

/-- The effective address of a memory operand with a register or no base (not RIP/FS). -/
def addrCode (m : Mem) : List Instr :=
  baseCode m.base ++ indexCode m.index ++ [c64 (m.disp.signExtend 64), b64op .add]

/-- The address minus the window base. -/
def offCode (W : Win) (X : List Instr) : List Instr := X ++ [c64 W.lo, b64op .sub]

/-- One bit of the `i32` wrap: `acc += ((x >>u k) & 1 ≠ 0) << k`. -/
def wrapStep (X : List Instr) (k : Nat) : List Instr :=
  X ++ [c64 (BitVec.ofNat 64 k), b64op (.shr .unsigned), c64 1, b64op .and, c64 0,
    .intRelOp .i64 .ne, c32 (BitVec.ofNat 32 k), b32op .shl, b32op .add]

/-- The first `k` bits. -/
def wrapAux (X : List Instr) : Nat → List Instr
  | 0 => []
  | k + 1 => wrapAux X k ++ wrapStep X k

/-- The low 32 bits of the `i64` that `X` computes, as an `i32`. -/
def wrapCode (X : List Instr) : List Instr := [c32 0] ++ wrapAux X 32

/-- Trap unless the 8-byte access at the address `X` computes lies in the window. -/
def checkCodeK (W : Win) (k : Nat) (X : List Instr) : List Instr :=
  if k ≤ W.size then
    [c32 1] ++ offCode W X ++ [c64 (BitVec.ofNat 64 (W.size - k)), .intRelOp .i64 (.le .unsigned),
      b32op (.div .unsigned), .drop]
  else [c32 1, c32 0, b32op (.div .unsigned), .drop]

/-- The check of an 8-byte access. -/
def checkCode (W : Win) (X : List Instr) : List Instr := checkCodeK W 8 X

/-- The memory argument of the 64-bit accesses (no offset). -/
def marg : MemArg := ⟨3, 0⟩

/-- Checked 64-bit load from the address `X` computes. -/
def loadCode (W : Win) (X : List Instr) : List Instr :=
  checkCode W X ++ wrapCode (offCode W X) ++ [.intLoad .i64 none ⟨0⟩ marg]

/-- Checked 64-bit store of the value `V` computes at the address `X` computes. -/
def storeCode (W : Win) (X V : List Instr) : List Instr :=
  checkCode W X ++ wrapCode (offCode W X) ++ V ++ [.intStore .i64 none ⟨0⟩ marg]

/-- `rsp - 8`. -/
def rspDown : List Instr := [gget (.reg .rsp), c64 8, b64op .sub]

/-- `op d, imm` (64-bit register destination, immediate already sign-extended). -/
def aluICode (op : AluOp) (d : Reg) (c : Word) : List Instr :=
  let X := [gget (.reg d)]
  let Y := [c64 c]
  let R := X ++ Y ++ [b64op (aluWasm op)]
  carryCode op X Y R ++ [gset .cf] ++ overflowCode op X Y R ++ [gset .of] ++
    zeroCode R ++ [gset .zf] ++ msbCode R ++ [gset .sf] ++
    (if op = .cmp then [] else R ++ [gset (.reg d)])

/-- A memory operand the methods handle: register or no base. -/
def plainMem (m : Mem) : Bool :=
  match m.base with
  | .reg _ | .none => true
  | _ => false

/-- `mov r64, [m]`. -/
def loadM (W : Win) (sz : Sz) (d : Reg) (m : Mem) (len : Nat) : Option (List Instr) :=
  if sz = .q ∧ plainMem m = true then
    some (loadCode W (addrCode m) ++ [gset (.reg d)] ++ nextCode len)
  else none

/-- `mov [m], r64`. -/
def storeM (W : Win) (sz : Sz) (dst : RM) (src : Reg) (len : Nat) : Option (List Instr) :=
  match sz, dst with
  | .q, .mem m =>
    if W.rw = true ∧ plainMem m = true then
      some (storeCode W (addrCode m) [gget (.reg src)] ++ nextCode len)
    else none
  | _, _ => none

/-- `op r64, imm`. -/
def aluIM (sz : Sz) (op : AluOp) (dst : RM) (c : Word) (len : Nat) : Option (List Instr) :=
  match sz, dst with
  | .q, .reg d => some (aluICode op d c ++ nextCode len)
  | _, _ => none

/-- The methods of the memory and stack forms, RIP update included. -/
def emitMem (W : Win) (i : Silmaril.X86.Ext.Instr) (len : Nat) : Option (List Instr) :=
  match i with
  | .load sz d m => loadM W sz d m len
  | .mov sz dst src => storeM W sz dst src len
  | .push r =>
    if W.rw = true then
      some (storeCode W rspDown [gget (.reg r)] ++ rspDown ++ [gset (.reg .rsp)] ++ nextCode len)
    else none
  | .pop r =>
    some (loadCode W [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
      gset (.reg .rsp), gset (.reg r)] ++ nextCode len)
  | .call rel =>
    if W.rw = true then
      some (storeCode W rspDown [gget .rip, c64 (BitVec.ofNat 64 len), b64op .add] ++ rspDown ++
        [gset (.reg .rsp), gget .rip, c64 (BitVec.ofNat 64 len + rel.signExtend 64), b64op .add,
          gset .rip])
    else none
  | .ret =>
    some (loadCode W [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
      gset (.reg .rsp), gset .rip])
  | .aluI8 sz op dst imm => aluIM sz op dst (imm.signExtend 64) len
  | .aluI sz op dst imm => aluIM sz op dst (imm.signExtend 64) len
  | .movI _ _ _ => none
  | .movI16 _ _ => none
  | .mov8 _ _ => none
  | .movI8 _ _ => none
  | .movI32 _ _ => none
  | .movabs _ _ => none
  | .store _ _ _ => none
  | .movx _ _ _ _ _ => none
  | .movsxd _ _ => none
  | .lea _ _ _ => none
  | .alu _ _ _ _ => none
  | .aluR _ _ _ _ => none
  | .aluA _ _ _ => none
  | .test _ _ _ => none
  | .test8 _ _ => none
  | .testI8 _ _ => none
  | .testA8 _ => none
  | .cmpI8 _ _ => none
  | .cmpA8 _ => none
  | .testA _ _ => none
  | .incdec _ _ _ => none
  | .pushRM _ => none
  | .bswap _ _ => none
  | .unary _ _ _ => none
  | .imul _ _ _ => none
  | .mul _ _ => none
  | .shift _ _ _ _ => none
  | .cxd _ => none
  | .cxe _ => none
  | .div _ _ _ => none
  | .cmov _ _ _ _ => none
  | .setcc _ _ => none
  | .jmp _ => none
  | .jmp8 _ => none
  | .jcc _ _ => none
  | .jcc8 _ _ => none
  | .leave => none
  | .endbr64 => none
  | .ud2 => none
  | .nop _ => none
  | .bitcount _ _ _ _ => none


/-! ## Width-generic forms: narrow loads, compare/test, ALU with a memory operand -/

/-- An operand: a register, an immediate, or a memory operand (register or no base). -/
inductive Opd where
  | reg (r : Reg)
  | imm (c : Word)
  | mem (m : Mem) (h : plainMem m = true)

/-- The operand of an `r/m` (`none` for RIP- or FS-relative memory). -/
def opdOf : RM → Option Opd
  | .reg r => some (.reg r)
  | .mem m => if h : plainMem m = true then some (.mem m h) else none

/-- The memory argument of a `k`-byte access (natural alignment, no offset). -/
def margK : Nat → MemArg
  | 1 => ⟨0, 0⟩
  | 2 => ⟨1, 0⟩
  | 4 => ⟨2, 0⟩
  | _ => marg

/-- The zero-extending `i64` load of `k` bytes (`k ∈ {1, 2, 4, 8}`). -/
def ldK : Nat → Instr
  | 1 => .intLoad .i64 (some (.i8, .unsigned)) ⟨0⟩ (margK 1)
  | 2 => .intLoad .i64 (some (.i16, .unsigned)) ⟨0⟩ (margK 2)
  | 4 => .intLoad .i64 (some (.i32, .unsigned)) ⟨0⟩ (margK 4)
  | _ => .intLoad .i64 none ⟨0⟩ marg

/-- Checked zero-extending `k`-byte load from the address `X` computes. -/
def loadCodeK (W : Win) (k : Nat) (X : List Instr) : List Instr :=
  checkCodeK W k X ++ wrapCode (offCode W X) ++ [ldK k]

/-- The value of an operand (memory: zero-extended, `w / 8` bytes). -/
def opdCode (W : Win) (w : Nat) : Opd → List Instr
  | .reg r => [gget (.reg r)]
  | .imm c => [c64 c]
  | .mem m _ => loadCodeK W (w / 8) (addrCode m)

/-- `X << (64 - w)`: a `w`-bit value in the top bits, where the 64-bit flag formulas give the
`w`-bit flags. -/
def upCode (w : Nat) (X : List Instr) : List Instr :=
  X ++ [c64 (BitVec.ofNat 64 (64 - w)), b64op .shl]

/-- Push SF, ZF, OF, CF (CF on top) of `op x, y` (64-bit operands `X`, `Y`). -/
def flagPush (op : AluOp) (X Y : List Instr) : List Instr :=
  let R := X ++ Y ++ [b64op (aluWasm op)]
  msbCode R ++ zeroCode R ++ overflowCode op X Y R ++ carryCode op X Y R

/-- Pop the flags `flagPush` pushed. -/
def flagSet : List Instr := [gset .cf, gset .of, gset .zf, gset .sf]

/-- A flag-setting form: `op a, b` at width `w` (`and` for TEST, `sub` or `cmp` for CMP),
writing the result to `wb` (64-bit only). -/
structure FForm where
  w : Nat
  op : AluOp
  a : Opd
  b : Opd
  wb : Option Reg

/-- A load form: `d := ext(src)` from `w` bits (sign- or zero-extended), at destination size
`dsz` (32-bit destinations zero-extend). -/
structure LForm where
  w : Nat
  sx : Bool
  src : Opd
  dsz : Sz
  d : Reg

/-- The width-generic forms. -/
inductive Form where
  | flag (F : FForm)
  | load (L : LForm)
  | nop

/-- The result write-back of a flag form. -/
def wbCode (W : Win) (F : FForm) : List Instr :=
  match F.wb with
  | none => []
  | some d => upCode F.w (opdCode W F.w F.a) ++ upCode F.w (opdCode W F.w F.b) ++
      [b64op (aluWasm F.op), gset (.reg d)]

/-- The method body of a form. -/
def Form.code (W : Win) : Form → List Instr
  | .flag F => flagPush F.op (upCode F.w (opdCode W F.w F.a)) (upCode F.w (opdCode W F.w F.b)) ++
      wbCode W F ++ flagSet
  | .load L => upCode L.w (opdCode W L.w L.src) ++
      [c64 (BitVec.ofNat 64 (64 - L.w)), b64op (.shr (if L.sx then .signed else .unsigned))] ++
      (if L.dsz = .d then [c64 0xffffffff, b64op .and] else []) ++ [gset (.reg L.d)]
  | .nop => []

/-- A flag form from `r/m` operands. -/
def flagOf (w : Nat) (op : AluOp) (a : RM) (b : Opd) : Option Form :=
  (opdOf a).map fun a => .flag ⟨w, op, a, b, none⟩

/-- `op r, r/m`: CMP at both sizes, the other operations at 64 bits. -/
def aluROf (sz : Sz) (op : AluOp) (d : Reg) (src : RM) : Option Form :=
  (opdOf src).bind fun b =>
    if op = .cmp then some (.flag ⟨sz.bits, .cmp, .reg d, b, none⟩)
    else if sz = .q then some (.flag ⟨64, op, .reg d, b, some d⟩) else none

/-- `cmp r/m, imm` (the immediate sign-extended). -/
def cmpIOf (sz : Sz) (op : AluOp) (dst : RM) (c : Word) : Option Form :=
  if op = .cmp then flagOf sz.bits .cmp dst (.imm c) else none

/-- `cmp r/m, r`. -/
def cmpOf (sz : Sz) (op : AluOp) (dst : RM) (src : Reg) : Option Form :=
  if op = .cmp then flagOf sz.bits .cmp dst (.reg src) else none

/-- `mov r32, [m]`. -/
def load32Of (sz : Sz) (d : Reg) (m : Mem) : Option Form :=
  if h : sz = .d ∧ plainMem m = true then some (.load ⟨32, false, .mem m h.2, .q, d⟩) else none

/-- The width-generic form of an instruction, if any. -/
def formOf (i : Silmaril.X86.Ext.Instr) : Option Form :=
  match i with
  | .load sz d m => load32Of sz d m
  | .movx sx sz n d src => (opdOf src).map fun o => .load ⟨n.bits, sx, o, sz, d⟩
  | .movsxd d src => (opdOf src).map fun o => .load ⟨32, true, o, .q, d⟩
  | .test sz dst src => flagOf sz.bits .and dst (.reg src)
  | .test8 dst src => flagOf 8 .and dst (.reg src)
  | .testI8 dst imm => flagOf 8 .and dst (.imm (imm.setWidth 64))
  | .cmpI8 dst imm => flagOf 8 .cmp dst (.imm (imm.setWidth 64))
  | .testA8 imm => some (.flag ⟨8, .and, .reg .rax, .imm (imm.setWidth 64), none⟩)
  | .cmpA8 imm => some (.flag ⟨8, .cmp, .reg .rax, .imm (imm.setWidth 64), none⟩)
  | .testA sz imm => some (.flag ⟨sz.bits, .and, .reg .rax, .imm (imm.signExtend 64), none⟩)
  | .aluA sz op imm => cmpIOf sz op (.reg .rax) (imm.signExtend 64)
  | .alu sz op dst src => cmpOf sz op dst src
  | .aluR sz op d src => aluROf sz op d src
  | .aluI sz op dst imm => cmpIOf sz op dst (imm.signExtend 64)
  | .aluI8 sz op dst imm => cmpIOf sz op dst (imm.signExtend 64)
  | .nop _ => some .nop
  | .mov _ _ _ => none
  | .movI _ _ _ => none
  | .movI16 _ _ => none
  | .mov8 _ _ => none
  | .movI8 _ _ => none
  | .movI32 _ _ => none
  | .movabs _ _ => none
  | .store _ _ _ => none
  | .lea _ _ _ => none
  | .incdec _ _ _ => none
  | .push _ => none
  | .pop _ => none
  | .pushRM _ => none
  | .bswap _ _ => none
  | .unary _ _ _ => none
  | .imul _ _ _ => none
  | .mul _ _ => none
  | .shift _ _ _ _ => none
  | .cxd _ => none
  | .cxe _ => none
  | .div _ _ _ => none
  | .cmov _ _ _ _ => none
  | .setcc _ _ => none
  | .jmp _ => none
  | .jmp8 _ => none
  | .jcc _ _ => none
  | .jcc8 _ _ => none
  | .call _ => none
  | .ret => none
  | .leave => none
  | .endbr64 => none
  | .ud2 => none
  | .bitcount _ _ _ _ => none

/-- The access of an operand: address and byte count. -/
def Opd.access (w : Nat) (σ : State) (next : Word) : Opd → Option (Word × Nat)
  | .mem m _ => some (m.addr σ next, w / 8)
  | _ => none

/-- The memory access of a form. -/
def Form.access (σ : State) (next : Word) : Form → Option (Word × Nat)
  | .flag F => match F.a.access F.w σ next with
    | some p => some p
    | none => F.b.access F.w σ next
  | .load L => L.src.access L.w σ next
  | .nop => none

/-- The methods of the width-generic forms, RIP update included. -/
def emitForm (W : Win) (i : Silmaril.X86.Ext.Instr) (len : Nat) : Option (List Instr) :=
  (formOf i).map fun F => F.code W ++ nextCode len

/-- **The methods with memory**: the memory and stack forms, everything `emitX` handles, then
the width-generic forms. -/
def emitM (W : Win) (i : Silmaril.X86.Ext.Instr) (len : Nat) : Option (List Instr) :=
  match emitMem W i len with
  | some c => some c
  | none => match emitX i len with
    | some c => some c
    | none => emitForm W i len

/-- The access of `mov r/m, r`. -/
def accessMov (sz : Sz) (dst : RM) (σ : State) (next : Word) : Option Word :=
  match sz, dst with
  | .q, .mem m => some (m.addr σ next)
  | _, _ => none

/-- The 8-byte memory access of a memory or stack form, if any (its address). -/
def accessMem (i : Silmaril.X86.Ext.Instr) (σ : State) (len : Nat) : Option Word :=
  match i with
  | .load sz _ m => if sz = .q then some (m.addr σ (σ.rip + BitVec.ofNat 64 len)) else none
  | .mov sz dst _ => accessMov sz dst σ (σ.rip + BitVec.ofNat 64 len)
  | .push _ => some (σ.read .rsp - 8#64)
  | .call _ => some (σ.read .rsp - 8#64)
  | .pop _ => some (σ.read .rsp)
  | .ret => some (σ.read .rsp)
  | .movI _ _ _ => none
  | .movI16 _ _ => none
  | .mov8 _ _ => none
  | .movI8 _ _ => none
  | .movI32 _ _ => none
  | .movabs _ _ => none
  | .store _ _ _ => none
  | .movx _ _ _ _ _ => none
  | .movsxd _ _ => none
  | .lea _ _ _ => none
  | .alu _ _ _ _ => none
  | .aluR _ _ _ _ => none
  | .aluI _ _ _ _ => none
  | .aluI8 _ _ _ _ => none
  | .aluA _ _ _ => none
  | .test _ _ _ => none
  | .test8 _ _ => none
  | .testI8 _ _ => none
  | .testA8 _ => none
  | .cmpI8 _ _ => none
  | .cmpA8 _ => none
  | .testA _ _ => none
  | .incdec _ _ _ => none
  | .pushRM _ => none
  | .bswap _ _ => none
  | .unary _ _ _ => none
  | .imul _ _ _ => none
  | .mul _ _ => none
  | .shift _ _ _ _ => none
  | .cxd _ => none
  | .cxe _ => none
  | .div _ _ _ => none
  | .cmov _ _ _ _ => none
  | .setcc _ _ => none
  | .jmp _ => none
  | .jmp8 _ => none
  | .jcc _ _ => none
  | .jcc8 _ _ => none
  | .leave => none
  | .endbr64 => none
  | .ud2 => none
  | .nop _ => none
  | .bitcount _ _ _ _ => none

/-- **The memory access of an instruction** (address and byte count), if any. -/
def access (i : Silmaril.X86.Ext.Instr) (σ : State) (len : Nat) : Option (Word × Nat) :=
  match accessMem i σ len with
  | some a => some (a, 8)
  | none => (formOf i).bind (·.access σ (σ.rip + BitVec.ofNat 64 len))

/-! ## Programs with memory -/

open Silmaril.Sim.X86.Loop (XTab lookupI) in
/-- A run of `k` instructions of the table from `σ`, `mem`, every memory access inside the window
(and every write), ending where RIP leaves the table. -/
inductive XRunM (tab : XTab) (W : Win) :
    Nat → State → Silmaril.Process.Memory → State → Silmaril.Process.Memory → Prop
  | done {σ : State} {mem : Silmaril.Process.Memory} : lookupI tab σ.rip = none →
      XRunM tab W 0 σ mem σ mem
  | step {σ σ₁ σ' : State} {mem mem₁ mem' : Silmaril.Process.Memory} {i : Silmaril.X86.Ext.Instr}
      {n k : Nat} : lookupI tab σ.rip = some (i, n) →
      Silmaril.X86.Ext.exec i σ mem n = .ok σ₁ mem₁ →
      (∀ a k, access i σ n = some (a, k) → W.HoldsK k a) → mem.WritesWithin mem₁ W.Mem →
      XRunM tab W k σ₁ mem₁ σ' mem' → XRunM tab W (k + 1) σ mem σ' mem'

open Silmaril.Sim.X86.Loop (XTab) in
/-- Every instruction of the table has a method with memory. -/
def SupportedM (W : Win) (tab : XTab) : Prop := ∀ e ∈ tab, (emitM W e.2.1 e.2.2).isSome

open Silmaril.Sim.X86.Loop (XTab) in
/-- The table of method code with memory. -/
def compileTabM (W : Win) (tab : XTab) : List (Word × List Instr) :=
  tab.map fun e => (e.1, (emitM W e.2.1 e.2.2).getD [])

/-- The window bytes of an x86 memory, as Wasm bytes. -/
noncomputable def winBytes (mem : Silmaril.Process.Memory) (W : Win) : ByteArray :=
  ⟨((List.range W.size).map fun k =>
    UInt8.ofBitVec ((mem.bytes.get? (W.lo.toNat + k)).getD 0)).toArray⟩

/-- The window is readable, writable and backed in `mem`, within the Wasm address range. -/
def WinOK (mem : Silmaril.Process.Memory) (W : Win) : Prop :=
  W.size ≤ 2 ^ 32 ∧ W.lo.toNat + W.size ≤ 2 ^ 64 ∧
    ∀ k < W.size, mem.permits .read (W.lo.toNat + k) = true ∧
      (W.rw = true → mem.permits .write (W.lo.toNat + k) = true) ∧
      (mem.bytes.get? (W.lo.toNat + k)).isSome

/-- **The Wasm problem** of a dispatcher with memory: from every store holding registers `R`,
RIP `w` and Wasm memory `B` (at least the window's size) with `Pre R w B`, every run that stops
falls through with registers `R'` and RIP `w'` satisfying `Post R w B R' w'`. -/
def LProblemM (P : Profile) (host : HostSemantics H) (W : Win) (code : List Instr)
    (Pre : (Reg → Word) → Word → ByteArray → Prop)
    (Post : (Reg → Word) → Word → ByteArray → (Reg → Word) → Word → Prop) : Prop :=
  ∀ (s : Store H) (f : Frame) (R : Reg → Word) (w : Word) (B : ByteArray), GRegs s f R →
    gval s f .rip = some (Val.i64 w) → wbytes s f = some B → W.size ≤ B.size → Pre R w B →
    Silmaril.Wasm.Logic.Hoare.HWP P host s f (expression code) fun s' f' o => o = .normal [] ∧
      ∀ (R' : Reg → Word) (w' : Word), (∀ r, gval s' f' (.reg r) = some (Val.i64 (R' r))) →
        gval s' f' .rip = some (Val.i64 w') → Post R w B R' w'

open Silmaril.Sim.X86.Loop (XTab) in
/-- **The x86 problem** with memory: every window-respecting run from a state with `Pre` (on
its registers, RIP and window bytes) ends with `Post`. -/
def XLProblemM (tab : XTab) (W : Win) (Pre : (Reg → Word) → Word → ByteArray → Prop)
    (Post : (Reg → Word) → Word → ByteArray → (Reg → Word) → Word → Prop) : Prop :=
  ∀ (σ σ' : State) (mem mem' : Silmaril.Process.Memory) (k : Nat), WinOK mem W →
    Pre σ.read σ.rip (winBytes mem W) → XRunM tab W k σ mem σ' mem' →
    Post σ.read σ.rip (winBytes mem W) σ'.read σ'.rip

end Silmaril.Sim.X86.GM
