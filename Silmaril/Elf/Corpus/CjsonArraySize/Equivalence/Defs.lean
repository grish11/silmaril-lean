module
public import Silmaril.Elf.Corpus.CjsonArraySize.Thms
public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.Bytes
/-! Actual bounded loop-pair obligation; UNPROVED. Function excerpt placement, not whole-ELF loading.
No safety, return-value equality or source-refinement assumption is an entry law.
Finite allocated acyclic lists only; no universal nondeterministic termination claim. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArraySize.Equivalence
open Silmaril.Project.Shapes
open Silmaril.X86 (MState FnContract)
def leftCode : List (BitVec 8) := [0x55,0x48,0x89,0xe5,0x48,0x89,0x7d,0xe8,0x48,0xc7,0x45,0xf0,0x0,0x0,0x0,0x0,0x48,0xc7,0x45,0xf8,0x0,0x0,0x0,0x0,0x48,0x83,0x7d,0xe8,0x0,0x75,0x7,0xb8,0x0,0x0,0x0,0x0,0xeb,0x29,0x48,0x8b,0x45,0xe8,0x48,0x8b,0x40,0x10,0x48,0x89,0x45,0xf0,0xeb,0x10,0x48,0x83,0x45,0xf8,0x1,0x48,0x8b,0x45,0xf0,0x48,0x8b,0x0,0x48,0x89,0x45,0xf0,0x48,0x83,0x7d,0xf0,0x0,0x75,0xe9,0x48,0x8b,0x45,0xf8,0x5d,0xc3]
def left : Silmaril.Project.Shapes.Placement := ⟨21378, leftCode, 0⟩
def right : Silmaril.Project.Shapes.Placement := ⟨Silmaril.Elf.Corpus.CjsonArraySize.address, Silmaril.Elf.Corpus.CjsonArraySize.code, 0⟩
structure Input where
  isNull : Bool
  length : Fin 65
  base : Nat
  payload : Nat → BitVec 8
  aligned : base % 8 = 0
  lower : 65536 ≤ base
  upper : base + 65*64 < 2^47

def heap (i : Input) (index : Nat) := i.base + 64*index
def root (i : Input) : BitVec 64 := if i.isNull then 0 else BitVec.ofNat 64 i.base
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[.pointer], some .int32⟩
def heapBytes (i : Input) (offset : Nat) : BitVec 8 :=
  let index := offset / 64
  let fieldOffset := offset % 64
  let first : BitVec 64 := BitVec.ofNat 64 (if i.length.val == 0 then 0 else heap i 1)
  let next : BitVec 64 := BitVec.ofNat 64 (if index < i.length.val then heap i (index+1) else 0)
  if index == 0 && 16 ≤ fieldOffset && fieldOffset < 24 then
    (first >>> ((fieldOffset-16)*8)).setWidth 8
  else if 0 < index && fieldOffset < 8 then
    (next >>> (fieldOffset*8)).setWidth 8
  else i.payload offset

def heapMatches (i : Input) (m : MState) : Bool :=
  (List.range ((i.length.val+1)*64)).all fun offset =>
    m.memory.bytes.get? (i.base+offset) == some (heapBytes i offset)

def initial (i : Input) (a b : MState) : Prop :=
  SysV.CallEntry left signature 32 (.cons (root i) .nil) a ∧
  SysV.CallEntry right signature 0 (.cons (root i) .nil) b ∧
  a.memory = b.memory ∧
  (∀ r, a.core.read r = b.core.read r) ∧
  a.core.flags = b.core.flags ∧
  Silmaril.X86.Open.isa.live a ∧ Silmaril.X86.Open.isa.live b ∧
  FnContract.AbiEntry a.core a.memory ∧ FnContract.AbiEntry b.core b.memory ∧
  heap i (i.length.val+1) + 65536 < SysV.rspOf a ∧
  a.memory.Permitted .read i.base ((i.length.val+1)*64) ∧
  heapMatches i a = true

/-- Exact per-side frame and ABI, complete mapping/byte preservation supplied
by WritesWithin; actual low32 returns compared directly, without an expected count. -/
def outcome (a b x y : MState) : Prop :=
  FnContract.AbiReturn a.core a.memory x.core ∧
  FnContract.AbiReturn b.core b.memory y.core ∧
  a.memory.WritesWithin x.memory (SysV.StackBelow a 32) ∧
  b.memory.WritesWithin y.memory (SysV.StackBelow b 0) ∧
  (x.core.read .rax).setWidth 32 = (y.core.read .rax).setWidth 32 ∧
  (∀ address, ¬ SysV.StackBelow a 32 address →
    x.memory.bytes.get? address = y.memory.bytes.get? address) ∧
  x.memory.regions = y.memory.regions

/-- Entry existence for EVERY address/payload/list instance prevents empty contexts.
First-return existence and all first-return outcomes are demanded, not assumed. -/
@[problem "silmaril.corpus.cjson.get_array_size.optimization_equivalence"
  (title := "Actual cJSON finite-list traversal O0/O2 contextual binary equivalence")]
def Task.optimization : Prop :=
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.F 21378 leftCode ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1.F right.base.toNat right.code ∧
  (∀ i, ∃ a b, initial i a b) ∧
  (∀ i a b, initial i a b →
    (∃ x, FnContract.FirstReturn Silmaril.X86.Open.isa a x) ∧
    (∃ y, FnContract.FirstReturn Silmaril.X86.Open.isa b y) ∧
    ∀ x y, FnContract.FirstReturn Silmaril.X86.Open.isa a x →
      FnContract.FirstReturn Silmaril.X86.Open.isa b y → outcome a b x y)
end Silmaril.Elf.Corpus.CjsonArraySize.Equivalence
