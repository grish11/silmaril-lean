module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestOpen

/-! # GNU `sha256sum`: the statement of `digest_file` on a readable file

`Task.digestFile E R W b lb kb`: from `digest_file (name, bin_result, missing)`'s entry
(`0x6a40`) on a file that opens and reads without error, every run returns (System V) with the
32-byte SHA-256 of the file's contents at `bin_result`, `*missing = false`, `eax = 1` (true),
the caller's data other than those two objects, the other streams, the library state, `fsBase`
and the stack permissions as they were. Proof in progress (D): prologue to `*missing = false`
(`sha_digest_pro`, `sha_digest_mid`) and up to `fopen_safer` (`sha_digest_head`, partial).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

/-- **The read loop's invariant** at `0x6b27`: the context holds `absorbed`, the buffer the
`pending` bytes, the stream the rest. -/
structure DigInv (E : Env) (R : ShaRep) (W : World) (b lb kb : Word) (X : Nat → Prop) (s u : PState) (F buf g : Word) (z : BitVec 32)
    (data absorbed pending : List Byte) (st : St) : Prop where
  hX : ∀ x, X x → x + 1024 < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x
  lo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat
  al : (s.m.core.read .rsp).toNat % 16 = 8
  body : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) X
  rbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rbx : u.m.core.read .rbx = F
  r12 : u.m.core.read .r12 = buf
  r13 : u.m.core.read .r13 = 0x8000#64
  r14 : BitVec.setWidth 32 (u.m.core.read .r14) = z
  r15 : u.m.core.read .r15 = BitVec.ofNat 64 pending.length
  plen : pending.length ≤ 0x8000
  sbin : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 200) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rsi])
  sctx : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 192) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rsp - 184#64])
  sg : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  miss : u.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  rdxhi : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat
  holds : R.holds u.m.memory (s.m.core.read .rsp - 184#64) absorbed
  bufrd : u.m.memory.readBytes buf.toNat pending.length = some pending
  bufr : u.m.memory.Permitted .read buf.toNat 0x8048
  bufw : u.m.memory.Permitted .write buf.toNat 0x8048
  bufok : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 →
    ¬ W.Kept a ∧ a + 0x100000 < (s.m.core.read .rsp).toNat ∧ a < E.S.lo ∧ ¬ E.S.priv u.m.memory a
  file : E.S.file u.m.memory F st
  stok : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧
    (st.eof = true → st.rd = [])
  data : absorbed ++ pending ++ st.rd = data
  g : u.g = s.g.withBlk buf.toNat 0x8048
  others : ∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file u.m.memory f st'
  pdx : PermDX s u.m.memory
  /-- the library variables of the entry are kept -/
  lib : LibK E W s.m.memory u.m.memory
  /-- the buffer holds no library variable of the entry (it was the library's when `malloc` returned it) -/
  buffr : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → ¬ LibV E W s.m.memory a


/-- What `digest_file`'s caller provides. -/
structure DigEntry (E : Env) (W : World) (b lb kb : Word) (s : PState) (p : List Byte)
    (data : Silmaril.Apps.Sha256sum.Bytes) (g : Word) : Prop where
  rip : s.m.core.rip = b + 0x6a40#64
  abi : AbiEntry s.m.core s.m.memory
  room : Room W s.m.memory (s.m.core.read .rsp) 1024
  lo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat
  done : s.g.done = none
  mem : ShaMemCD b lb kb s.m.memory
  /-- the file name, a C string in the program's kept memory (an argument) -/
  name : CStr s.m.memory (s.m.core.read .rdi) p
  namek : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j)
  /-- not `-` (standard input) -/
  notDash : ∀ c0, s.m.memory.readBytes (s.m.core.read .rdi).toNat 1 = some [c0] → c0 ≠ 0x2d#8
  /-- the file opens and reads without error -/
  file : E.fs (toSpec p) = .ok data
  /-- `bin_result` (32 bytes) and `missing` (1 byte): the caller's, writable and readable -/
  outs : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a
  binw : s.m.memory.Permitted .write (s.m.core.read .rsi).toNat 32
  binr : s.m.memory.Permitted .read (s.m.core.read .rsi).toNat 32
  missw : s.m.memory.Permitted .write (s.m.core.read .rdx).toNat 1
  missr : s.m.memory.Permitted .read (s.m.core.read .rdx).toNat 1
  /-- `bin_result` and `missing` are different objects -/
  disj : (s.m.core.read .rsi).toNat + 32 ≤ (s.m.core.read .rdx).toNat ∨
    (s.m.core.read .rdx).toNat + 1 ≤ (s.m.core.read .rsi).toNat
  /-- the stack guard `%fs:0x28`, in the program's kept memory -/
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  /-- the library's resources for one `fopen` and one `malloc (BLOCKSIZE + 72)` -/
  res : InMain s.g ∧ s.g.files < E.maxOpen ∧ data.length ≤ E.maxFile ∧ s.g.allocs < E.maxAllocs ∧
    s.g.heap + 0x8048 ≤ E.maxHeap

/-- What `digest_file` guarantees on return (for the entry state `s` with the library state after its
`fopen` and `malloc`). -/
structure DigExit (E : Env) (W : World) (s t : PState) (data : Silmaril.Apps.Sha256sum.Bytes) : Prop where
  abi : AbiReturn s.m.core s.m.memory t.m.core
  keep : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ DX s a) s.m.memory t.m.memory
  digest : t.m.memory.readBytes (s.m.core.read .rsi).toNat 32 = some (sha256 (ofSpec data))
  missing : t.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  ok : low32 (t.m.core.read .rax) = 1#32
  /-- the library state as given (its live blocks aside: `free` took the buffer back) -/
  g : t.g = { s.g with blocks := t.g.blocks }
  streams : ∀ f st, E.S.file s.m.memory f st → E.S.file t.m.memory f st
  fs : t.m.core.fsBase = s.m.core.fsBase
  perm : PermKept s t.m.memory
  /-- the permissions of `bin_result` and `missing` are as at entry -/
  permDX : PermDX s t.m.memory
  /-- the library variables (`program_invocation_name`, …) are kept -/
  lib : LibK E W s.m.memory t.m.memory

/-- **`digest_file` on a readable file** (the open goal; D proves it). -/
def Task.digestFile (E : Env) (R : ShaRep) (W : World) (b lb kb : Word) : Prop :=
  DigImps E R W b lb kb → ∀ (Q : PState → Prop) (s : PState) (p : List Byte)
    (data : Silmaril.Apps.Sha256sum.Bytes) (g : Word), DigEntry E W b lb kb s p data g →
    (∀ t, DigExit E W { s with g := s.g.opened.alloc 0x8048 } t data → MustQ W Q t) → MustQ W Q s

end Silmaril.Elf.Link.Dyn.Sha256sum
