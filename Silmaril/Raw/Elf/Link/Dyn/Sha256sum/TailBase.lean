module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CertMem
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainGetopt
public import Silmaril.Elf.Link.Dyn.Cert.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Cert.Frame

/-! # GNU `sha256sum`: tools for `main`'s tail (block certificates on the pieces of `main`)

* `ShaMainAll.keepW`: the code of `main` (`CertMainAll`'s pieces, loaded and not writable)
  survives anything that keeps the image below the option variables.
* `must_piece`: run a certified block of a piece of `main`.
* `exec_aluR8_mem`: `op al, byte [mem]` (the two byte-ALU forms the lifter leaves as gaps).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert

theorem loaded_keepW {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory} (h : Keeps (ImgW b) m m')
    {off : Nat} {code : List Byte} (hr : off + code.length ≤ 0xa160)
    (hl : Loaded m (b + BitVec.ofNat 64 off) code) : Loaded m' (b + BitVec.ofNat 64 off) code := by
  unfold Loaded Memory.fetchBytes at hl ⊢
  rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  exact hl

theorem codeRO_keepW {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory} (h : Keeps (ImgW b) m m')
    {off : Nat} {code : List Byte} (hr : off + code.length ≤ 0xa160)
    (hc : CodeRO m (b + BitVec.ofNat 64 off) code) : CodeRO m' (b + BitVec.ofNat 64 off) code := by
  intro k hk
  have e : (b + BitVec.ofNat 64 off).toNat = b.toNat + off := addr_toNat (by omega)
  have := hc k hk
  rw [e] at this ⊢
  rw [(h _ ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩).2]
  exact this

theorem mainAll_lens : mainAll0Text.length = 0x1fd ∧ mainAll1Text.length = 0x1da ∧
    mainAll2Text.length = 0x1f5 ∧ mainAll3Text.length = 0x1f9 ∧ mainAll4Text.length = 0x1f9 ∧
    mainAll5Text.length = 0x1f7 ∧ mainAll6Text.length = 0x1e7 ∧ mainAll7Text.length = 0x1f8 ∧
    mainAll8Text.length = 0x1fd ∧ mainAll9Text.length = 0x155 := by
  decide +kernel

theorem ShaMainAll.keepW {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMainAll b m) (h : Keeps (ImgW b) m m') : ShaMainAll b m' := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := mainAll_lens
  exact ⟨loaded_keepW hb h (by omega) hm.ld0, codeRO_keepW hb h (by omega) hm.ro0,
    loaded_keepW hb h (by omega) hm.ld1, codeRO_keepW hb h (by omega) hm.ro1,
    loaded_keepW hb h (by omega) hm.ld2, codeRO_keepW hb h (by omega) hm.ro2,
    loaded_keepW hb h (by omega) hm.ld3, codeRO_keepW hb h (by omega) hm.ro3,
    loaded_keepW hb h (by omega) hm.ld4, codeRO_keepW hb h (by omega) hm.ro4,
    loaded_keepW hb h (by omega) hm.ld5, codeRO_keepW hb h (by omega) hm.ro5,
    loaded_keepW hb h (by omega) hm.ld6, codeRO_keepW hb h (by omega) hm.ro6,
    loaded_keepW hb h (by omega) hm.ld7, codeRO_keepW hb h (by omega) hm.ro7,
    loaded_keepW hb h (by omega) hm.ld8, codeRO_keepW hb h (by omega) hm.ro8,
    loaded_keepW hb h (by omega) hm.ld9, codeRO_keepW hb h (by omega) hm.ro9⟩

theorem loadN_of_rb {m : Memory} {a : Word} {k : Nat} {l : List Byte}
    (h : m.readBytes a.toNat k = some l) :
    loadN m a k = some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue l)) := by
  simp [loadN, h]

@[simp] theorem post_fs (B : Silmaril.X86.Bir9.Block) (s : PState) (env : Silmaril.X86.Bir9.Env) :
    (post B s env).m.core.fsBase = env.s0.fsBase := rfl
@[simp] theorem post_g (B : Silmaril.X86.Bir9.Block) (s : PState) (env : Silmaril.X86.Bir9.Env) :
    (post B s env).g = s.g := rfl
@[simp] theorem post_mem (B : Silmaril.X86.Bir9.Block) (s : PState) (env : Silmaril.X86.Bir9.Env) :
    (post B s env).m.memory = env.mem := rfl
@[simp] theorem env_push_s0 (env : Silmaril.X86.Bir9.Env) (v : Word) : (env.push v).s0 = env.s0 := rfl
@[simp] theorem env_push_mem (env : Silmaril.X86.Bir9.Env) (v : Word) : (env.push v).mem = env.mem := rfl
@[simp] theorem env0_s0 (m : MState) : (env0 m).s0 = m.core := rfl
@[simp] theorem env0_mem (m : MState) : (env0 m).mem = m.memory := rfl

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]
theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-- `eax = !ok` at `main`'s end, for `ok = 1` (only the low byte of `rdx` matters). -/
theorem low8_xor1 (x : BitVec 64) (hdx : BitVec.setWidth 8 x = 1#8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 8
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 1#64)))))))) =
    0#32 := by
  have h8 : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 1#64)))) = BitVec.setWidth 8 x ^^^ 1#8 := by
    ext i hi
    simp [BitVec.getElem_setWidth]
  rw [h8, hdx]
  decide

/-- `eax = !ok` at `main`'s end, for `ok ∈ {0, 1}` (K8): 0 if `ok = 1`, else 1. -/
theorem low8_xorB (x : BitVec 64) {d : BitVec 8} (hdx : BitVec.setWidth 8 x = d) (hd : d = 0#8 ∨ d = 1#8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 8
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 1#64)))))))) =
    if d = 1#8 then 0#32 else 1#32 := by
  have h8 : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 1#64)))) = BitVec.setWidth 8 x ^^^ 1#8 := by
    ext i hi
    simp [BitVec.getElem_setWidth]
  rw [h8, hdx]
  rcases hd with rfl | rfl <;> decide

/-- Run a certified block of a piece `code` of `main` at `b + cb`. -/
theorem must_piece {W : World} {Q : PState → Prop} {s : PState} {b : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hd : s.g.done = none) {cb : Nat} {code : List Byte}
    (hlen : cb + code.length ≤ 0xa188) (hl : Loaded s.m.memory (b + BitVec.ofNat 64 cb) code)
    (hro : CodeRO s.m.memory (b + BitVec.ofNat 64 cb) code) (B : Blk) (hok : B.ok code = true)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 (cb + B.off))
    (h : Wp B.b.stmts (env0 s.m) fun env => MustQ W Q (post B.b s env)) : MustQ W Q s :=
  must_blk_at B hok hd (fun n hn => sha_in' I hb (by omega)) hl hro hrip h

/-- A near `call rel32`: the return address pushed, control at the target. -/
theorem exec_call (rel : BitVec 32) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read .rsp - 8#64).toNat 8) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.call rel))) c m l =
      .ok { c.write .rsp (c.read .rsp - 8#64) with rip := c.rip + BitVec.ofNat 64 l + rel.signExtend 64 }
        (pushMem m (c.read .rsp) (c.rip + BitVec.ofNat 64 l)) := by
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, pushWord_mem h]

/-- `op al, byte [M]` (`or`/`and`/… with a memory source). -/
theorem exec_aluR8_mem {op : Silmaril.X86.AluOp} (hop : op ≠ .cmp) (M : Silmaril.X86.Ext.Mem) (c : State)
    (m : Memory) (l : Nat) {y : Word}
    (h : loadN m (M.addr c (c.rip + BitVec.ofNat 64 l)) 1 = some y) :
    Silmaril.X86.Ext9.exec (.ext8 (.new (.aluR op (.low .rax) (.mem M)))) c m l =
      .ok { (Silmaril.X86.Ext8.BReg.low .rax).write c
          (Silmaril.X86.Ext.AluOp.resultN op ((Silmaril.X86.Ext8.BReg.low .rax).read c) (y.setWidth 8)) with
        flags := Silmaril.X86.Ext.AluOp.flagsN op ((Silmaril.X86.Ext8.BReg.low .rax).read c) (y.setWidth 8),
        rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.RM8.read, h,
    Silmaril.X86.Ext8.alu8, hop, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext.retire]

end Silmaril.Elf.Link.Dyn.Sha256sum
