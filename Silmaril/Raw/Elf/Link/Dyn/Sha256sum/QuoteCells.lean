module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteFrame
public import Silmaril.Raw.Elf.Link.Dyn.Cert.Frame

/-! # GNU `sha256sum`: stack cells of `quotef`'s run

Tools for the machine runs of `Task.quotePro` and `Task.quoteExit`:

* `Cells M R L`: the cells `(d, k, v)` of `L` (the `k`-byte value at `R - d` is `v`), with
  `Cells.store` (a store at `R - d` adds its cell and drops the cells it overlaps),
  `Cells.keep` (a frame keeps them), `Cells.get`;
* `QC`: a code chunk of `sha256sum` loaded, read-only and in the image (`ShaRO.qc`);
* `bsub_sub`, `bsub_add`: offsets below `R` in normal form `R - BitVec.ofNat 64 d`;
* `OutStk`: outside the page below `R` (`¬ QW` and `errno` are), `keeps_outStk`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn (addr_toNat plainOk slotOk)

/-! ## Offsets below `R` -/

theorem bsub_sub (R : Word) (a c : Nat) :
    R - BitVec.ofNat 64 a - BitVec.ofNat 64 c = R - BitVec.ofNat 64 (a + c) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem bsub_add (R : Word) (a c : Nat) :
    R - BitVec.ofNat 64 a + BitVec.ofNat 64 c = R - BitVec.ofNat 64 ((a + (2 ^ 64 - c % 2 ^ 64)) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 := R.isLt
  have : c % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  omega

theorem bsub_toNat {R : Word} {d : Nat} (h : d ≤ R.toNat) : (R - BitVec.ofNat 64 d).toNat = R.toNat - d :=
  sub_toNat h (by have := R.isLt; omega)

/-! ## Cells -/

/-- The cells `(d, k, v)` of `L`: the `k`-byte value at `R - d` is `v` (`d ≤ R`). -/
def Cells (M : Memory) (R : Word) (L : List (Nat × Nat × Word)) : Prop :=
  ∀ c ∈ L, c.1 ≤ R.toNat ∧ loadN M (R - BitVec.ofNat 64 c.1) c.2.1 = some c.2.2

/-- The cell `c` misses a store of `k` bytes at `R - d`. -/
def cdisj (d k : Nat) (c : Nat × Nat × Word) : Bool := decide (d + c.2.1 ≤ c.1) || decide (c.1 + k ≤ d)

theorem Cells.nil (M : Memory) (R : Word) : Cells M R [] := by intro c h; cases h

theorem Cells.get {M : Memory} {R : Word} {L : List (Nat × Nat × Word)} (h : Cells M R L) {d k : Nat}
    {v : Word} (hm : (d, k, v) ∈ L) : loadN M (R - BitVec.ofNat 64 d) k = some v := (h _ hm).2

theorem Cells.sub {M : Memory} {R : Word} {L L' : List (Nat × Nat × Word)} (h : Cells M R L)
    (hs : ∀ c ∈ L', c ∈ L) : Cells M R L' := fun c hc => h c (hs c hc)

theorem Cells.cons {M : Memory} {R : Word} {L : List (Nat × Nat × Word)} (h : Cells M R L) {d k : Nat}
    {v : Word} (hd : d ≤ R.toNat) (hl : loadN M (R - BitVec.ofNat 64 d) k = some v) :
    Cells M R ((d, k, v) :: L) := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact ⟨hd, hl⟩
  · exact h c hc

theorem Cells.append {M : Memory} {R : Word} {L L' : List (Nat × Nat × Word)} (h : Cells M R L)
    (h' : Cells M R L') : Cells M R (L ++ L') := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact h c hc
  · exact h' c hc

theorem loadN_storeMem_same {M : Memory} {a v : Word} {k : Nat} (hr : M.Permitted .read a.toNat k)
    (hv : v.toNat < 2 ^ (8 * k)) : loadN (storeMem M a k v) a k = some v := by
  simp only [loadN, storeMem_read hr, Option.map_some, Silmaril.X86.Ext.leValue_leBytes,
    Nat.mod_eq_of_lt hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem loadN_storeMem_sub {M : Memory} {a A v : Word} {k j n : Nat} (hr : M.Permitted .read a.toNat k)
    (hA : A.toNat = a.toNat + j) (hj : j < k) (hjn : j + n ≤ k) :
    loadN (storeMem M a k v) A n =
      some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue (((Silmaril.X86.Ext.leBytes v k).drop j).take n))) := by
  have h := Silmaril.Process.Memory.readBytes_sub_range (storeMem_read (v := v) hr) hj hjn
  simp only [loadN, hA, h, Option.map_some]

theorem Cells.store {M : Memory} {R : Word} {L : List (Nat × Nat × Word)} (h : Cells M R L) {d k : Nat}
    {v : Word} (hd : d ≤ R.toNat) (hr : M.Permitted .read (R.toNat - d) k) (hv : v.toNat < 2 ^ (8 * k)) :
    Cells (storeMem M (R - BitVec.ofNat 64 d) k v) R ((d, k, v) :: L.filter (cdisj d k)) := by
  have ht := bsub_toNat hd
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact ⟨hd, loadN_storeMem_same (by rw [ht]; exact hr) hv⟩
  · rw [List.mem_filter] at hc
    obtain ⟨hc, hdj⟩ := hc
    obtain ⟨hc1, hc2⟩ := h c hc
    refine ⟨hc1, ?_⟩
    rw [loadN_storeMem_ne ?_]
    · exact hc2
    · rw [ht, bsub_toNat hc1]
      simp only [cdisj, Bool.or_eq_true, decide_eq_true_eq] at hdj
      omega

theorem Cells.keep {M M' : Memory} {R : Word} {L : List (Nat × Nat × Word)} (h : Cells M R L)
    {P : Nat → Prop} (hk : Keeps P M M') (hP : ∀ c ∈ L, ∀ j, j < c.2.1 → P (R.toNat - c.1 + j)) :
    Cells M' R L := by
  intro c hc
  obtain ⟨h1, h2⟩ := h c hc
  refine ⟨h1, ?_⟩
  rw [hk.loadN (fun j hj => by rw [bsub_toNat h1]; exact hP c hc j hj)]
  exact h2

/-- The cells of `L` lie in `[R - D, R + 8)`. -/
def CellsIn (D : Nat) (L : List (Nat × Nat × Word)) : Bool :=
  L.all fun c => decide (c.1 ≤ D) && decide (c.2.1 ≤ c.1 + 8)

theorem Cells.keepFrom {M M' : Memory} {R : Word} {L : List (Nat × Nat × Word)} (h : Cells M R L)
    {D : Nat} (hD : CellsIn D L = true) {P : Nat → Prop}
    (hk : Keeps P M M') (hP : ∀ a, R.toNat - D ≤ a → a < R.toNat + 8 → P a) : Cells M' R L :=
  h.keep hk fun c hc j hj => by
    have := List.all_eq_true.1 hD c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have h1 := (h c hc).1
    exact hP _ (by omega) (by omega)

theorem room_permR {W : World} {M : Memory} {R : Word} (hroom : Room W M R 2048) {acc : Access}
    (hacc : acc = .read ∨ acc = .write) {d k : Nat} (hd : d ≤ 2048) (hk : k ≤ d + 8) :
    M.Permitted acc (R - BitVec.ofNat 64 d).toNat k := by
  have := hroom.1
  rw [bsub_toNat (by omega)]
  exact room_perm hroom hacc (by omega) (by omega)

theorem pushMem_eq (m : Memory) (sp v : Word) : pushMem m sp v = storeMem m (sp - 8#64) 8 v := by
  simp only [pushMem, storeMem, Silmaril.X86.Ext.leBytes_eight]

/-- New cells of a store, and the old ones it misses. -/
theorem Cells.storeAdd {M : Memory} {R : Word} {L N : List (Nat × Nat × Word)} (h : Cells M R L) {d k : Nat}
    {v : Word} (hd : d ≤ R.toNat) (hN : Cells (storeMem M (R - BitVec.ofNat 64 d) k v) R N) :
    Cells (storeMem M (R - BitVec.ofNat 64 d) k v) R (N ++ L.filter (cdisj d k)) := by
  have ht := bsub_toNat hd
  refine hN.append fun c hc => ?_
  rw [List.mem_filter] at hc
  obtain ⟨hc, hdj⟩ := hc
  obtain ⟨hc1, hc2⟩ := h c hc
  refine ⟨hc1, ?_⟩
  rw [loadN_storeMem_ne ?_]
  · exact hc2
  · rw [ht, bsub_toNat hc1]
    simp only [cdisj, Bool.or_eq_true, decide_eq_true_eq] at hdj
    omega

/-- A sub-cell of a store at `R - d`: the bytes `[j, j + n)` of the stored value. -/
theorem loadN_storeR {M : Memory} {R v : Word} {d k j n : Nat} (hd : d ≤ R.toNat)
    (hr : M.Permitted .read (R.toNat - d) k) (hj : j < k) (hjn : j + n ≤ k) (hjd : j ≤ d) :
    loadN (storeMem M (R - BitVec.ofNat 64 d) k v) (R - BitVec.ofNat 64 (d - j)) n =
      some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue (((Silmaril.X86.Ext.leBytes v k).drop j).take n))) :=
  loadN_storeMem_sub (by rw [bsub_toNat hd]; exact hr) (by rw [bsub_toNat (by omega), bsub_toNat hd]; omega) hj hjn

/-- A store into the stack page keeps `ShaRO`. -/
theorem ShaRO.storeR {W : World} {b lb : Word} {M : Memory} (h : ShaRO b lb M) (I : W.InImage = ShaImg b)
    {R : Word} (hroom : Room W M R 2048) {d k : Nat} {v : Word} (hd : d ≤ 2048) (hk : k ≤ d) :
    ShaRO b lb (storeMem M (R - BitVec.ofNat 64 d) k v) := by
  have := hroom.1
  refine h.keep (storeMem_keeps fun x hx => ?_)
  have hi : W.InImage x := by rw [I]; unfold ShaImg; omega
  have := room_store_img hroom (a := R - BitVec.ofNat 64 d) (k := k) (by rw [bsub_toNat (by omega)]; omega)
    (by rw [bsub_toNat (by omega)]; omega) x hi
  exact this

theorem readBytes_of_loadN' {m : Memory} {a v : Word} {k : Nat} (h : loadN m a k = some v) (hk : k ≤ 8) :
    m.readBytes a.toNat k = some (Silmaril.X86.Ext.leBytes v k) := by
  unfold loadN at h
  cases hr : m.readBytes a.toNat k with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact hr.symm.trans (Silmaril.X86.Ext.holdsLE_of_readBytes hr hk)

theorem loadN_lt {m : Memory} {a v : Word} {k : Nat} (h : loadN m a k = some v) :
    v.toNat < 2 ^ (8 * k) := by
  unfold loadN at h
  cases hr : m.readBytes a.toNat k with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hl : bs.length = k := Silmaril.Process.Memory.readWith_length hr
    have := Silmaril.X86.Ext.leValue_lt bs
    rw [hl] at this
    rw [BitVec.toNat_ofNat]
    exact lt_of_le_of_lt (Nat.mod_le _ _) this

theorem zext_small {v : Word} {w : Nat} (h : v.toNat < 2 ^ w) (_hw : w ≤ 64) : (v.setWidth w).setWidth 64 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by have := v.isLt; omega)]

/-- A load at `R - e` that misses a store at `R - d`. -/
theorem loadN_stR {m : Memory} {R v : Word} {d k e n : Nat} (hd : d ≤ R.toNat) (he : e ≤ R.toNat)
    (h : d + n ≤ e ∨ e + k ≤ d) :
    loadN (storeMem m (R - BitVec.ofNat 64 d) k v) (R - BitVec.ofNat 64 e) n = loadN m (R - BitVec.ofNat 64 e) n :=
  loadN_storeMem_ne (by rw [bsub_toNat hd, bsub_toNat he]; omega)

@[simp] theorem state_fs (B : Silmaril.X86.Bir9.Block) (env : Silmaril.X86.Bir9.Env) :
    (B.state env).core.fsBase = env.s0.fsBase := rfl

/-! ## Outside the page below `R` -/

/-- Below the page under `R`, or at or above `R`. -/
def OutStk (R : Word) (a : Nat) : Prop := a + 2048 < R.toNat ∨ R.toNat ≤ a

theorem keeps_outStk {M : Memory} {R : Word} {d k : Nat} {v : Word} (hd : d ≤ 2047) (hk : k ≤ d)
    (h4 : 2048 ≤ R.toNat) : Keeps (OutStk R) M (storeMem M (R - BitVec.ofNat 64 d) k v) :=
  storeMem_keeps fun x hx => by
    rw [bsub_toNat (by omega)]; unfold OutStk at hx; omega

theorem outStk_of_qw {b : Word} {s : PState} {a : Nat} (h : ¬ QW b s a) (h4 : 2048 ≤ (s.m.core.read .rsp).toNat) :
    OutStk (s.m.core.read .rsp) a := by
  unfold QW at h; unfold OutStk; omega

theorem outStk_of_errno {E : Env} {R : Word} {a : Nat} (h : ErrnoR E a) (he : E.errnoA.toNat + 4 ≤ E.S.lo)
    (hlo : E.S.lo + 2048 ≤ R.toNat) : OutStk R a := by
  unfold ErrnoR at h; unfold OutStk; omega

/-- **Program stores into the page below the entry `rsp`** keep `QF`. -/
theorem QF.stores {E : Env} {W : World} {b lb : Word} {s : PState} {p : List Byte} {m m' : Memory}
    (hE : QEntry E W b lb s p) (hF : QF E W b s m)
    (hk : Keeps (OutStk (s.m.core.read .rsp)) m m') (hreg : m'.regions = m.regions) : QF E W b s m' := by
  have h4 : 2048 ≤ (s.m.core.read .rsp).toNat := hE.room.1
  refine hF.local (fun a ha => ⟨(hE.slot0 a ha).2.2, (hE.slot0 a ha).1⟩) hE.lo
    (hk.mono fun a ha => ?_) (hk.mono fun a ha => ?_) hreg
  · unfold QW at ha; unfold OutStk; omega
  · exact outStk_of_errno ha hE.errnoLo hE.lo

/-! ## Code chunks -/

/-- A code chunk `code` at `b + cb`: in the image, loaded, read-only. -/
structure QC (W : World) (b : Word) (M : Memory) (cb : Nat) (code : List Byte) : Prop where
  img : ∀ n, n < code.length → W.InImage (b + BitVec.ofNat 64 (cb + n)).toNat
  ld : Loaded M (b + BitVec.ofNat 64 cb) code
  ro : CodeRO M (b + BitVec.ofNat 64 cb) code

theorem ShaRO.qc {W : World} {b lb : Word} {M : Memory} (h : ShaRO b lb M) (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {cb : Nat} {code : List Byte} (hv : 0x2000 ≤ cb)
    (hend : cb + code.length ≤ 0x2000 + 0x4d51) (h0 : 0 < code.length)
    (hp : plainOk shaFile shaTextPh shaSlots cb code = true) : QC W b M cb code :=
  ⟨fun n hn => sha_in' I hb (by omega), h.loaded hb hv hend h0 hp, h.codeRO hb hv hend⟩

/-- `ShaRO` is kept by a `QF` frame. -/
theorem QF.shaRO {E : Env} {W : World} {b lb : Word} {s : PState} {p : List Byte} {m : Memory}
    (hE : QEntry E W b lb s p) (hF : QF E W b s m) : ShaRO b lb m :=
  hE.ro.keep ((hF.keepK hE.room).mono fun a ha => ⟨Or.inl (by
    rw [hE.imps.img]; unfold ShaImg; omega), by unfold Slot0; omega⟩)

theorem QF.slots {E : Env} {W : World} {b lb : Word} {s : PState} {p : List Byte} {m : Memory}
    (hE : QEntry E W b lb s p) (hF : QF E W b s m) : QSlots b m :=
  hE.slots.keep hE.imps.hb ((hF.keepK hE.room).mono fun a ha => ⟨Or.inl (by
    rw [hE.imps.img]; exact ha.1), ha.2⟩)

theorem shaQ_slotsOk : slotOk shaSlots 0x9de8 (.addr 2 0x2a6e0) = true ∧
    slotOk shaSlots 0x9df8 (.addr 2 0x39480) = true := by decide +kernel

set_option maxRecDepth 20000 in
/-- The GOT slots of `__errno_location` and `__ctype_get_mb_cur_max`. -/
theorem ShaRO.got {b lb : Word} {m : Memory} (h : ShaRO b lb m) (hb : b.toNat + 0xa188 < 2 ^ 64) :
    loadN m (b + 0x9de8#64) 8 = some (lb + 0x2a6e0#64) ∧ loadN m (b + 0x9df8#64) 8 = some (lb + 0x39480#64) := by
  obtain ⟨Fk, Fc, Fl, kb, ldb, res, ifn, m0, h1, h2, h3, h4, h5⟩ := h
  have hk : ∀ {off : Nat}, 0x2000 ≤ off → off + 8 ≤ 0xa000 →
      loadN m (b + BitVec.ofNat 64 off) 8 = loadN m0 (b + BitVec.ofNat 64 off) 8 := fun {off} ho1 ho2 =>
    h5.loadN fun j hj => by rw [addr_toNat (by omega)]; constructor <;> omega
  obtain ⟨f, b', i, D, T, hf, hb', hi, -, hD, hT, himg⟩ := h4
  simp only [List.head?_cons, Option.some.injEq] at hf hb'
  subst hf hb'
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots h1 h2 h3, Option.some.injEq] at hD
  subst hD
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  obtain ⟨s1, s2⟩ := shaQ_slotsOk
  refine ⟨(hk (off := 0x9de8) (by omega) (by omega)).trans ?_, (hk (off := 0x9df8) (by omega) (by omega)).trans ?_⟩
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)

end Silmaril.Elf.Link.Dyn.Sha256sum
