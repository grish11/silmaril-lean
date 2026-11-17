module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiArgs
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiLast
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailPre

/-! # GNU `sha256sum FILE…`: `main` from `0x29fd` to the first call of `digest_file`

`multi_pre` runs `tail_opts` (the option checks) and `multi_args` (the loop's set-up with
operands) from `MainOpt` and establishes the loop's invariant `LoopAt` at `0x2b81` for the
first operand, with a FRESH body (base: `main`'s entry registers with the memory at `0x2b81`).

`FilesEntry`: the facts of `main`'s entry this needs beyond `MainOpt` (the layout of the
argument vector `argv = a0 :: ops`, `have_read_stdin = 0`, the guard, the return address).
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

/-- **The layout facts at `main`'s entry that its operand loop uses** (beyond what `MainOpt`
carries to `0x29fd`): the return address is the library's gate; the code of all of `main` and
`completed.0` (image); `have_read_stdin = 0`; the guard (kept, outside the image); the operands
`ops` in `argv[1..]` (argument area, `ArgsAt`), `argc = |ops| + 1` without overflow. -/
structure FilesEntry (E : Env) (W : World) (b lb : Word) (s : PState) (ops : List (Word × List Byte))
    (g : Word) : Prop where
  ret : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])
  al : (s.m.core.read .rsp).toNat % 16 = 8
  lo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat
  mainAll : ShaMainAll b s.m.memory
  bss : loadN s.m.memory (b + 0xa040#64) 1 = some 0#64
  bssw : s.m.memory.Permitted .write (b + 0xa040#64).toNat 1
  hr : loadN s.m.memory (b + 0xa160#64) 1 = some 0#64
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  guardImg : ∀ j, j < 8 → ¬ ShaImg b ((s.m.core.fsBase + 0x28#64).toNat + j)
  imgVar : ∀ a, ShaImg b a → ¬ VarR lb a
  argsImg : ∀ a, W.args a → ¬ ShaImg b a
  optK : ∀ a, OptR E a → ¬ W.Kept a
  args : ArgsAt W s.m.memory (s.m.core.read .rsi + 8#64) ops
  ne : ops ≠ []
  argc : BitVec.setWidth 32 (s.m.core.read .rdi) = BitVec.ofNat 32 (ops.length + 1)
  argcLim : ops.length + 1 < 2 ^ 31
  avLim : (s.m.core.read .rsi).toNat + 8 * (ops.length + 1) < 2 ^ 64

theorem filesMem_keeps {m : Memory} {fp p1 e dl : Word} (hfp : 0x100 ≤ fp.toNat) :
    Keeps (fun a => ¬ (fp.toNat - 0x100 ≤ a ∧ a < fp.toNat - 0xd0)) m (filesMem m fp p1 e dl) := by
  have e00 := fpo00 _ hfp
  have e18 := fpo18 _ hfp
  have e20 := fpo20 _ hfp
  have e28 := fpo28 _ hfp
  unfold filesMem
  refine (((storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)).trans
    (storeMem_keeps fun x hx => ?_)).trans (storeMem_keeps fun x hx => ?_)
  · rw [e00]; omega
  · rw [e18]; omega
  · rw [e20]; omega
  · rw [e28]; omega

/-- `&argv[argc]` as computed at `0x2ae3` (`rbx + (sext argc << 3)`). -/
theorem argv_end {av : Word} {k : Nat} (hk : k + 2 < 2 ^ 31) (hlim : av.toNat + 8 * (k + 2) < 2 ^ 64) :
    av + ((BitVec.ofNat 32 (k + 2)).signExtend 64 <<< 3) = av + 8#64 + BitVec.ofNat 64 (8 * (k + 1)) := by
  have hs : (BitVec.ofNat 32 (k + 2)).signExtend 64 <<< 3 = BitVec.ofNat 64 (8 * (k + 2)) := by
    have hm : (BitVec.ofNat 32 (k + 2)).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := k + 2) (by omega), Nat.mod_eq_of_lt (a := k + 2) (by omega),
      Nat.mod_eq_of_lt (a := 8 * (k + 2)) (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [addr_toNat (by omega), addr_toNat (b := av + 8#64) (by rw [addr_toNat (v := 8) (by omega)]; omega),
    addr_toNat (v := 8) (by omega)]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`main` from `0x29fd` to the first `call digest_file`**, operands `(p, n) :: rest`, keeping
the memory outside the image and away from `main`'s stack page (K8). -/
theorem multi_preK {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hopA : E.optindA = lb + 0x204248#64)
    {C : Nat → Prop} {fi : Word} {sti : St} {Q : PState → Prop} {s s1 z : PState} {g : Word}
    {p : Word} {n : List Byte} {rest : List (Word × List Byte)}
    (ht : FilesEntry E W b lb s ((p, n) :: rest) g)
    (hO : MainOpt E W b lb kb sr sc C fi (outSt 1) (outSt 2) sti s s1 z g { s.g with atexit := [b + 0x69b0#64] })
    (hout : s.g.out = []) (hjobs : s.g.jobs = [.exitRax]) (hres : RoomN E s.g (rest.length + 1))
    (k : ∀ v, LoopAt E W b lb kb sr sc s v (s.m.core.read .rsi + 8#64) p n rest [] g →
      Keeps (fun a => ¬ ShaImg b a ∧ (a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a))
        z.m.memory v.m.memory →
      Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a)) s.m.memory v.m.memory →
      v.g = { s.g with atexit := [b + 0x69b0#64] } → MustQ W Q v) :
    MustQ W Q z := by
  have hA := hO.at_
  have hB := hA.body
  have hbase := hA.base
  have hsp1 : s1.m.core.read .rsp = s.m.core.read .rsp := by rw [hbase]
  have hroom : Room W z.m.memory (s.m.core.read .rsp) 4096 := hsp1 ▸ hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hlo := ht.lo
  have hKroom : ∀ a, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat + 8 → ¬ W.Kept a :=
    fun a h1 h2 => (hroom.2.2 a h1 h2).2.2
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a :=
    fun a ha => by by_contra hc; exact hKroom a (by omega) (by omega) ha
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [I]; exact ha)
  have hsz : Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a)) s.m.memory z.m.memory :=
    hA.kimg.trans (hB.keep.mono fun a ha => by
      rcases ha with ha | ha
      · exact Or.inl (hImgK a ha.1)
      · exact Or.inl ha.1)
  have hW : ∀ a, ImgW b a → ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a) := fun a ha => Or.inl ha
  have hzMA : ShaMainAll b z.m.memory := ht.mainAll.keepW hb (hsz.mono hW)
  have hzM : ShaMemM b lb sr z.m.memory := hB.mem.mn
  have hd := hB.done
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
  have hrbp : z.m.core.read .rbp = s.m.core.read .rsp - 8#64 := hA.rbp
  have eC8 : (z.m.core.read .rbp + 0xffffffffffffff38#64).toNat = (s.m.core.read .rsp).toNat - 208 := by
    rw [hrbp]; exact (fp_neg _ 0xc8 (by omega) (by decide) (by decide)).trans (by omega)
  have eE0 : (z.m.core.read .rbp + 0xffffffffffffff20#64).toNat = (s.m.core.read .rsp).toNat - 232 := by
    rw [hrbp]; exact (fp_neg _ 0xe0 (by omega) (by decide) (by decide)).trans (by omega)
  have hbinz : loadN z.m.memory (z.m.core.read .rbp + 0xffffffffffffff38#64) 4 = some 0xffffffff#64 := by
    rw [loadN_rb eC8 hO.binary]; rfl
  have hbin' : loadN (optMem z.m.memory b) (z.m.core.read .rbp + 0xffffffffffffff38#64) 4 = some 0xffffffff#64 := by
    have hK : W.Kept (b + 0xa168#64).toNat := hImgK _ (sha_in hb (by decide))
    rw [loadN_rb eC8 ((optMem_rb hb _ (by
      have := hKout _ hK; rw [addr_toNat (by omega)] at this; omega)).trans hO.binary)]; rfl
  have hchk : loadN (optMem z.m.memory b) (z.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64 := by
    have hK : W.Kept (b + 0xa168#64).toNat := hImgK _ (sha_in hb (by decide))
    rw [loadN_rb eE0 ((optMem_rb hb _ (by
      have := hKout _ hK; rw [addr_toNat (by omega)] at this; omega)).trans hO.check)]; rfl
  -- `have_read_stdin` at `0x29fd`
  have eHR : (b + 0xa160#64).toNat = b.toNat + 0xa160 := addr_toNat (by omega)
  have hrz : loadN z.m.memory (b + 0xa160#64) 1 = some 0#64 := by
    have h1 : z.m.memory.readBytes (b.toNat + 0xa160) 1 = s.m.memory.readBytes (b.toNat + 0xa160) 1 := by
      rw [hB.keep.readBytes (fun j hj => Or.inl (hImgK _ ⟨by omega, by omega⟩)), hA.khr]
    have h2 := ht.hr
    simp only [loadN, eHR] at h2 ⊢
    rw [h1]; exact h2
  refine tail_opts I hb hd hzMA hzM hA.rw hA.rip hbinz hbin' hchk ?_
  intro y hyr hym hyg hyR hydx hyfs
  -- `0x2ae3`
  have hkzy : Keeps (fun x => ImgW b x ∨ ¬ ShaImg b x) z.m.memory y.m.memory := hym ▸ optMem_keep hb _
  have hyMA : ShaMainAll b y.m.memory := hzMA.keepW hb (hkzy.mono fun a ha => Or.inl ha)
  have hyM : ShaMemM b lb sr y.m.memory := hzM.keepW hb (hkzy.mono fun a ha => Or.inl ha)
  have hyd : y.g.done = none := by rw [hyg]; exact hd
  have yrbp : y.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [hyR _ (by decide) (by decide)]; exact hrbp
  have yrbx : y.m.core.read .rbx = s.m.core.read .rsi := by rw [hyR _ (by decide) (by decide)]; exact hA.rbx
  have yr12 : BitVec.setWidth 32 (y.m.core.read .r12) = BitVec.ofNat 32 (rest.length + 2) := by
    rw [hyR _ (by decide) (by decide), hA.r12, ht.argc]; rfl
  have hopt : loadN y.m.memory (lb + 0x204248#64) 4 = some 1#64 := by
    rw [← hopA, loadN_keeps hkzy (fun j hj => Or.inr fun hI => ht.optK _ ⟨by omega, by omega⟩ (hImgK _ hI))]
    exact hO.optind
  have hlimA := ht.avLim
  have hargc := ht.argcLim
  simp only [List.length_cons] at hlimA hargc
  have hn1 : BitVec.ofNat 32 (rest.length + 2) ≠ 1#32 := by
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hend := argv_end (av := s.m.core.read .rsi) (k := rest.length) (by omega) (by omega)
  have eav : (s.m.core.read .rsi + 8#64).toNat = (s.m.core.read .rsi).toNat + 8 := addr_toNat (v := 8) (by omega)
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := ht.args
  -- what `0x29fd` → `0x2ae3` keeps of the arguments
  have hkarg : ∀ a, W.args a → ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a) :=
    fun a ha => Or.inr ⟨Or.inr (Or.inl ha), ht.argsImg a ha⟩
  have hsy : Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a)) s.m.memory y.m.memory :=
    hsz.trans (hkzy.mono fun a ha => by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr ha.2)
  have hfp : 0x100 ≤ (y.m.core.read .rbp).toNat := by rw [yrbp, e8]; omega
  have hpy : ∀ acc a, y.m.memory.permits acc a = z.m.memory.permits acc a := fun _ _ => by rw [hym]; rfl
  refine multi_args I hb hyd (fun m h => hyMA.keepW hb (imgW_img h)) hyr (A := lb + 0x204248#64)
    hyM.optindV hopt yr12 hn1 (by
      rw [yrbx, hend]
      simp only [BitVec.ult, eav, addr_toNat (b := s.m.core.read .rsi + 8#64) (v := 8 * (rest.length + 1))
        (by rw [eav]; omega), decide_eq_true_eq]
      omega) (p1 := p)
    (by rw [yrbx, loadN_keeps hsy (fun j hj => hkarg _ (ha2 j hj))]; exact ha1) hfp
    (fun x hx => by rw [yrbp, e8]; have := hKout x (hImgK x hx); omega)
    (fun x h1 h2 => by
      rw [yrbp, e8] at h1 h2; rw [hpy, hpy]
      exact ⟨(hroom.2.2 x (by omega) (by omega)).1, (hroom.2.2 x (by omega) (by omega)).2.1⟩)
    (by rw [hym, yrbp, ← hrbp]; exact hchk) ?_
  intro v hvr hvm hvg hvfs hvdi hv12 hvsi hvbx hvdx hv14 hv15 hvR
  rw [yrbx, yrbp, hydx, hend] at hvm
  have efp : 0x100 ≤ (s.m.core.read .rsp - 8#64).toNat := by rw [e8]; omega
  have hkyv := hvm ▸ filesMem_keeps (m := y.m.memory) (p1 := p)
    (e := s.m.core.read .rsi + 8#64 + BitVec.ofNat 64 (8 * (rest.length + 1))) (dl := 1#64) efp
  rw [e8] at hkyv
  -- what `0x29fd` → `0x2b81` keeps
  have KW : Keeps (fun a => (ImgW b a ∨ ¬ ShaImg b a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0)) z.m.memory v.m.memory :=
    (hkzy.mono fun a ha => ha.1).trans (hkyv.mono fun a ha => ha.2)
  have hWv : ∀ a, ImgW b a → (ImgW b a ∨ ¬ ShaImg b a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0) := fun a ha =>
    ⟨Or.inl ha, fun hc => by have := hKout a (hImgK a ha.1); omega⟩
  have hRv : ∀ a, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0) →
      (ImgW b a ∨ ¬ ShaImg b a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0) := fun a h1 h2 h3 =>
    ⟨Or.inr fun hI => hKroom a h1 h2 (hImgK a hI), h3⟩
  have KSV : Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a)) s.m.memory v.m.memory :=
    hsz.trans (KW.mono fun a ha => by
      rcases ha with ha | ha
      · exact hWv a ha
      · exact ⟨Or.inr ha.2, fun hc => by have := hKout a ha.1; omega⟩)
  have hpv : ∀ acc a, v.m.memory.permits acc a = z.m.memory.permits acc a := fun acc a => by
    rw [hvm]; unfold filesMem; simp only [storeMem_permits]; rw [hym]; unfold optMem; simp only [storeMem_permits]
  have hImgW : ∀ n, n + 8 ≤ 0xa160 → ∀ j, j < 8 → ImgW b ((b + BitVec.ofNat 64 n).toNat + j) := fun n hn j hj => by
    rw [addr_toNat (by omega)]; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
  have hvsp : v.m.core.read .rsp = z.m.core.read .rsp := by
    rw [hvR .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hyR _ (by decide) (by decide)]
  have hfs : v.m.core.fsBase = s.m.core.fsBase := by
    rw [hvfs, hyfs, hB.fs]; exact congrArg Silmaril.X86.State.fsBase hbase
  have hR : ∀ r : Reg, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .r8 → r ≠ .r12 → r ≠ .rbx → r ≠ .r14 → r ≠ .r15 →
      r ≠ .rdx → r ≠ .rsi → v.m.core.read r = z.m.core.read r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
    rw [hvR r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, hyR r h1 h9]
  have hfrR : ∀ a len, (s.m.core.read .rsp).toNat - 4096 ≤ a → a + len ≤ (s.m.core.read .rsp).toNat + 8 →
      y.m.memory.Permitted .read a len := fun a len h1 h2 => by
    rw [hym]; unfold optMem; rw [storeMem_permitted, storeMem_permitted]
    exact room_perm hroom (Or.inl rfl) h1 h2
  have e18 := fpo18 _ efp
  have e20 := fpo20 _ efp
  have e28 := fpo28 _ efp
  rw [e8] at e18 e20 e28
  have henv : MEnv E W b lb (fun a => C a ∧ ¬ OptR E a) fi (outSt 1) (outSt 2) sti v.m.memory := by
    refine hA.env.keepP (KW.mono fun a ha => ?_) hpv
    rcases ha with ha | ha
    · have hl := E.S.priv_lo _ _ ha
      exact ⟨Or.inr fun hI => hA.env.np a (Or.inl hI) |>.1 ha, by omega⟩
    · have hK : W.Kept a := by
        have := hA.env.vars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
        rwa [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
          simp only [VarR] at ha; omega] at this
      have hni : ¬ ShaImg b a := fun hI => ht.imgVar a hI ha
      exact ⟨Or.inr hni, fun hc => by have := hKout a hK; omega⟩
  have hgv : v.g = { s.g with atexit := [b + 0x69b0#64] } := hvg.trans (hyg.trans hA.g)
  refine k v ⟨⟨Body.freshK hB hbase (by decide) hvsp (by rw [hvfs, hyfs]) (by rw [hvg, hyg]; exact hd)
      hpv (KW.mono fun a ha => hRv a (by omega) (by omega) (by omega)) (hB.mem.keepW hb (KW.mono hWv)),
    hzMA.keepW hb (KW.mono hWv),
    by rw [loadN_keeps KSV (fun j hj => Or.inl (hImgW 0xa040 (by decide) j (by omega)))]; exact ht.bss,
    (KSV.permitted (fun j hj => Or.inl (hImgW 0xa040 (by decide) j (by omega)))).2 ht.bssw, ?_, hvr,
    by rw [hR .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hrbp,
    by rw [hvbx, yrbp], hv12, hv14, by rw [hv15, yrbx], hfs, by rw [hgv]; exact hjobs, by rw [hgv],
    ?_, ?_, ⟨outSt 1, ⟨henv.out, rfl⟩, rfl, rfl, by rw [hgv]; simp [hout, outSt]⟩, henv.err, henv.vars,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hgv]; exact hres.mono (by omega)⟩, hvdi, by rw [hvsi, yrbp],
    by rw [hvdx, yrbp], by rw [hgv]; exact hres⟩
    (KW.mono fun a ha => ⟨Or.inr ha.1, by have := ha.2; omega⟩) KSV hgv
  · have e68 : (b + 0xa168#64).toNat = b.toNat + 0xa168 := addr_toNat (by omega)
    have e78 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by omega)
    rw [loadN_keeps hkyv (fun j hj => fun hc => by
        have := hKout _ (hImgK ((b + 0xa160#64).toNat + j) (by rw [eHR]; exact ⟨by omega, by omega⟩)); omega), hym]
    unfold optMem
    rw [loadN_storeMem_ne (by rw [e78, eHR]; omega), loadN_storeMem_ne (by rw [e68, eHR]; omega)]
    exact hrz
  · rw [loadN_keeps KSV (fun j hj => Or.inr ⟨ht.guardk j hj, ht.guardImg j hj⟩)]
    exact ht.guard
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega))]; exact hA.guard
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega))]; exact hO.tag
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega))]; exact hO.binary
  · have e78 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by omega)
    rw [loadN_keeps hkyv (fun j hj => fun hc => by
        have := hKout _ (hImgK ((b + 0xa178#64).toNat + j) (by rw [e78]; exact ⟨by omega, by omega⟩)); omega), hym]
    exact loadN_store8 (shaRw_perm (o := 0x18) (n := 8) hb hA.rw (Or.inl rfl) (by decide))
  · rw [hvm]; unfold filesMem
    rw [loadN_storeMem_ne (by rw [e18, e28]; omega), loadN_storeMem_ne (by rw [e18, e20]; omega)]
    exact loadN_store8 (by rw [storeMem_permitted, e18]; exact hfrR _ _ (by omega) (by omega))
  · rw [eav]; omega
  · rw [hvm]; unfold filesMem
    rw [loadN_store1 (by
      rw [storeMem_permitted, storeMem_permitted, storeMem_permitted, e28]
      exact hfrR _ _ (by omega) (by omega))]
    rfl
  · rw [hvm]; unfold filesMem
    rw [loadN_storeMem_ne (by rw [e20, e28]; omega)]
    exact loadN_store8 (by rw [storeMem_permitted, storeMem_permitted, e20]; exact hfrR _ _ (by omega) (by omega))
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega)),
      hB.keep.readBytes (fun j hj => Or.inr (by rw [hsp1]; omega)), hA.ret]
    exact ht.ret
  · exact ArgsAt.keep (KSV.mono fun a ha => hkarg a ha) ⟨ha1, ha2, ha3, ha4, ha5⟩

/-- **`main` from `0x29fd` to the first `call digest_file`**, operands `(p, n) :: rest`. -/
theorem multi_pre {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hopA : E.optindA = lb + 0x204248#64)
    {C : Nat → Prop} {fi : Word} {sti : St} {Q : PState → Prop} {s s1 z : PState} {g : Word}
    {p : Word} {n : List Byte} {rest : List (Word × List Byte)}
    (ht : FilesEntry E W b lb s ((p, n) :: rest) g)
    (hO : MainOpt E W b lb kb sr sc C fi (outSt 1) (outSt 2) sti s s1 z g { s.g with atexit := [b + 0x69b0#64] })
    (hout : s.g.out = []) (hjobs : s.g.jobs = [.exitRax]) (hres : RoomN E s.g (rest.length + 1))
    (k : ∀ v, LoopAt E W b lb kb sr sc s v (s.m.core.read .rsi + 8#64) p n rest [] g → MustQ W Q v) :
    MustQ W Q z :=
  multi_preK I hb hopA ht hO hout hjobs hres fun v h _ _ _ => k v h

end Silmaril.Elf.Link.Dyn.Sha256sum
