module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailRun2
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailMid
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainStdin

/-! # GNU `sha256sum`, stdin tier: `main` from `0x29fd` to the call of `digest_file`, as a body

`tail_pre` runs `tail_opts` and `tail_args` from `MainOpt` and states what holds at `0x2b81`
(`MidAt`): a FRESH body of `main` (base: `main`'s entry registers with the memory at `0x2b81`,
so nothing before is to be kept: the `.bss` option stores and `argv[1] = "-"` lie outside both
the image part `ImgW` and the frame), the library state, and the values the rest of `main`
reads (the loop's slots, the guard, the return address).
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

/-- What holds at `0x2b81` (`call digest_file`), with `main`'s entry `s` (`sp` its stack
pointer, `argv` its `rsi`). -/
structure MidAt (E : Env) (W : World) (b lb kb sr sc : Word) (C : Nat → Prop) (fi : Word) (sto ste sti : St)
    (s v : PState) (g : Word) (G : Ghost) : Prop where
  body : Body W (ShaMemAll b lb kb sr sc) (reb s v.m.memory) v 328 4096 (sv6 (reb s v.m.memory))
  ma : ShaMainAll b v.m.memory
  rw : ShaRw b v.m.memory
  clr : loadN v.m.memory (b + 0x9f68#64) 8 = some (lb + 0x91400#64)
  bss : loadN v.m.memory (b + 0xa040#64) 1 = some 0#64
  bssw : v.m.memory.Permitted .write (b + 0xa040#64).toNat 1
  rip : v.m.core.rip = b + 0x2b81#64
  rbp : v.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rdi : v.m.core.read .rdi = b + 0x716e#64
  r12 : v.m.core.read .r12 = b + 0x716e#64
  rsi : v.m.core.read .rsi = s.m.core.read .rsp - 8#64 + 0xffffffffffffffa0#64
  rbx : v.m.core.read .rbx = s.m.core.read .rsp - 8#64 + 0xffffffffffffffa0#64
  rdx : v.m.core.read .rdx = s.m.core.read .rsp - 8#64 + 0xffffffffffffff58#64
  r14 : v.m.core.read .r14 = b + 0x7238#64
  r15 : v.m.core.read .r15 = s.m.core.read .rsi + 8#64
  fs : v.m.core.fsBase = s.m.core.fsBase
  ghost : v.g = G
  guard : loadN v.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guards : v.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  var : loadN v.m.memory (lb + 0x2056b0#64) 8 = some fi
  env : MEnv E W b lb C fi sto ste sti v.m.memory
  tag : v.m.memory.readBytes ((s.m.core.read .rsp).toNat - 216) 1 = some [0#8]
  bin : v.m.memory.readBytes ((s.m.core.read .rsp).toNat - 208) 4 = some [0xff#8, 0xff#8, 0xff#8, 0xff#8]
  len : loadN v.m.memory (b + 0xa178#64) 8 = some 0x40#64
  endp : loadN v.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64) 8 = some (s.m.core.read .rsi + 16#64)
  ok : loadN v.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 = some 1#64
  ret : v.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])

/-- The stores of `0x2ae3`–`0x2b74` keep everything outside the frame slots and `argv[1]`. -/
theorem argsMem_keeps {m : Memory} {av fp b dl : Word} (hfp : 0x100 ≤ fp.toNat) (hav : av.toNat + 16 < 2 ^ 64) :
    Keeps (fun a => ¬ (fp.toNat - 0x100 ≤ a ∧ a < fp.toNat - 0xd0) ∧ ¬ (av.toNat + 8 ≤ a ∧ a < av.toNat + 16))
      m (argsMem m av fp b dl) := by
  have ea : (av + 8#64).toNat = av.toNat + 8 := addr_toNat (v := 8) (by omega)
  have e00 := fpo00 _ hfp
  have e18 := fpo18 _ hfp
  have e20 := fpo20 _ hfp
  have e28 := fpo28 _ hfp
  unfold argsMem
  refine ((((storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)).trans
    (storeMem_keeps fun x hx => ?_)).trans (storeMem_keeps fun x hx => ?_)).trans (storeMem_keeps fun x hx => ?_)
  · rw [ea]; omega
  · rw [e00]; omega
  · rw [e18]; omega
  · rw [e20]; omega
  · rw [e28]; omega

/-- The library state survives a change of memory that keeps its private memory, the stream
variables and every permission. -/
theorem MEnv.keepP {E : Env} {W : World} {b lb : Word} {C : Nat → Prop} {fi : Word} {sto ste sti : St}
    {m m' : Memory} (h : MEnv E W b lb C fi sto ste sti m)
    (hk : Keeps (fun a => E.S.priv m a ∨ VarR lb a) m m') (hp : ∀ acc a, m'.permits acc a = m.permits acc a) :
    MEnv E W b lb C fi sto ste sti m' := by
  have hpv : E.S.priv m' = E.S.priv m := E.S.priv_keep _ _ (hk.mono fun _ h => Or.inl h)
  have hf : ∀ f st, E.S.file m f st → E.S.file m' f st := fun f st hf =>
    (E.S.local_ _ _ _ _ (hk.mono fun x hx => Or.inl (E.S.foot_priv _ _ _ _ hf hx)) hf).1
  refine ⟨hf _ _ h.out, hf _ _ h.err, hf _ _ h.inp, h.vars.keepR (hk.mono fun _ h => Or.inr h),
    fun x hx => ?_, fun x hx => ?_⟩
  · rw [hpv, hp]; exact h.np x hx
  · rw [hp]; exact h.wr x hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`main` from `0x29fd` to `call digest_file`** (`tail_opts`, `tail_args`), stdin tier,
packaged as `MidAt`. -/
theorem tail_pre {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hopA : E.optindA = lb + 0x204248#64)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s s1 z : PState} {g : Word} {G : Ghost}
    (ht : TailEntry E W b lb s fi g) (hO : MainOpt E W b lb kb sr sc C fi sto ste sti s s1 z g G)
    (hargc : BitVec.setWidth 32 (s.m.core.read .rdi) = 1#32)
    (k : ∀ v, MidAt E W b lb kb sr sc (fun a => C a ∧ ¬ OptR E a) fi sto ste sti s v g G → MustQ W Q v) :
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
  -- from the entry to `0x29fd`
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
  refine tail_opts I hb hd hzMA hzM hA.rw hA.rip hbinz hbin' hchk ?_
  intro y hyr hym hyg hyR hydx hyfs
  -- `0x2ae3`
  have hkzy : Keeps (fun x => ImgW b x ∨ ¬ ShaImg b x) z.m.memory y.m.memory := hym ▸ optMem_keep hb _
  have hyMA : ShaMainAll b y.m.memory := hzMA.keepW hb (hkzy.mono fun a ha => Or.inl ha)
  have hyM : ShaMemM b lb sr y.m.memory := hzM.keepW hb (hkzy.mono fun a ha => Or.inl ha)
  have hyd : y.g.done = none := by rw [hyg]; exact hd
  have yrbp : y.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [hyR _ (by decide) (by decide)]; exact hrbp
  have yrbx : y.m.core.read .rbx = s.m.core.read .rsi := by rw [hyR _ (by decide) (by decide)]; exact hA.rbx
  have yr12 : BitVec.setWidth 32 (y.m.core.read .r12) = 1#32 := by
    rw [hyR _ (by decide) (by decide), hA.r12, hargc]
  have hopt : loadN y.m.memory (lb + 0x204248#64) 4 = some 1#64 := by
    rw [← hopA, loadN_keeps hkzy (fun j hj => Or.inr fun hI => ht.optK _ ⟨by omega, by omega⟩ (hImgK _ hI))]
    exact hO.optind
  have hav := ht.av
  have eav : (s.m.core.read .rsi + 8#64).toNat = (s.m.core.read .rsi).toNat + 8 := addr_toNat (v := 8) (by omega)
  have hPav : ∀ j, j < 8 → ImgW b ((s.m.core.read .rsi).toNat + 8 + j) ∨
      (W.Kept ((s.m.core.read .rsi).toNat + 8 + j) ∧ ¬ ShaImg b ((s.m.core.read .rsi).toNat + 8 + j)) :=
    fun j hj => Or.inr ⟨Or.inr (Or.inl (ht.avA j hj)), ht.argsImg _ (ht.avA j hj)⟩
  have hpy : ∀ acc a, y.m.memory.permits acc a = z.m.memory.permits acc a := fun _ _ => by rw [hym]; rfl
  have hyperm : ∀ {acc : Access}, s.m.memory.Permitted acc ((s.m.core.read .rsi).toNat + 8) 8 →
      y.m.memory.Permitted acc (y.m.core.read .rbx + 8#64).toNat 8 := fun {acc} h => by
    rw [yrbx, eav, hym]; unfold optMem; rw [storeMem_permitted, storeMem_permitted]
    exact (hsz.permitted (acc := acc) hPav).2 h
  have hfp : 0x100 ≤ (y.m.core.read .rbp).toNat := by rw [yrbp, e8]; omega
  refine tail_args I hb hyd (fun m h => hyMA.keepW hb (imgW_img h)) hyr (A := lb + 0x204248#64)
    hyM.optindV hopt yr12
    (by rw [yrbx]; exact hav) (hyperm ht.avW) (hyperm ht.avR) hfp
    (fun x hx => by rw [yrbp, e8]; have := hKout x (hImgK x hx); omega)
    (fun x hx => by
      rw [yrbx]; by_contra hc
      exact ht.argsImg _ (by
        have := ht.avA (x - ((s.m.core.read .rsi).toNat + 8)) (by omega)
        rwa [show (s.m.core.read .rsi).toNat + 8 + (x - ((s.m.core.read .rsi).toNat + 8)) = x by omega] at this) hx)
    (by rw [yrbp, yrbx, e8]; have := ht.avHi; omega)
    (fun x h1 h2 => by
      rw [yrbp, e8] at h1 h2; rw [hpy, hpy]
      exact ⟨(hroom.2.2 x (by omega) (by omega)).1, (hroom.2.2 x (by omega) (by omega)).2.1⟩)
    (by rw [hym, yrbp, ← hrbp]; exact hchk) ?_
  intro v hvr hvm hvg hvfs hvdi hv12 hvsi hvbx hvdx hv14 hv15 hvR
  rw [yrbx, yrbp, hydx] at hvm
  have efp : 0x100 ≤ (s.m.core.read .rsp - 8#64).toNat := by rw [e8]; omega
  have hkyv := hvm ▸ argsMem_keeps (m := y.m.memory) (b := b) (dl := 1#64) efp hav
  rw [e8] at hkyv
  -- what `0x29fd` → `0x2b81` keeps
  have KW : Keeps (fun a => (ImgW b a ∨ ¬ ShaImg b a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0) ∧
      ¬ ((s.m.core.read .rsi).toNat + 8 ≤ a ∧ a < (s.m.core.read .rsi).toNat + 16)) z.m.memory v.m.memory :=
    (hkzy.mono fun a ha => ha.1).trans (hkyv.mono fun a ha => ha.2)
  have hslot : ∀ a, ShaImg b a → ¬ ((s.m.core.read .rsi).toNat + 8 ≤ a ∧ a < (s.m.core.read .rsi).toNat + 16) :=
    fun a hI hc => ht.argsImg _ (by
      have := ht.avA (a - ((s.m.core.read .rsi).toNat + 8)) (by omega)
      rwa [show (s.m.core.read .rsi).toNat + 8 + (a - ((s.m.core.read .rsi).toNat + 8)) = a by omega] at this) hI
  have hWv : ∀ a, ImgW b a → (ImgW b a ∨ ¬ ShaImg b a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0) ∧
      ¬ ((s.m.core.read .rsi).toNat + 8 ≤ a ∧ a < (s.m.core.read .rsi).toNat + 16) := fun a ha =>
    ⟨Or.inl ha, fun hc => by have := hKout a (hImgK a ha.1); omega, hslot a ha.1⟩
  have hRv : ∀ a, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0) →
      (ImgW b a ∨ ¬ ShaImg b a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 8 - 0x100 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 8 - 0xd0) ∧
      ¬ ((s.m.core.read .rsi).toNat + 8 ≤ a ∧ a < (s.m.core.read .rsi).toNat + 16) := fun a h1 h2 h3 =>
    ⟨Or.inr fun hI => hKroom a h1 h2 (hImgK a hI), h3, fun hc => by have := ht.avHi; omega⟩
  have KSV : Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a ∧
      ¬ ((s.m.core.read .rsi).toNat + 8 ≤ a ∧ a < (s.m.core.read .rsi).toNat + 16))) s.m.memory v.m.memory :=
    (hsz.mono fun a ha => ha.imp id fun h => ⟨h.1, h.2.1⟩).trans (KW.mono fun a ha => by
      rcases ha with ha | ha
      · exact hWv a ha
      · exact ⟨Or.inr ha.2.1, fun hc => by have := hKout a ha.1; omega, ha.2.2⟩)
  have hpv : ∀ acc a, v.m.memory.permits acc a = z.m.memory.permits acc a := fun acc a => by
    rw [hvm]; unfold argsMem; simp only [storeMem_permits]; rw [hym]; unfold optMem; simp only [storeMem_permits]
  have hImgW : ∀ n, n + 8 ≤ 0xa160 → ∀ j, j < 8 → ImgW b ((b + BitVec.ofNat 64 n).toNat + j) := fun n hn j hj => by
    rw [addr_toNat (by omega)]; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
  have hvsp : v.m.core.read .rsp = s.m.core.read .rsp - 328#64 := by
    rw [hvR .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hyR _ (by decide) (by decide), hB.rsp, hsp1]
  have hfs : v.m.core.fsBase = s.m.core.fsBase := by
    rw [hvfs, hyfs, hB.fs]; exact congrArg Silmaril.X86.State.fsBase hbase
  have hsv : sv6 (reb s v.m.memory) = sv6 s1 := by simp only [sv6, reb_core, hbase]
  have hR : ∀ r : Reg, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .r8 → r ≠ .r12 → r ≠ .rbx → r ≠ .r14 → r ≠ .r15 →
      r ≠ .rdx → r ≠ .rsi → v.m.core.read r = z.m.core.read r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
    rw [hvR r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, hyR r h1 h9]
  -- the stores' values
  have hfrR : ∀ a len, (s.m.core.read .rsp).toNat - 4096 ≤ a → a + len ≤ (s.m.core.read .rsp).toNat + 8 →
      y.m.memory.Permitted .read a len := fun a len h1 h2 => by
    rw [hym]; unfold optMem; rw [storeMem_permitted, storeMem_permitted]
    exact room_perm hroom (Or.inl rfl) h1 h2
  have e18 := fpo18 _ efp
  have e20 := fpo20 _ efp
  have e28 := fpo28 _ efp
  rw [e8] at e18 e20 e28
  refine k v ⟨⟨by rw [hvsp]; rfl, Keeps.refl _ _, hroom.keeps fun a _ _ acc => hpv acc a,
      hB.mem.keepW hb (KW.mono hWv), hfs, by rw [hvg, hyg]; exact hd, ?_, fun _ _ _ _ => rfl⟩,
    hzMA.keepW hb (KW.mono hWv), fun j hj => by rw [hpv, hpv]; exact hA.rw j hj, ?_, ?_, ?_, hvr, ?_, hvdi, hv12,
    by rw [hvsi, yrbp], by rw [hvbx, yrbp], by rw [hvdx, yrbp], hv14, by rw [hv15, yrbx], hfs,
    hvg.trans (hyg.trans hA.g), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hsv] at hp
    have hp' := hB.saved p hp
    simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hp
    have h8 : 8 ≤ p.1 ∧ p.1 ≤ 48 := by rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    show v.m.memory.readBytes ((s.m.core.read .rsp).toNat - p.1) 8 = _
    rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega)), ← hp', hsp1]
  · rw [loadN_keeps KSV (fun j hj => Or.inl (hImgW 0x9f68 (by decide) j hj))]; exact ht.clr
  · rw [loadN_keeps KSV (fun j hj => Or.inl (hImgW 0xa040 (by decide) j (by omega)))]; exact ht.bss
  · exact (KSV.permitted (fun j hj => Or.inl (hImgW 0xa040 (by decide) j (by omega)))).2 ht.bssw
  · rw [hR .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hrbp
  · rw [loadN_keeps KSV (fun j hj => Or.inr ⟨ht.guardk j hj, ht.guardImg j hj, by have := ht.avG; omega⟩)]
    exact ht.guard
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega))]; exact hA.guard
  · rw [loadN_keeps KSV (fun j hj => Or.inr ⟨ht.vark j hj, ht.varImg j hj, by have := ht.avIn; omega⟩)]
    exact ht.var
  · refine hA.env.keepP (KW.mono fun a ha => ?_) hpv
    rcases ha with ha | ha
    · have hl := E.S.priv_lo _ _ ha
      exact ⟨Or.inr fun hI => hA.env.np a (Or.inl hI) |>.1 ha, by omega, fun hc => by have := ht.avHi; omega⟩
    · have hK : W.Kept a := by
        have := hA.env.vars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
        rwa [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
          simp only [VarR] at ha; omega] at this
      refine ⟨Or.inr fun hI => ht.imgVar a hI ha, fun hc => by have := hKout a hK; omega, fun hc => ?_⟩
      have := ht.avVar (a - ((s.m.core.read .rsi).toNat + 8)) (by omega)
      rw [show (s.m.core.read .rsi).toNat + 8 + (a - ((s.m.core.read .rsi).toNat + 8)) = a by omega] at this
      exact this ha
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega))]; exact hO.tag
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega))]; exact hO.binary
  · have e78 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by omega)
    rw [loadN_keeps hkyv (fun j hj => ⟨fun hc => by
        have := hKout _ (hImgK ((b + 0xa178#64).toNat + j) (by rw [e78]; exact ⟨by omega, by omega⟩)); omega,
        hslot _ (by rw [e78]; exact ⟨by omega, by omega⟩)⟩), hym]
    exact loadN_store8 (shaRw_perm (o := 0x18) (n := 8) hb hA.rw (Or.inl rfl) (by decide))
  · rw [hvm]; unfold argsMem
    rw [loadN_storeMem_ne (by rw [e18, e28]; omega), loadN_storeMem_ne (by rw [e18, e20]; omega)]
    exact loadN_store8 (by rw [storeMem_permitted, storeMem_permitted, e18]; exact hfrR _ _ (by omega) (by omega))
  · rw [hvm]; unfold argsMem
    rw [loadN_store1 (by
      rw [storeMem_permitted, storeMem_permitted, storeMem_permitted, storeMem_permitted, e28]
      exact hfrR _ _ (by omega) (by omega))]
    rfl
  · rw [KW.readBytes (fun j hj => hRv _ (by omega) (by omega) (by omega)),
      hB.keep.readBytes (fun j hj => Or.inr (by rw [hsp1]; omega)), hA.ret]
    exact ht.ret

end Silmaril.Elf.Link.Dyn.Sha256sum
