module

public import Silmaril.Sim.GlibcBridge.Bytes.Defs
public import Silmaril.Proofs.Sim.GlibcBridge.Hello
public import Silmaril.Sim.X86.Toy.Thms

/-!
# The glibc hello's actual bytes on GM, relative to the `puts` contract

* `emitB_sound`: the added methods (`endbr64`, RIP-relative `lea`) and GM's are sound for
  `Silmaril.X86.Ext.exec`; `jmpInd_sound`: the `jmp *[rip + d]` step is `Ext9.execNew`'s.
* `enc_extStore0`: the import return (before the driver's `ret`) keeps the encoding.
* `brun_x_inv`, `brun_jmp_inv`, `brun_fm_inv`: inversion of dispatcher runs.
* `tabAt_ghello`: the table is the bytes.
* `ghelloB_run`, `ghelloB_run_of`: the dispatcher runs of the actual `main` + `puts@plt` with a
  `puts` meeting `putsC1` have exactly the WASI hello's observables.
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G
open Silmaril.Sim.X86.GM
open Silmaril.Sim.WasiBridge
open Silmaril.Sim.WasiBridge.G

variable {H : Type} {s : Store H} {f : Frame}

/-! ## The added methods -/

theorem exec_endbr64 (σ : State) (m : Memory) (n : Nat) :
    Silmaril.X86.Ext.exec .endbr64 σ m n = Silmaril.X86.Ext.exec (.jmp8 0) σ m n := by
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire]

theorem exec_lea_rip (d : Reg) (disp : BitVec 32) (σ : State) (m : Memory) (n : Nat) :
    Silmaril.X86.Ext.exec (.lea .q d (Silmaril.X86.Ext.Mem.ofRip disp)) σ m n =
      Silmaril.X86.Ext.exec (.movabs d (σ.rip + BitVec.ofNat 64 n + disp.signExtend 64)) σ m n := by
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Mem.addr,
    Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Base.value, Silmaril.X86.Ext.Sz.write]

theorem exec_lea_rip' (d : Reg) (mm : Silmaril.X86.Ext.Mem) (hb : mm.base = .rip) (σ : State)
    (m : Memory) (n : Nat) :
    Silmaril.X86.Ext.exec (.lea .q d mm) σ m n =
      Silmaril.X86.Ext.exec (.movabs d (σ.rip + BitVec.ofNat 64 n + mm.disp.signExtend 64)) σ m n := by
  obtain ⟨b, ix, disp, hr⟩ := mm
  simp only at hb
  subst hb
  obtain rfl := hr rfl
  exact exec_lea_rip d disp σ m n

/-- `access i σ n = some (a, k)` is impossible for a concrete instruction without a memory
operand (it closes the hypothesis), or forces `a`, `k` for one with a stack access. -/
macro "access_cases " h:ident : tactic => `(tactic| (set_option linter.unusedSimpArgs false in
  simp [access, accessMem, formOf, cmpOf, cmpIOf, flagOf, Form.access, Opd.access, opdOf] at $h:ident))

/-- **Soundness of the methods** (GM's `emitM_sound`, extended). -/
theorem emitB_sound {W : Win} {i : Silmaril.X86.Ext.Instr} {n : Nat} {code : List Instr}
    {σ : State} (hc : emitB W σ.rip i n = some code) (hE : Enc s f σ) {mem : Memory}
    (hM : MemEnc s f mem W) {σ' : State} {mem' : Memory}
    (hx : Silmaril.X86.Ext.exec i σ mem n = .ok σ' mem')
    (hw : ∀ a k, access i σ n = some (a, k) → W.HoldsK k a) :
    ∃ s', exec s f [] code = some (s', f, []) ∧ Enc s' f σ' ∧ MemEnc s' f mem' W := by
  unfold emitB at hc
  split at hc
  · rw [exec_endbr64] at hx
    obtain ⟨s', h1, h2, h3, -⟩ := emitM_sound hc hE hM hx (fun a k h => by access_cases h)
    exact ⟨s', h1, h2, h3⟩
  · rename_i d mm
    split at hc
    · rename_i hb
      rw [exec_lea_rip' d mm hb] at hx
      obtain ⟨s', h1, h2, h3, -⟩ := emitM_sound hc hE hM hx (fun a k h => by access_cases h)
      exact ⟨s', h1, h2, h3⟩
    · cases hc
  · obtain ⟨s', h1, h2, h3, -⟩ := emitM_sound hc hE hM hx hw
    exact ⟨s', h1, h2, h3⟩

/-- The `jmp *[rip + d]` step is `Ext9`'s: with the load answered by the memory, the store after
it encodes `Ext9.execNew`'s state. -/
theorem jmpInd_sound {σ : State} (hE : Enc s f σ) {mem : Memory} {d : BitVec 32} {n : Nat}
    {v : Word}
    (hl : Silmaril.X86.Ext.loadN mem (σ.rip + BitVec.ofNat 64 n + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.execNew (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip d))) σ mem
        (σ.rip + BitVec.ofNat 64 n) = .ok { σ with rip := v } mem ∧
      Enc (upd s f .rip (Val.i64 v)) f { σ with rip := v } := by
  refine ⟨?_, Enc.next hE { σ with rip := v } rfl rfl v rfl⟩
  simp [Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.Mem.addr,
    Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Base.value, hl, Silmaril.X86.Ext.Sz.bytes]

/-! ## The import return -/

/-- The core after an import returned `v` with scratch registers `ws` (flags undefined). -/
def extCore0 (σ : State) (v : Word) (ws : Reg → Word) : State :=
  { writeRegs (σ.write .rax v) (scratch.map fun q => (q, ws q)) with flags := undefFlags σ.flags }

theorem enc_extStore0 {σ : State} (hE : Enc s f σ) (v : Word) (ws : Reg → Word) :
    Enc (extStore0 s f v ws) f (extCore0 σ v ws) := by
  have h₁ := enc_reg hE .rax v (σ.write .rax v) (regsAfter_write _ _ _ _ rfl) rfl rfl
  have h₂ := enc_undef (enc_updRegs h₁ (scratch.map fun q => (q, ws q)))
  have hf : undefFlags (writeRegs (σ.write .rax v) (scratch.map fun q => (q, ws q))).flags =
      undefFlags σ.flags := by rw [writeRegs_flags]; rfl
  unfold extCore0
  rw [← hf]
  exact h₂

theorem wbytes_updRegs (s : Store H) (l : List (Reg × Word)) :
    wbytes (updRegs s f l) f = wbytes s f := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => exact (ih _).trans (wbytes_upd _ _ _ _)

theorem memEnc_extStore0 {mem : Memory} {W : Win} (hM : MemEnc s f mem W) (v : Word)
    (ws : Reg → Word) : MemEnc (extStore0 s f v ws) f mem W :=
  hM.congr ((wbytes_updRegs _ _).trans (wbytes_upd _ _ _ _))

theorem writeRegs_read_rsp (σ : State) (l : List (Reg × Word)) (h : ∀ e ∈ l, e.1 ≠ .rsp) :
    (writeRegs σ l).read .rsp = σ.read .rsp := by
  induction l generalizing σ with
  | nil => rfl
  | cons a l ih =>
    simp only [writeRegs]
    rw [ih _ (fun e he => h e (List.mem_cons_of_mem _ he))]
    rw [State.read_write]
    have := h a (List.mem_cons_self ..)
    simp [Ne.symm this]

theorem extCore0_rsp (σ : State) (v : Word) (ws : Reg → Word) :
    (extCore0 σ v ws).read .rsp = σ.read .rsp := by
  show (writeRegs (σ.write .rax v) (scratch.map fun q => (q, ws q))).read .rsp = _
  rw [writeRegs_read_rsp _ _ (by simp [scratch])]
  simp

theorem extCore0_rip (σ : State) (v : Word) (ws : Reg → Word) : (extCore0 σ v ws).rip = σ.rip := by
  show (writeRegs (σ.write .rax v) (scratch.map fun q => (q, ws q))).rip = _
  rw [writeRegs_rip]; rfl


/-! ## The x86 steps of the hello -/

theorem exec_endbr64' (σ : State) (m : Memory) (n : Nat) :
    Silmaril.X86.Ext.exec .endbr64 σ m n = .ok { σ with rip := σ.rip + BitVec.ofNat 64 n } m := by
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire]

theorem exec_aluI8_rsp (σ : State) (m : Memory) (n : Nat) (op : Silmaril.X86.AluOp)
    (h : op ≠ .cmp) : ∃ fl, Silmaril.X86.Ext.exec (.aluI8 .q op (.reg .rsp) 8#8) σ m n =
      .ok { σ.write .rsp (Silmaril.X86.Ext.AluOp.resultN op (σ.read .rsp) 8#64) with
        rip := σ.rip + BitVec.ofNat 64 n, flags := fl } m := by
  cases op <;> simp at h <;>
    simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]

theorem exec_xor_eax (σ : State) (m : Memory) (n : Nat) :
    ∃ fl, Silmaril.X86.Ext.exec (.alu .d .xor (.reg .rax) .rax) σ m n =
      .ok { σ.write .rax 0 with rip := σ.rip + BitVec.ofNat 64 n, flags := fl } m := by
  have hx : ∀ y : BitVec Silmaril.X86.Ext.Sz.d.bits, (y ^^^ y).setWidth 64 = 0#64 := fun y => by
    apply BitVec.eq_of_toNat_eq; simp; erw [BitVec.toNat_xor, Nat.xor_self]
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write,
    Silmaril.X86.Ext.AluOp.resultN]
  erw [hx]

theorem exec_call' {σ : State} {m m' : Memory} {n : Nat} (rel : BitVec 32)
    (hs : Silmaril.X86.Ext.storeN m (σ.read .rsp - 8#64) 8 (σ.rip + BitVec.ofNat 64 n) = some m') :
    Silmaril.X86.Ext.exec (.call rel) σ m n =
      .ok { σ.write .rsp (σ.read .rsp - 8#64) with
        rip := σ.rip + BitVec.ofNat 64 n + rel.signExtend 64 } m' := by
  simp [Silmaril.X86.Ext.exec, pushWord_storeN, hs]

theorem exec_ret' {σ : State} {m : Memory} {n : Nat} {v : Word}
    (h : Silmaril.X86.Ext.loadN m (σ.read .rsp) 8 = some v) :
    Silmaril.X86.Ext.exec .ret σ m n = .ok { σ.write .rsp (σ.read .rsp + 8#64) with rip := v } m := by
  simp [Silmaril.X86.Ext.exec, popWord_loadN h]

theorem permitted_of_loadN {m : Memory} {a v : Word} {k : Nat}
    (h : Silmaril.X86.Ext.loadN m a k = some v) : m.Permitted .read a.toNat k := by
  simp only [Silmaril.X86.Ext.loadN, Option.map_eq_some_iff, Silmaril.Process.Memory.readBytes,
    Silmaril.Process.Memory.readWith] at h
  obtain ⟨b, hb, -⟩ := h
  split at hb
  · assumption
  · cases hb

/-! ## Inversion -/

variable {C : Nat → ImportC} {mem : Memory} {W : Win} {ld : Word → Option Word}
  {fm : Word → Option (Nat × List Reg)} {tab : BTab}

theorem brun_x_inv {evs : List LEv} (hb : BRun C mem W ld fm tab s f evs) {σ : State}
    (hE : Enc s f σ) {memX : Memory} (hM : MemEnc s f memX W) (hfm : fm σ.rip = none)
    {i : Silmaril.X86.Ext.Instr} {n : Nat} (hl : lookupB tab σ.rip = some (.x i, n)) {σ' : State}
    {memX' : Memory} (hx : Silmaril.X86.Ext.exec i σ memX n = .ok σ' memX')
    (hw : ∀ a k, access i σ n = some (a, k) → W.HoldsK k a) :
    evs = [] ∨ ∃ s' : Store H, Enc s' f σ' ∧ MemEnc s' f memX' W ∧ BRun C mem W ld fm tab s' f evs := by
  have hr := hE.2.2.1
  cases hb with
  | stop => exact .inl rfl
  | ins hrip _ hl' hc he hb' =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hl] at hl'; simp only [Option.some.injEq, Prod.mk.injEq, BI.x.injEq] at hl'
    obtain ⟨rfl, rfl⟩ := hl'
    obtain ⟨s'', he', hE', hM'⟩ := emitB_sound hc hE hM hx hw
    rw [he] at he'; cases he'
    exact .inr ⟨_, hE', hM', hb'⟩
  | jmpInd hrip _ hl' =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hl] at hl'; simp at hl'
  | ext hrip hf =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hfm] at hf; cases hf
  | halt hrip hf =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hfm] at hf; cases hf

theorem brun_jmp_inv {evs : List LEv} (hb : BRun C mem W ld fm tab s f evs) {σ : State}
    (hE : Enc s f σ) (hfm : fm σ.rip = none) {d : BitVec 32} {n : Nat}
    (hl : lookupB tab σ.rip = some (.jmpInd d, n)) {v : Word}
    (hld : ld (σ.rip + BitVec.ofNat 64 n + d.signExtend 64) = some v) :
    evs = [] ∨ BRun C mem W ld fm tab (upd s f .rip (Val.i64 v)) f evs := by
  have hr := hE.2.2.1
  cases hb with
  | stop => exact .inl rfl
  | ins hrip _ hl' =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hl] at hl'; simp at hl'
  | jmpInd hrip _ hl' hld' hb' =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hl] at hl'; simp only [Option.some.injEq, Prod.mk.injEq, BI.jmpInd.injEq] at hl'
    obtain ⟨rfl, rfl⟩ := hl'
    rw [hld] at hld'; cases hld'
    exact .inr hb'
  | ext hrip hf =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hfm] at hf; cases hf
  | halt hrip hf =>
    rw [hr] at hrip; simp only [Option.some.injEq, val_i64_inj] at hrip; subst hrip
    rw [hfm] at hf; cases hf

/-- The RIP global of a store with `Enc`: the dispatcher looks up the encoded RIP. -/
private theorem fm_rip {α : Type} {fm : Word → Option α} {r a : Word}
    (hr : gval s f .rip = some (Val.i64 a)) (hrip : gval s f .rip = some (Val.i64 r)) :
    fm r = fm a := by
  rw [val_i64_inj.mp (Option.some.inj (hrip.symm.trans hr))]

theorem brun_fm_inv {evs : List LEv} (hb : BRun C mem W ld fm tab s f evs) {σ : State}
    (hE : Enc s f σ) {k : Nat} {regs : List Reg} (hfm : fm σ.rip = some (k, regs)) :
    evs = [] ∨ (∃ o, C k mem (regs.map σ.read) o none ∧ evs = [.ext k (regs.map σ.read) o none]) ∨
    ∃ (o : List Obs) (v : Word) (ws : Reg → Word) (rc : List Instr) (s' : Store H) (evs' : List LEv), C k mem (regs.map σ.read) o (some v) ∧
      evs = .ext k (regs.map σ.read) o (some v) :: evs' ∧ emitM W .ret 1 = some rc ∧
      exec (extStore0 s f v ws) f [] rc = some (s', f, []) ∧ BRun C mem W ld fm tab s' f evs' := by
  have hr : gval s f .rip = some (Val.i64 σ.rip) := hE.2.2.1
  have ha : regArgs s f regs = some (regs.map σ.read) := regArgs_enc hE regs
  cases hb with
  | stop => exact .inl rfl
  | ins hrip hf => cases hfm.symm.trans ((fm_rip hr hrip).symm.trans hf)
  | jmpInd hrip hf => cases hfm.symm.trans ((fm_rip hr hrip).symm.trans hf)
  | ext hrip hf h hc hrc he hb' =>
    obtain ⟨rfl, rfl⟩ : (k, regs) = (_, _) :=
      Option.some.inj (hfm.symm.trans ((fm_rip hr hrip).symm.trans hf))
    cases ha.symm.trans h
    exact .inr (.inr ⟨_, _, _, _, _, _, hc, rfl, hrc, he, hb'⟩)
  | halt hrip hf h hc =>
    obtain ⟨rfl, rfl⟩ : (k, regs) = (_, _) :=
      Option.some.inj (hfm.symm.trans ((fm_rip hr hrip).symm.trans hf))
    cases ha.symm.trans h
    exact .inr (.inl ⟨_, hc, rfl⟩)

/-- The outputs `putsC1` allows for the hello's string. -/
theorem putsC1_hello {m : Memory} {p : Word} {args : List Word} {o : List Obs} {r : Option Word}
    (h : putsC1 m args o r) (hp : args.head? = some p) (hstr : cstr m p = some msgS) :
    (∃ v, r = some v) ∧ ∃ k, 1 ≤ k ∧ k ≤ 14 ∧ o = (helloMsg.take k).map (.wr 1) := by
  obtain ⟨⟨p', s', w, r', v', hp', hs, hpg, rfl, rfl, -⟩, hne⟩ := h
  rw [hp, Option.some.injEq] at hp'
  subst hp'
  rw [hstr, Option.some.injEq] at hs
  subst hs
  have hpre := putsGlibc_prefix hpg
  rw [msgS_nl] at hpre
  have hw0 : w ≠ [] := by rintro rfl; exact hne rfl
  refine ⟨⟨_, rfl⟩, w.length, List.length_pos_iff.2 hw0, ?_, ?_⟩
  · have := hpre.length_le; simpa [helloMsg] using this
  · rw [← List.prefix_iff_eq_take.1 hpre]

/-! ## The glibc hello's bytes -/

theorem read_with_rip (t : State) (y : Word) (r : Reg) :
    ({ t with rip := y } : State).read r = t.read r := rfl

theorem ghelloFm_none {r : Word} (h1 : r ≠ putsF) (h2 : r ≠ mainRet) : ghelloFm r = none := by
  simp [ghelloFm, h1, h2]

theorem ghelloFm_puts : ghelloFm putsF = some (0, sysvArgs) := by simp [ghelloFm]

theorem ghelloFm_ret : ghelloFm mainRet = some (1, [.rax]) := by
  simp [ghelloFm, show mainRet ≠ putsF by decide]

/-- **The tail of `main`** after `puts` returned: `xor %eax,%eax; add $8,%rsp; ret` to
`mainRet`, then `exit(rax)`. -/
theorem ghelloB_tail {P : ImportC} {ld : Word → Option Word} {σ : State} (hE : Enc s f σ)
    {m : Memory} (hM : MemEnc s f m W) (hrip : σ.rip = 0x401064#64)
    (hret : Silmaril.X86.Ext.loadN m (σ.read .rsp + 8#64) 8 = some mainRet)
    (hW : W.Holds (σ.read .rsp + 8#64)) {evs : List LEv}
    (hb : BRun (ghelloC P) mem W ld ghelloFm ghelloTab s f evs) :
    levsObs mem evs <+: [.exit 0] := by
  have nil : levsObs mem [] <+: [Obs.exit 0] := List.nil_prefix
  -- xor %eax,%eax
  obtain ⟨fl8, hx8⟩ := exec_xor_eax σ m 2
  rcases brun_x_inv hb hE hM (by rw [hrip]; exact ghelloFm_none (by decide) (by decide))
    (by rw [hrip]; rfl) hx8 (fun a k h => by access_cases h) with rfl | ⟨s8, hE8, hM8, hb⟩
  · exact nil
  generalize hσ8 : ({ σ.write .rax 0 with rip := σ.rip + BitVec.ofNat 64 2, flags := fl8 } : State) = σ8 at hE8
  have r8 : σ8.rip = 0x401066#64 := by rw [← hσ8]; show σ.rip + _ = _; rw [hrip]; decide
  have a8 : σ8.read .rax = 0 := by
    rw [← hσ8]; show (σ.write .rax 0).read .rax = 0; exact State.read_write_same ..
  have p8 : σ8.read .rsp = σ.read .rsp := by
    rw [← hσ8]; show (σ.write .rax 0).read .rsp = _; rw [State.read_write]; simp
  -- add $8,%rsp
  obtain ⟨fl9, hx9⟩ := exec_aluI8_rsp σ8 m 4 .add (by decide)
  rcases brun_x_inv hb hE8 hM8 (by rw [r8]; exact ghelloFm_none (by decide) (by decide))
    (by rw [r8]; rfl) hx9 (fun a k h => by access_cases h) with rfl | ⟨s9, hE9, hM9, hb⟩
  · exact nil
  generalize hσ9 : ({ σ8.write .rsp (Silmaril.X86.Ext.AluOp.resultN .add (σ8.read .rsp) 8#64) with
    rip := σ8.rip + BitVec.ofNat 64 4, flags := fl9 } : State) = σ9 at hE9
  have r9 : σ9.rip = 0x40106a#64 := by rw [← hσ9]; show σ8.rip + _ = _; rw [r8]; decide
  have a9 : σ9.read .rax = 0 := by
    rw [← hσ9]
    show (σ8.write .rsp (Silmaril.X86.Ext.AluOp.resultN .add (σ8.read .rsp) 8#64)).read .rax = 0
    rw [State.read_write]; simpa using a8
  have p9 : σ9.read .rsp = σ.read .rsp + 8#64 := by
    rw [← hσ9]
    show (σ8.write .rsp (Silmaril.X86.Ext.AluOp.resultN .add (σ8.read .rsp) 8#64)).read .rsp = _
    rw [State.read_write_same, p8]; rfl
  -- ret
  have hret9 : Silmaril.X86.Ext.loadN m (σ9.read .rsp) 8 = some mainRet := by rw [p9]; exact hret
  have hW9 : W.Holds (σ9.read .rsp) := by rw [p9]; exact hW
  rcases brun_x_inv hb hE9 hM9 (by rw [r9]; exact ghelloFm_none (by decide) (by decide))
    (by rw [r9]; rfl) (exec_ret' (n := 1) hret9) (fun a k h => by access_cases h; obtain ⟨rfl, rfl⟩ := h; exact hW9)
    with rfl | ⟨s10, hE10, -, hb⟩
  · exact nil
  have a10 : ({ σ9.write .rsp (σ9.read .rsp + 8#64) with rip := mainRet } : State).read .rax = 0 := by
    show (σ9.write .rsp (σ9.read .rsp + 8#64)).read .rax = 0; rw [State.read_write]; simpa using a9
  -- exit(rax)
  rcases brun_fm_inv hb hE10 ghelloFm_ret with rfl | ⟨o, hc, rfl⟩ | ⟨o, v, -, -, -, -, hc, -⟩
  · exact nil
  · obtain ⟨a, ha, rfl, -⟩ := hc
    simp only [List.map_cons, List.map_nil, a10, List.head?_cons, Option.some.injEq] at ha
    subst ha
    simp [levsObs, LEv.obs]
  · obtain ⟨_, -, -, h⟩ := hc
    cases h

/-- The address of the string (`lea 0xfa5(%rip),%rdi` at `0x401058`). -/
def ghMsg : Word := 0x402004#64

/-- From the import address with the string in `rdi` and the return address on the stack:
the `puts` call, the driver's `ret`, and the tail. -/
theorem ghelloB_mid {P : ImportC} (hP : Meets P putsC1) {ld : Word → Option Word}
    (hstr : cstr mem ghMsg = some msgS) {σ : State} (hE : Enc s f σ) {m : Memory}
    (hM : MemEnc s f m W) (hrip : σ.rip = putsF) (hd : σ.read .rdi = ghMsg)
    (hra : Silmaril.X86.Ext.loadN m (σ.read .rsp) 8 = some 0x401064#64) (hWa : W.Holds (σ.read .rsp))
    (hmr : Silmaril.X86.Ext.loadN m (σ.read .rsp + 16#64) 8 = some mainRet)
    (hW0 : W.Holds (σ.read .rsp + 16#64)) {evs : List LEv}
    (hb : BRun (ghelloC P) mem W ld ghelloFm ghelloTab s f evs) :
    ∃ k, 1 ≤ k ∧ k ≤ 14 ∧ levsObs mem evs <+: helloObs k := by
  have nil : levsObs mem [] <+: helloObs 1 := List.nil_prefix
  rcases brun_fm_inv hb hE (by rw [hrip]; exact ghelloFm_puts) with rfl | ⟨o, hc, -⟩ |
      ⟨o, v, ws, rc, s7, evs', hc, rfl, hrc, he7, hb7⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  · obtain ⟨⟨_, h⟩, -⟩ := putsC1_hello (hP _ _ _ _ hc) (by simp [sysvArgs, hd]) hstr
    cases h
  obtain ⟨-, k, hk1, hk, rfl⟩ := putsC1_hello (hP _ _ _ _ hc) (by simp [sysvArgs, hd]) hstr
  have hEτ : Enc (extStore0 s f v ws) f (extCore0 σ v ws) := enc_extStore0 hE v ws
  have hMτ : MemEnc (extStore0 s f v ws) f m W := memEnc_extStore0 hM v ws
  have pτ : (extCore0 σ v ws).read .rsp = σ.read .rsp := extCore0_rsp σ v ws
  have hraτ : Silmaril.X86.Ext.loadN m ((extCore0 σ v ws).read .rsp) 8 = some 0x401064#64 := by
    rw [pτ]; exact hra
  have hWaτ : W.Holds ((extCore0 σ v ws).read .rsp) := by rw [pτ]; exact hWa
  obtain ⟨s7', he7', hE7, hM7, -⟩ := emitM_sound hrc hEτ hMτ (exec_ret' (n := 1) hraτ)
    (fun a k h => by access_cases h; obtain ⟨rfl, rfl⟩ := h; exact hWaτ)
  cases he7.symm.trans he7'
  refine ⟨k, hk1, hk, ?_⟩
  show (helloMsg.take k).map (.wr 1) ++ levsObs mem evs' <+: helloObs k
  rw [helloObs]
  refine (List.prefix_append_right_inj _).2 (ghelloB_tail hE7 hM7 rfl ?_ ?_ hb7)
  · rw [read_with_rip, State.read_write_same, pτ,
      show σ.read .rsp + 8#64 + 8#64 = σ.read .rsp + 16#64 by bv_omega]
    exact hmr
  · rw [read_with_rip, State.read_write_same, pτ,
      show σ.read .rsp + 8#64 + 8#64 = σ.read .rsp + 16#64 by bv_omega]
    exact hW0

set_option maxRecDepth 20000 in
/-- **Every dispatcher run of the actual bytes** (`main` from its entry, `puts@plt`, with
`GOT[puts]` bound to the import and `main`'s return address the start-up contract's
`mainRet`), with a `puts` meeting `putsC1`, has the observables of the WASI hello for some
`1 ≤ k ≤ 14`. -/
theorem ghelloB_run {P : ImportC} (hP : Meets P putsC1) {ld : Word → Option Word}
    (hstr : cstr mem ghMsg = some msgS) (hgot : ld gotPuts = some putsF) {σ : State}
    (hE : Enc s f σ) (hM : MemEnc s f mem W) (hrw : W.rw = true) (hrip : σ.rip = 0x401050#64)
    (hret : Silmaril.X86.Ext.loadN mem (σ.read .rsp) 8 = some mainRet)
    (hW0 : W.Holds (σ.read .rsp)) (hW16 : W.Holds (σ.read .rsp - 16#64))
    (h16 : 16 ≤ (σ.read .rsp).toNat) {evs : List LEv}
    (hb : BRun (ghelloC P) mem W ld ghelloFm ghelloTab s f evs) :
    ∃ k, 1 ≤ k ∧ k ≤ 14 ∧ levsObs mem evs <+: helloObs k := by
  have nil : levsObs mem [] <+: helloObs 1 := List.nil_prefix
  generalize hR : σ.read .rsp = R at hret hW0 hW16 h16
  -- endbr64
  rcases brun_x_inv hb hE hM (by rw [hrip]; exact ghelloFm_none (by decide) (by decide))
    (by rw [hrip]; rfl) (exec_endbr64' σ mem 4) (fun a k h => by access_cases h)
    with rfl | ⟨s1, hE1, hM1, hb1⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  generalize hσ1 : ({ σ with rip := σ.rip + BitVec.ofNat 64 4 } : State) = σ1 at hE1
  have r1 : σ1.rip = 0x401054#64 := by rw [← hσ1]; show σ.rip + _ = _; rw [hrip]; decide
  have p1 : σ1.read .rsp = R := by rw [← hσ1, ← hR]; rfl
  -- sub $8,%rsp
  obtain ⟨fl2, hx2⟩ := exec_aluI8_rsp σ1 mem 4 .sub (by decide)
  rcases brun_x_inv hb1 hE1 hM1 (by rw [r1]; exact ghelloFm_none (by decide) (by decide))
    (by rw [r1]; rfl) hx2 (fun a k h => by access_cases h) with rfl | ⟨s2, hE2, hM2, hb2⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  generalize hσ2 : ({ σ1.write .rsp (Silmaril.X86.Ext.AluOp.resultN .sub (σ1.read .rsp) 8#64) with
    rip := σ1.rip + BitVec.ofNat 64 4, flags := fl2 } : State) = σ2 at hE2
  have r2 : σ2.rip = 0x401058#64 := by rw [← hσ2]; show σ1.rip + _ = _; rw [r1]; decide
  have p2 : σ2.read .rsp = R - 8#64 := by
    rw [← hσ2]
    show (σ1.write .rsp (Silmaril.X86.Ext.AluOp.resultN .sub (σ1.read .rsp) 8#64)).read .rsp = _
    rw [State.read_write_same, p1]; rfl
  -- lea 0xfa5(%rip),%rdi
  have hx3 := (exec_lea_rip .rdi 0xfa5#32 σ2 mem 7).trans (exec_movabs .rdi _ σ2 mem 7)
  rcases brun_x_inv hb2 hE2 hM2 (by rw [r2]; exact ghelloFm_none (by decide) (by decide))
    (by rw [r2]; rfl) hx3 (fun a k h => by access_cases h) with rfl | ⟨s3, hE3, hM3, hb3⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  generalize hσ3 : movStep σ2 .rdi (σ2.rip + BitVec.ofNat 64 7 + (0xfa5#32).signExtend 64) 7 = σ3
    at hE3
  have r3 : σ3.rip = 0x40105f#64 := by rw [← hσ3, movStep_rip, r2]; decide
  have p3 : σ3.read .rsp = R - 8#64 := by rw [← hσ3]; simp [p2]
  have d3 : σ3.read .rdi = ghMsg := by rw [← hσ3]; simp [r2]; decide
  -- call puts@plt
  have hWa : W.Holds (σ3.read .rsp - 8#64) := by
    rw [p3, show R - 8#64 - 8#64 = R - 16#64 by bv_omega]; exact hW16
  obtain ⟨-, -, -, m1, -, hst, -, -, -⟩ := hM3.store hrw hWa (σ3.rip + BitVec.ofNat 64 5)
  have hx4 := exec_call' 0xffffffdc#32 hst
  rcases brun_x_inv hb3 hE3 hM3 (by rw [r3]; exact ghelloFm_none (by decide) (by decide))
    (by rw [r3]; rfl) hx4 (fun a k h => by access_cases h; obtain ⟨rfl, rfl⟩ := h; exact hWa)
    with rfl | ⟨s4, hE4, hM4, hb4⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  have hra : Silmaril.X86.Ext.loadN m1 (σ3.read .rsp - 8#64) 8 = some 0x401064#64 := by
    obtain ⟨-, w, -, hl, -⟩ := hM3.load hWa
    rw [Silmaril.X86.Ext.loadN_storeN_eight hst (permitted_of_loadN hl), r3]; decide
  have hmr : Silmaril.X86.Ext.loadN m1 R 8 = some mainRet := by
    rw [Silmaril.X86.Ext.loadN_storeN_disjoint hst (by rw [p3]; bv_omega), hret]
  generalize hσ4 : ({ σ3.write .rsp (σ3.read .rsp - 8#64) with
    rip := σ3.rip + BitVec.ofNat 64 5 + (0xffffffdc#32).signExtend 64 } : State) = σ4 at hE4
  have r4 : σ4.rip = 0x401040#64 := by rw [← hσ4]; show σ3.rip + _ + _ = _; rw [r3]; decide
  have p4 : σ4.read .rsp = σ3.read .rsp - 8#64 := by
    rw [← hσ4, read_with_rip, State.read_write_same]
  have d4 : σ4.read .rdi = ghMsg := by
    rw [← hσ4, read_with_rip, State.read_write]; simpa using d3
  -- puts@plt: endbr64
  rcases brun_x_inv hb4 hE4 hM4 (by rw [r4]; exact ghelloFm_none (by decide) (by decide))
    (by rw [r4]; rfl) (exec_endbr64' σ4 m1 4) (fun a k h => by access_cases h)
    with rfl | ⟨s5, hE5, hM5, hb5⟩
  · exact ⟨1, le_rfl, by omega, nil⟩
  generalize hσ5 : ({ σ4 with rip := σ4.rip + BitVec.ofNat 64 4 } : State) = σ5 at hE5
  have r5 : σ5.rip = 0x401044#64 := by rw [← hσ5]; show σ4.rip + _ = _; rw [r4]; decide
  -- jmp *0x2fb6(%rip)
  have hld : ld (σ5.rip + BitVec.ofNat 64 6 + (0x2fb6#32).signExtend 64) = some putsF := by
    rw [r5, show (0x401044#64 + BitVec.ofNat 64 6 + (0x2fb6#32).signExtend 64) = gotPuts by decide]
    exact hgot
  rcases brun_jmp_inv hb5 hE5 (by rw [r5]; exact ghelloFm_none (by decide) (by decide))
    (by rw [r5]; rfl) hld with rfl | hb6
  · exact ⟨1, le_rfl, by omega, nil⟩
  have hE6 := Enc.next hE5 { σ5 with rip := putsF } rfl rfl putsF rfl
  have hM6 := hM5.congr (wbytes_upd s5 f .rip (Val.i64 putsF))
  have d6 : ({ σ5 with rip := putsF } : State).read .rdi = ghMsg := by
    rw [read_with_rip, ← hσ5, read_with_rip]; exact d4
  have p6 : ({ σ5 with rip := putsF } : State).read .rsp = σ3.read .rsp - 8#64 := by
    rw [read_with_rip, ← hσ5, read_with_rip]; exact p4
  -- the import call, the driver's `ret` and the tail
  rw [← p6] at hra
  rw [← p6] at hWa
  exact ghelloB_mid hP hstr hE6 hM6 rfl d6 hra hWa
    (by rw [p6, p3, show R - 8#64 - 8#64 + 16#64 = R by bv_omega]; exact hmr)
    (by rw [p6, p3, show R - 8#64 - 8#64 + 16#64 = R by bv_omega]; exact hW0) hb6

end Silmaril.Sim.GlibcBridge
