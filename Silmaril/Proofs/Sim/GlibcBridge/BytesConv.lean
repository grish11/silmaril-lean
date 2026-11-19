module

public import Silmaril.Proofs.Sim.GlibcBridge.Bytes

/-!
# The glibc hello's actual bytes on GM: the converse, the table, the equivalence

* `tabAt_ghello`: the code table is what the bytes of `main` and `puts@plt` decode to.
* `ghelloB_run_of`: if the `puts` admits each output `msg.take k`, each WASI hello trace is the
  observable trace of a dispatcher run of the actual bytes.
* **`ghelloB_equiv`**: relative to the `puts` contract, the actual linked bytes ≡ the WASI hello.
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
variable {C : Nat → ImportC} {mem : Memory} {W : Win} {ld : Word → Option Word}
  {fm : Word → Option (Nat × List Reg)} {tab : BTab}

/-! ## Forward steps -/

theorem brun_x_step {σ : State} (hE : Enc s f σ) {memX : Memory} (hM : MemEnc s f memX W)
    (hfm : fm σ.rip = none) {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (hl : lookupB tab σ.rip = some (.x i, n)) (hc : (emitB W σ.rip i n).isSome) {σ' : State} {memX' : Memory}
    (hx : Silmaril.X86.Ext.exec i σ memX n = .ok σ' memX')
    (hw : ∀ a k, access i σ n = some (a, k) → W.HoldsK k a) :
    ∃ s' : Store H, Enc s' f σ' ∧ MemEnc s' f memX' W ∧
      ∀ evs, BRun C mem W ld fm tab s' f evs → BRun C mem W ld fm tab s f evs := by
  obtain ⟨code, hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨s', he, hE', hM'⟩ := emitB_sound hc hE hM hx hw
  exact ⟨s', hE', hM', fun _ hb => .ins hE.2.2.1 hfm hl hc he hb⟩

/-! ## The table -/

theorem fetch_sub {m : Memory} {a : Nat} {bs : List Byte}
    (h : m.fetchBytes a bs.length = some bs) {off n : Nat} (h1 : off < bs.length)
    (h2 : off + n ≤ bs.length) : m.fetchBytes (a + off) n = some ((bs.drop off).take n) :=
  Silmaril.Process.Memory.readWith_sub_range h h1 h2

/-- **The table is the bytes** of `puts@plt` (at `0x401040`) and `main` (at `0x401050`). -/
theorem tabAt_ghello {m : Memory} (hp : m.fetchBytes 0x401040 pltBytes.length = some pltBytes)
    (hm : m.fetchBytes 0x401050 mainBytes.length = some mainBytes) : TabAt m ghelloTab := by
  show ∀ e ∈ ghelloTab, _
  simp only [ghelloTab, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 0) (n := 4) hp (by decide) (by decide), by decide⟩
  · exact ⟨_, fetch_sub (off := 4) (n := 6) hp (by decide) (by decide), by decide⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 0) (n := 4) hm (by decide) (by decide), by decide⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 4) (n := 4) hm (by decide) (by decide), by decide⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 8) (n := 7) hm (by decide) (by decide), by decide⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 15) (n := 5) hm (by decide) (by decide), by decide⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 20) (n := 2) hm (by decide) (by decide), by decide⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 22) (n := 4) hm (by decide) (by decide), by decide⟩
  · exact Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, fetch_sub (off := 26) (n := 1) hm (by decide) (by decide), by decide⟩

/-! ## The converse -/

theorem ghelloB_tail_of {P : ImportC} {ld : Word → Option Word} {σ : State} (hE : Enc s f σ)
    {m : Memory} (hM : MemEnc s f m W) (hrip : σ.rip = 0x401064#64)
    (hret : Silmaril.X86.Ext.loadN m (σ.read .rsp + 8#64) 8 = some mainRet)
    (hW : W.Holds (σ.read .rsp + 8#64)) :
    BRun (ghelloC P) mem W ld ghelloFm ghelloTab s f [.ext 1 [0] [.exit 0] none] := by
  obtain ⟨fl8, hx8⟩ := exec_xor_eax σ m 2
  obtain ⟨s8, hE8, hM8, g8⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE hM
    (by rw [hrip]; exact ghelloFm_none (by decide) (by decide)) (by rw [hrip]; rfl)
    (by rw [hrip]; rfl) hx8 (fun a k h => by access_cases h)
  generalize hσ8 : ({ σ.write .rax 0 with rip := σ.rip + BitVec.ofNat 64 2, flags := fl8 } : State) = σ8 at hE8
  have r8 : σ8.rip = 0x401066#64 := by rw [← hσ8]; show σ.rip + _ = _; rw [hrip]; decide
  have a8 : σ8.read .rax = 0 := by
    rw [← hσ8]; show (σ.write .rax 0).read .rax = 0; exact State.read_write_same ..
  have p8 : σ8.read .rsp = σ.read .rsp := by
    rw [← hσ8]; show (σ.write .rax 0).read .rsp = _; rw [State.read_write]; simp
  obtain ⟨fl9, hx9⟩ := exec_aluI8_rsp σ8 m 4 .add (by decide)
  obtain ⟨s9, hE9, hM9, g9⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE8 hM8
    (by rw [r8]; exact ghelloFm_none (by decide) (by decide)) (by rw [r8]; rfl)
    (by rw [r8]; rfl) hx9 (fun a k h => by access_cases h)
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
  rw [← p9] at hret hW
  obtain ⟨s10, hE10, -, g10⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE9 hM9
    (by rw [r9]; exact ghelloFm_none (by decide) (by decide)) (by rw [r9]; rfl)
    (by rw [r9]; rfl) (exec_ret' (n := 1) hret) (fun a k h => by access_cases h; obtain ⟨rfl, rfl⟩ := h; exact hW)
  have a10 : ({ σ9.write .rsp (σ9.read .rsp + 8#64) with rip := mainRet } : State).read .rax = 0 := by
    rw [read_with_rip, State.read_write]; simpa using a9
  have hexit : exitC mem ([Reg.rax].map
      ({ σ9.write .rsp (σ9.read .rsp + 8#64) with rip := mainRet } : State).read) [.exit 0] none :=
    ⟨0, by simp; exact a9, by decide, rfl⟩
  have hh := BRun.halt (C := ghelloC P) (mem := mem) (W := W) (ld := ld) (tab := ghelloTab)
    hE10.2.2.1 ghelloFm_ret (regArgs_enc hE10 _) hexit
  simp only [List.map_cons, List.map_nil, a10] at hh
  exact g8 _ (g9 _ (g10 _ hh))

/-- The converse from the import address. -/
theorem ghelloB_mid_of {P : ImportC} {ld : Word → Option Word}
    (hA : ∀ args k, args.head? = some ghMsg → 1 ≤ k → k ≤ 14 →
      ∃ v, P mem args ((helloMsg.take k).map (.wr 1)) (some v))
    {σ : State} (hE : Enc s f σ) {m : Memory}
    (hM : MemEnc s f m W) (hrip : σ.rip = putsF) (hd : σ.read .rdi = ghMsg)
    (hra : Silmaril.X86.Ext.loadN m (σ.read .rsp) 8 = some 0x401064#64) (hWa : W.Holds (σ.read .rsp))
    (hmr : Silmaril.X86.Ext.loadN m (σ.read .rsp + 16#64) 8 = some mainRet)
    (hW0 : W.Holds (σ.read .rsp + 16#64)) {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 14) :
    ∃ evs, BRun (ghelloC P) mem W ld ghelloFm ghelloTab s f evs ∧ levsObs mem evs = helloObs k := by
  obtain ⟨v, hv⟩ := hA (sysvArgs.map σ.read) k (by simp [sysvArgs, hd]) hk1 hk
  have hEτ := enc_extStore0 hE v (fun _ => 0)
  have hMτ := memEnc_extStore0 hM v (fun _ => 0)
  have pτ := extCore0_rsp σ v (fun _ => 0)
  rw [← pτ] at hra hWa
  obtain ⟨rc, hrc⟩ : ∃ rc, emitM W .ret 1 = some rc := ⟨_, rfl⟩
  obtain ⟨s7, he7, hE7, hM7, -⟩ := emitM_sound hrc hEτ hMτ (exec_ret' (n := 1) hra)
    (fun a k h => by access_cases h; obtain ⟨rfl, rfl⟩ := h; exact hWa)
  have ht := ghelloB_tail_of (P := P) (mem := mem) (ld := ld) hE7 hM7 rfl
    (by rw [read_with_rip, State.read_write_same, pτ,
          show σ.read .rsp + 8#64 + 8#64 = σ.read .rsp + 16#64 by bv_omega]; exact hmr)
    (by rw [read_with_rip, State.read_write_same, pτ,
          show σ.read .rsp + 8#64 + 8#64 = σ.read .rsp + 16#64 by bv_omega]; exact hW0)
  refine ⟨_, BRun.ext (k := 0) (regs := sysvArgs) (ws := fun _ => 0) hE.2.2.1
    (by rw [hrip]; exact ghelloFm_puts) (regArgs_enc hE _) (show ghelloC P 0 mem _ _ _ from hv)
    hrc he7 ht, ?_⟩
  simp [levsObs, LEv.obs, helloObs]

set_option maxRecDepth 20000 in
/-- **The converse**: if the `puts` admits every output `msg.take k`, each WASI hello trace is
the observable trace of a dispatcher run of the actual bytes. -/
theorem ghelloB_run_of {P : ImportC} {ld : Word → Option Word}
    (hA : ∀ args k, args.head? = some ghMsg → 1 ≤ k → k ≤ 14 →
      ∃ v, P mem args ((helloMsg.take k).map (.wr 1)) (some v))
    (hgot : ld gotPuts = some putsF) {σ : State}
    (hE : Enc s f σ) (hM : MemEnc s f mem W) (hrw : W.rw = true) (hrip : σ.rip = 0x401050#64)
    (hret : Silmaril.X86.Ext.loadN mem (σ.read .rsp) 8 = some mainRet)
    (hW0 : W.Holds (σ.read .rsp)) (hW16 : W.Holds (σ.read .rsp - 16#64))
    (h16 : 16 ≤ (σ.read .rsp).toNat) {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 14) :
    ∃ evs, BRun (ghelloC P) mem W ld ghelloFm ghelloTab s f evs ∧ levsObs mem evs = helloObs k := by
  generalize hR : σ.read .rsp = R at hret hW0 hW16 h16
  obtain ⟨s1, hE1, hM1, g1⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE hM
    (by rw [hrip]; exact ghelloFm_none (by decide) (by decide)) (by rw [hrip]; rfl)
    (by rw [hrip]; rfl) (exec_endbr64' σ mem 4) (fun a k h => by access_cases h)
  generalize hσ1 : ({ σ with rip := σ.rip + BitVec.ofNat 64 4 } : State) = σ1 at hE1
  have r1 : σ1.rip = 0x401054#64 := by rw [← hσ1]; show σ.rip + _ = _; rw [hrip]; decide
  have p1 : σ1.read .rsp = R := by rw [← hσ1, ← hR]; rfl
  obtain ⟨fl2, hx2⟩ := exec_aluI8_rsp σ1 mem 4 .sub (by decide)
  obtain ⟨s2, hE2, hM2, g2⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE1 hM1
    (by rw [r1]; exact ghelloFm_none (by decide) (by decide)) (by rw [r1]; rfl)
    (by rw [r1]; rfl) hx2 (fun a k h => by access_cases h)
  generalize hσ2 : ({ σ1.write .rsp (Silmaril.X86.Ext.AluOp.resultN .sub (σ1.read .rsp) 8#64) with
    rip := σ1.rip + BitVec.ofNat 64 4, flags := fl2 } : State) = σ2 at hE2
  have r2 : σ2.rip = 0x401058#64 := by rw [← hσ2]; show σ1.rip + _ = _; rw [r1]; decide
  have p2 : σ2.read .rsp = R - 8#64 := by
    rw [← hσ2]
    show (σ1.write .rsp (Silmaril.X86.Ext.AluOp.resultN .sub (σ1.read .rsp) 8#64)).read .rsp = _
    rw [State.read_write_same, p1]; rfl
  have hx3 := (exec_lea_rip .rdi 0xfa5#32 σ2 mem 7).trans (exec_movabs .rdi _ σ2 mem 7)
  obtain ⟨s3, hE3, hM3, g3⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE2 hM2
    (by rw [r2]; exact ghelloFm_none (by decide) (by decide)) (by rw [r2]; rfl)
    (by rw [r2]; rfl) hx3 (fun a k h => by access_cases h)
  generalize hσ3 : movStep σ2 .rdi (σ2.rip + BitVec.ofNat 64 7 + (0xfa5#32).signExtend 64) 7 = σ3
    at hE3
  have r3 : σ3.rip = 0x40105f#64 := by rw [← hσ3, movStep_rip, r2]; decide
  have p3 : σ3.read .rsp = R - 8#64 := by rw [← hσ3]; simp [p2]
  have d3 : σ3.read .rdi = ghMsg := by rw [← hσ3]; simp [r2]; decide
  have hWa : W.Holds (σ3.read .rsp - 8#64) := by
    rw [p3, show R - 8#64 - 8#64 = R - 16#64 by bv_omega]; exact hW16
  obtain ⟨-, -, -, m1, -, hst, -, -, -⟩ := hM3.store hrw hWa (σ3.rip + BitVec.ofNat 64 5)
  have hx4 := exec_call' 0xffffffdc#32 hst
  obtain ⟨s4, hE4, hM4, g4⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE3 hM3
    (by rw [r3]; exact ghelloFm_none (by decide) (by decide)) (by rw [r3]; rfl)
    (by rw [r3]; simp [emitB, emitM, emitMem, hrw]) hx4 (fun a k h => by access_cases h; obtain ⟨rfl, rfl⟩ := h; exact hWa)
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
  obtain ⟨s5, hE5, hM5, g5⟩ := brun_x_step (C := ghelloC P) (mem := mem) (ld := ld) (fm := ghelloFm) (tab := ghelloTab) hE4 hM4
    (by rw [r4]; exact ghelloFm_none (by decide) (by decide)) (by rw [r4]; rfl)
    (by rw [r4]; rfl) (exec_endbr64' σ4 m1 4) (fun a k h => by access_cases h)
  generalize hσ5 : ({ σ4 with rip := σ4.rip + BitVec.ofNat 64 4 } : State) = σ5 at hE5
  have r5 : σ5.rip = 0x401044#64 := by rw [← hσ5]; show σ4.rip + _ = _; rw [r4]; decide
  have hld : ld (σ5.rip + BitVec.ofNat 64 6 + (0x2fb6#32).signExtend 64) = some putsF := by
    rw [r5, show (0x401044#64 + BitVec.ofNat 64 6 + (0x2fb6#32).signExtend 64) = gotPuts by decide]
    exact hgot
  have hE6 := Enc.next hE5 { σ5 with rip := putsF } rfl rfl putsF rfl
  have hM6 := hM5.congr (wbytes_upd s5 f .rip (Val.i64 putsF))
  have d6 : ({ σ5 with rip := putsF } : State).read .rdi = ghMsg := by
    rw [read_with_rip, ← hσ5, read_with_rip]; exact d4
  have p6 : ({ σ5 with rip := putsF } : State).read .rsp = σ3.read .rsp - 8#64 := by
    rw [read_with_rip, ← hσ5, read_with_rip]; exact p4
  rw [← p6] at hra
  rw [← p6] at hWa
  obtain ⟨evs, hb, he⟩ := ghelloB_mid_of (P := P) (mem := mem) (W := W) (ld := ld) hA hE6 hM6 rfl d6
    hra hWa
    (by rw [p6, p3, show R - 8#64 - 8#64 + 16#64 = R by bv_omega]; exact hmr)
    (by rw [p6, p3, show R - 8#64 - 8#64 + 16#64 = R by bv_omega]; exact hW0) hk1 hk
  exact ⟨_, g1 _ (g2 _ (g3 _ (g4 _ (g5 _ (.jmpInd hE5.2.2.1
    (by rw [r5]; exact ghelloFm_none (by decide) (by decide)) (by rw [r5]; rfl) hld hb))))), he⟩

/-! ## The equivalence -/

/-- **The actual linked bytes ≡ the WASI hello, relative to the `puts` contract.** For the code
table decoded from the bytes of `main` and `puts@plt` (`tabAt_ghello`), `GOT[puts]` read as the
import's address, `main` entered at `0x401050` with the start-up contract's return address on a
stack inside GM's window, and any `puts` meeting `putsC1` and admitting each output: the
observable traces of the dispatcher runs on GM are those of the WASI hello. -/
theorem ghelloB_equiv {P : ImportC} (hP : Meets P putsC1) {ld : Word → Option Word}
    (hA : ∀ args k, args.head? = some ghMsg → 1 ≤ k → k ≤ 14 →
      ∃ v, P mem args ((helloMsg.take k).map (.wr 1)) (some v))
    (hstr : cstr mem ghMsg = some msgS) (hgot : ld gotPuts = some putsF) {σ : State}
    (hE : Enc s f σ) (hM : MemEnc s f mem W) (hrw : W.rw = true) (hrip : σ.rip = 0x401050#64)
    (hret : Silmaril.X86.Ext.loadN mem (σ.read .rsp) 8 = some mainRet)
    (hW0 : W.Holds (σ.read .rsp)) (hW16 : W.Holds (σ.read .rsp - 16#64))
    (h16 : 16 ≤ (σ.read .rsp).toNat) :
    ElfWasiEquiv (blinkObs (ghelloC P) mem W ld ghelloFm ghelloTab s f) helloWasi S1 := by
  refine ⟨fun o ⟨evs, hb, ho⟩ => ?_, fun o ho => ?_⟩
  · obtain ⟨k, hk1, hk, hp⟩ := ghelloB_run hP hstr hgot hE hM hrw hrip hret hW0 hW16 h16 hb
    exact (helloWasi_obs o).2 ⟨k, hk1, hk, ho.trans hp⟩
  · obtain ⟨k, hk1, hk, hp⟩ := (helloWasi_obs o).1 ho
    obtain ⟨evs, hb, he⟩ := ghelloB_run_of hA hgot hE hM hrw hrip hret hW0 hW16 h16 hk1 hk
    exact ⟨evs, hb, he ▸ hp⟩

/-- **With the bytes and `glibc.wat`'s `puts`**: the table is the bytes in `mem`, and the
dispatcher runs of the linked hello with `glibc.wat`'s `puts` ≡ the WASI hello. -/
theorem ghelloB_equiv_impl {ld : Word → Option Word}
    (hpb : mem.fetchBytes 0x401040 pltBytes.length = some pltBytes)
    (hmb : mem.fetchBytes 0x401050 mainBytes.length = some mainBytes)
    (hstr : cstr mem ghMsg = some msgS) (hgot : ld gotPuts = some putsF) {σ : State}
    (hE : Enc s f σ) (hM : MemEnc s f mem W) (hrw : W.rw = true) (hrip : σ.rip = 0x401050#64)
    (hret : Silmaril.X86.Ext.loadN mem (σ.read .rsp) 8 = some mainRet)
    (hW0 : W.Holds (σ.read .rsp)) (hW16 : W.Holds (σ.read .rsp - 16#64))
    (h16 : 16 ≤ (σ.read .rsp).toNat) :
    TabAt mem ghelloTab ∧
      ElfWasiEquiv (blinkObs (ghelloC putsImpl) mem W ld ghelloFm ghelloTab s f) helloWasi S1 :=
  ⟨tabAt_ghello hpb hmb, ghelloB_equiv putsImpl_meets
    (fun args k hp hk1 hk => putsImpl_admits hstr args k hp hk1 hk) hstr hgot hE hM hrw hrip hret
    hW0 hW16 h16⟩

end Silmaril.Sim.GlibcBridge
