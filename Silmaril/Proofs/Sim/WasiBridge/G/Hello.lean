module

public import Silmaril.Proofs.Sim.WasiBridge.G.Wasm
public import Silmaril.Sim.WasiBridge.Thms

/-!
# Hello world: the x86 process ≡ the simulator run ≡ the WASI program

* `itemsAt_hello`: the bytes `helloBytes` decode to `helloItems` (by `decide`).
* `hello_procRun`: for every answer `1 ≤ j ≤ 14` of the environment, the process has a run with
  the observables `helloObs j` (and one stopping after the write).
* `helloWasi_obs`: the observable traces of the WASI hello are the prefixes of `helloObs k`.
* **`hello_equiv`**: for every environment meeting `EnvS1` and every launch state holding the
  bytes, the message and defined flags, the process (LPS's user machine) is equivalent to the
  interaction runs of the G simulator's code with the `sys2wasi` answers, and to the WASI hello
  (`ElfWasiEquiv … helloWasi S1`).
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS (Event)
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Sim.X86.G

/-! ## The bytes -/

theorem itemAt_ins {mem : Memory} {a : Word} {bs : List Byte} {i : Silmaril.X86.Ext.Instr}
    (hf : mem.fetchBytes a.toNat bs.length = some bs) (hd : Silmaril.X86.Ext.decode bs = some (i, bs.length))
    (h2 : bs.take 2 ≠ [0x0f, 0x05]) (hl : 2 ≤ bs.length) :
    Silmaril.X86.Ext.fetch mem a.toNat = .decoded i bs.length ∧ ¬ SysAt mem a := by
  refine ⟨Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨bs, hf, hd⟩, fun hs => h2 ?_⟩
  have h := Silmaril.Process.Memory.readWith_sub_range (offset := 0) (len := 2) hf (by omega) (by omega)
  simp only [Nat.add_zero, List.drop_zero] at h
  unfold SysAt Silmaril.Process.Memory.fetchBytes at hs
  rw [hs] at h
  exact (Option.some.inj h).symm

theorem itemsAt_hello {mem : Memory} {a : Word} (hb : BytesAt mem a helloBytes) :
    ItemsAt mem a helloItems := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hb
  have i1 := itemAt_ins (i := .movI .q (.reg .rax) 1) h1 (by decide) (by decide) (by decide)
  have i2 := itemAt_ins (i := .movI .q (.reg .rdi) 1) h2 (by decide) (by decide) (by decide)
  have i3 := itemAt_ins (i := .movabs .rsi msgAddr) h3 (by decide) (by decide) (by decide)
  have i4 := itemAt_ins (i := .movI .q (.reg .rdx) 14) h4 (by decide) (by decide) (by decide)
  have i6 := itemAt_ins (i := .movI .q (.reg .rax) 60) h6 (by decide) (by decide) (by decide)
  have i7 := itemAt_ins (i := .movI .q (.reg .rdi) 0) h7 (by decide) (by decide) (by decide)
  exact ⟨i1.1, i1.2, i2.1, i2.2, i3.1, i3.2, i4.1, i4.2, h5, i6.1, i6.2, i7.1, i7.2, h8, trivial⟩

/-! ## Process runs -/

theorem lpsStep_mov {i : Silmaril.X86.Ext.Instr} {n : Nat} (hc : (emit i n).isSome)
    {σ σ' : State} {mem : Memory} (hf : Silmaril.X86.Ext.fetch mem σ.rip.toNat = .decoded i n)
    (hns : ¬ SysAt mem σ.rip) (hσ : FlagsDef σ) (hx : Silmaril.X86.Ext.exec i σ mem n = .ok σ' mem) :
    lpsStep ⟨σ, mem⟩ = some ⟨σ', mem⟩ ∧ FlagsDef σ' := by
  obtain ⟨code, hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨σ'', hx', hst, hfd, -⟩ := lpsStep_ins (m := ⟨σ, mem⟩) hc hf hns hσ
  rw [hx] at hx'
  simp only [Silmaril.X86.Ext.Result.ok.injEq] at hx'
  obtain ⟨rfl, -⟩ := hx'
  exact ⟨hst, hfd⟩

variable {E : SysEnv} {Ok : E.Model → Prop} {Chan : E.Model → Word → Prop}

theorem fd32_one' : Silmaril.Process.LPS.fd32 (1 : Word) = 1 := by decide

/-- The cores along the run of `hello`. -/
def hs1 (σ : State) : State := movStep σ .rax ((1 : BitVec 32).signExtend 64) 7
def hs2 (σ : State) : State := movStep (hs1 σ) .rdi ((1 : BitVec 32).signExtend 64) 7
def hs3 (σ : State) : State := movStep (hs2 σ) .rsi msgAddr 10
def hs4 (σ : State) : State := movStep (hs3 σ) .rdx ((14 : BitVec 32).signExtend 64) 7
def hs6 (τ : State) : State := movStep τ .rax ((60 : BitVec 32).signExtend 64) 7
def hs7 (τ : State) : State := movStep (hs6 τ) .rdi ((0 : BitVec 32).signExtend 64) 7

theorem hs4_regs (σ : State) : (hs4 σ).read .rax = 1 ∧ (hs4 σ).read .rdi = 1 ∧
    (hs4 σ).read .rsi = msgAddr ∧ (hs4 σ).read .rdx = 14#64 := by
  simp [hs4, hs3, hs2, hs1]

theorem hs7_regs (τ : State) : (hs7 τ).read .rax = 60 ∧ (hs7 τ).read .rdi = 0 := by
  simp [hs7, hs6]

/-- **The process runs of `hello`**, for each answer `j` of the environment. -/
theorem hello_procRun (hE : EnvS1 E Ok Chan) {mem : Memory} {σ : State}
    (hit : ItemsAt mem σ.rip helloItems) (hmsg : wsrc mem msgAddr 14#64 = helloMsg)
    (hσ : FlagsDef σ) (e : E.Model) (hok : Ok e) (hchan : Chan e 1) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ 14) :
    (∃ tr, ProcRun lpsStep E ⟨σ, mem⟩ e tr ∧ obsTrace tr = (helloMsg.take j).map (.wr 1)) ∧
    (∃ tr, ProcRun lpsStep E ⟨σ, mem⟩ e tr ∧ obsTrace tr = helloObs j) := by
  obtain ⟨hf1, hn1, hf2, hn2, hf3, hn3, hf4, hn4, hs5, hf6, hn6, hf7, hn7, hs8, -⟩ := hit
  obtain ⟨st1, d1⟩ := lpsStep_mov (σ := σ) (by decide) hf1 hn1 hσ (exec_movI _ _ _ mem 7)
  obtain ⟨st2, d2⟩ := lpsStep_mov (σ := hs1 σ) (by decide) hf2 hn2 d1 (exec_movI _ _ _ mem 7)
  obtain ⟨st3, d3⟩ := lpsStep_mov (σ := hs2 σ) (by decide) hf3 hn3 d2 (exec_movabs _ _ _ mem 10)
  obtain ⟨st4, d4⟩ := lpsStep_mov (σ := hs3 σ) (by decide) hf4 hn4 d3 (exec_movI _ _ _ mem 7)
  obtain ⟨ch, -⟩ := X86FlagChoices.compatible_exists σ.flags
  obtain ⟨hrax, hrdi, hrsi, hrdx⟩ := hs4_regs σ
  have hsrc : wsrc mem ((hs4 σ).read .rsi) ((hs4 σ).read .rdx) = helloMsg := by rw [hrsi, hrdx, hmsg]
  obtain ⟨e', hok', harm⟩ := hE.admitsWrite ⟨hs4 σ, mem⟩ e ch j hok hs5 hrax
    (by show Chan e (Silmaril.Process.LPS.fd32 ((hs4 σ).read .rdi)); rw [hrdi, fd32_one']; exact hchan)
    (by show Silmaril.Process.LPS.modeledRwRangeWith _ ((hs4 σ).read .rsi) ((hs4 σ).read .rdx) = true
        rw [hrsi, hrdx]; decide)
    (by show (hs4 σ).read .rdx ≠ 0; rw [hrdx]; decide) hj1
    (by show j ≤ (wsrc mem ((hs4 σ).read .rsi) ((hs4 σ).read .rdx)).length; rw [hsrc]; exact hj)
  simp only [hsrc] at harm
  have hw : obsTrace ((helloMsg.take j).map (Event.writeEv (Silmaril.Process.LPS.fd32 ((hs4 σ).read .rdi)))) =
      (helloMsg.take j).map (.wr 1) := by rw [obsTrace_writes, hrdi, fd32_one']; rfl
  have run4 : ∀ {tr}, ProcRun lpsStep E ⟨hs4 σ, mem⟩ e tr → ProcRun lpsStep E ⟨σ, mem⟩ e tr :=
    fun h => .step st1 (.step st2 (.step st3 (.step st4 h)))
  refine ⟨⟨_, run4 (.resume hs5 harm (.stop _ _)), by rw [List.append_nil]; exact hw⟩, ?_⟩
  let σ₅ := sysResume (hs4 σ) ch (Silmaril.Process.LPS.lenWord (helloMsg.take j))
  have d5 : FlagsDef σ₅ := flagsDef_sysResume _ _ _
  obtain ⟨st6, d6⟩ := lpsStep_mov (σ := σ₅) (by decide) hf6 hn6 d5 (exec_movI _ _ _ mem 7)
  obtain ⟨st7, d7⟩ := lpsStep_mov (σ := hs6 σ₅) (by decide) hf7 hn7 d6 (exec_movI _ _ _ mem 7)
  obtain ⟨h60, h0⟩ := hs7_regs σ₅
  obtain ⟨fs, hx⟩ := hE.admitsExit ⟨hs7 σ₅, mem⟩ e' ch hok' hs8 (.inl h60)
  refine ⟨_, run4 (.resume hs5 harm (.step st6 (.step st7 (.halt hs8 hx)))), ?_⟩
  rw [obsTrace_append, hw, h0]
  rfl

/-! ## The WASI side -/

/-- The full WASI trace for the answer `k`. -/
def helloT (k : Nat) : List Silmaril.Wasi.WEv :=
  [.imp (Silmaril.Wasi.Versions.P1.fn "fd_write") [.u32 1, .record [Silmaril.Wasi.bytesV helloMsg]]
     (Silmaril.Wasi.Versions.P1.okAns (some (.u32 (BitVec.ofNat 32 k)))),
   .imp (Silmaril.Wasi.Versions.P1.fn "proc_exit") [.u32 0] none]

theorem helloT_obs {k : Nat} (hk : k ≤ 14) : (helloT k).flatMap p1Obs = helloObs k := by
  have : (BitVec.ofNat 32 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  simp [helloT, p1Obs, ofP1, Silmaril.Wasi.Versions.P1.okAns, Silmaril.Wasi.okV, sysObs, bytesOf_bytesV,
    this, helloObs]

theorem helloT_in (k : Nat) : InP1 S1 (helloT k) := by
  intro ev he s hs
  simp [helloT] at he
  rcases he with rfl | rfl <;> simp [ofP1, Silmaril.Wasi.Versions.P1.okAns, Silmaril.Wasi.okV] at hs <;>
    subst hs <;> simp [SysEv.In, SysEv.name, S1]

theorem flatMap_prefix {α β : Type} (g : α → List β) {a b : List α} (h : a <+: b) :
    a.flatMap g <+: b.flatMap g := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.flatMap g, by simp⟩

/-- **The observables of the WASI hello.** -/
theorem helloWasi_obs (o : List Obs) :
    helloWasi.obs S1 o ↔ ∃ k, 1 ≤ k ∧ k ≤ 14 ∧ o <+: helloObs k := by
  constructor
  · rintro ⟨t, ⟨k, hk1, hk, ht⟩, -, ho⟩
    exact ⟨k, hk1, hk, ho.trans (by rw [← helloT_obs hk]; exact flatMap_prefix _ ht)⟩
  · rintro ⟨k, hk1, hk, ho⟩
    exact ⟨helloT k, ⟨k, hk1, hk, List.prefix_refl _⟩, helloT_in k, by rw [helloT_obs hk]; exact ho⟩

/-! ## Hello: process ≡ simulator ≡ WASI -/

theorem gitems_hello : GItems helloItems := by
  simp only [helloItems, GItems]; decide

/-- **Hello world, end to end.** For every environment answering like LPS's proved arms
(`EnvS1`) with descriptor 1 bound to the live channel 1, and every launch state whose memory
holds the bytes of `hello` at `rip` and the message at `0x402000`, with defined modelled flags:
the observable traces of the process are those of the interaction runs of the G simulator's
code for those bytes (with the `sys2wasi` adapter's answers), and those of the WASI hello. -/
theorem hello_equiv (hE : EnvS1 E Ok Chan) {mem : Memory} {σ : State} (hb : BytesAt mem σ.rip helloBytes)
    (hmsg : wsrc mem msgAddr 14#64 = helloMsg) (hσ : FlagsDef σ) (e : E.Model) (hok : Ok e)
    (hchan : Chan e 1) :
    Equiv (procObs lpsStep E ⟨σ, mem⟩ e) (wasmObs mem (encStore (H := Nat) σ) encFrame helloItems) ∧
      ElfWasiEquiv (procObs lpsStep E ⟨σ, mem⟩ e) helloWasi S1 := by
  have hit := itemsAt_hello hb
  have hEnc := enc_encStore (H := Nat) σ
  have pw : Refines (procObs lpsStep E ⟨σ, mem⟩ e) (wasmObs mem (encStore (H := Nat) σ) encFrame helloItems) := by
    rintro o ⟨tr, hr, rfl⟩
    obtain ⟨evs, rest, tr₁, tr₂, rfl, hw, hobs, hend⟩ :=
      procRun_wrun (f := encFrame) hE hr helloItems (encStore σ) hok rfl hit gitems_hello hEnc hσ
    obtain ⟨hrest, hnr, -⟩ := hello_wrun hmsg hEnc hw
    rcases hend with rfl | h | h
    · exact ⟨evs, rest, hw, by rw [List.append_nil, hobs]⟩
    · exact (hrest h).elim
    · exact (hnr h).elim
  have wv : Refines (wasmObs mem (encStore (H := Nat) σ) encFrame helloItems) (helloWasi.obs S1) := by
    rintro o ⟨evs, rest, hw, rfl⟩
    obtain ⟨-, -, k, hk1, hk, ho⟩ := hello_wrun hmsg hEnc hw
    exact (helloWasi_obs _).2 ⟨k, hk1, hk, ho⟩
  have vp : Refines (helloWasi.obs S1) (procObs lpsStep E ⟨σ, mem⟩ e) := by
    intro o ho
    obtain ⟨k, hk1, hk, ho⟩ := (helloWasi_obs o).1 ho
    rcases List.prefix_concat_iff.1 ho with rfl | ho
    · obtain ⟨tr, hr, h⟩ := (hello_procRun hE hit hmsg hσ e hok hchan hk1 hk).2
      exact ⟨tr, hr, h⟩
    · have hl : o.length ≤ k := by
        have := ho.length_le
        simp at this; omega
      have heq : o = (helloMsg.take o.length).map (.wr 1) := by
        rw [List.prefix_iff_eq_take.1 ho, ← List.map_take, List.take_take, Nat.min_eq_left hl]
        simp
      by_cases h0 : o.length = 0
      · rw [List.length_eq_zero_iff.1 h0]
        exact ⟨[], .stop _ _, rfl⟩
      · obtain ⟨tr, hr, h⟩ :=
          (hello_procRun hE hit hmsg hσ e hok hchan (j := o.length) (by omega) (by omega)).1
        exact ⟨tr, hr, by rw [h, ← heq]⟩
  exact ⟨⟨pw, wv.trans vp⟩, ⟨pw.trans wv, vp⟩⟩

/-- **Hello world under LPS's Linux model**: the environment of LPS's proved syscall arms
(`IoSpec.lpsEnv`), from any LPS model binding descriptors to equal channels with descriptor 1
live (e.g. LPS's initial model, `initModel_ok`, `initModel_chan1`). No assumption on the
environment remains. -/
theorem hello_equiv_lps (segs : List Silmaril.Process.LPS.Segment) {mem : Memory} {σ : State}
    (hb : BytesAt mem σ.rip helloBytes) (hmsg : wsrc mem msgAddr 14#64 = helloMsg) (hσ : FlagsDef σ)
    (e : Silmaril.Process.LPS.Model) (hok : LpsOk e) (hchan : LpsChan e 1) :
    Equiv (procObs lpsStep (lpsEnv segs) ⟨σ, mem⟩ e)
        (wasmObs mem (encStore (H := Nat) σ) encFrame helloItems) ∧
      ElfWasiEquiv (procObs lpsStep (lpsEnv segs) ⟨σ, mem⟩ e) helloWasi S1 :=
  hello_equiv (lpsEnv_S1 segs) hb hmsg hσ e hok hchan

end Silmaril.Sim.WasiBridge.G
