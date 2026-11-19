module

public import Silmaril.Sim.WasiBridge.G.Defs

/-!
# LPS's proved syscall arms meet `EnvS1`

* `resume_eq`: the state LPS resumes with after a syscall (other than `arch_prctl`) is
  `sysResume` with the effect's memory.
* **`lpsEnv_S1`**: `IoSpec.lpsEnv segs` (the arms `exitArm`, `writeArm`, `readArm`) meets
  `EnvS1` with `LpsOk` (descriptors bound to equal channels) and `LpsChan`.
* `initModel_ok`, `initModel_chan1`: LPS's initial model satisfies both for stdout.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.G

open Silmaril.X86 (Reg State MState)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec

theorem resume_eq (m : MState) (ch : X86FlagChoices.Choice) (eff : SyscallEffect)
    (h : m.core.read .rax ≠ 158#64) :
    resume (trapped ⟨m, none⟩ ch) eff = ⟨sysResume m.core ch eff.ret, applyMemoryEffect m.memory eff⟩ := by
  unfold resume trapped x86AdvancePastSvc x86ApplyEffectNative X86FlagChoices.completeState
  simp only
  split_ifs with hc
  · exact absurd (Option.some.inj hc.1) h
  · rfl

theorem applyMemoryEffect_nowrite (mem : Memory) (r : Word) (cs : List (Word × Nat)) :
    applyMemoryEffect mem ((mkEffect r [] []).withCopyins cs) = mem := rfl

theorem readableBytesAux_len (mp : Word → Option Byte) : ∀ (a : Word) (n : Nat),
    (readableBytesAux mp a n).length ≤ n
  | _, 0 => by simp [readableBytesAux]
  | a, n + 1 => by
    simp only [readableBytesAux]
    split
    · simp
    · simp only [List.length_cons]; have := readableBytesAux_len mp (a + 1) n; omega

theorem wsrc_len (mem : Memory) (buf n : Word) : ((wsrc mem buf n).length : Int) ≤ rwCountClamp n := by
  have h0 : 0 ≤ rwCountClamp n := by simp only [rwCountClamp, uns, MAX_RW_COUNT]; omega
  have h1 : rwCountClamp n ≤ 0x7ffff000 := by simp only [rwCountClamp, MAX_RW_COUNT]; omega
  have := readableBytesAux_len (viewByte mem .read) buf (zw (rwCountClamp n)).toNat
  simp only [wsrc, writeSource, readableBytes]
  simp only [zw, BitVec.toNat_ofInt] at this ⊢
  omega

theorem rax_of_toNat {w : Word} {k : Nat} (h : w.toNat = k) (hk : k < 2 ^ 64) : w = BitVec.ofNat 64 k :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk])

/-- The conclusion of `EnvS1.answers` for `lpsEnv` with `LpsOk`. -/
private def Ans (m : MState) (ch : X86FlagChoices.Choice) (o : IoOut Model) : Prop :=
  (m.core.read .rax = 1 ∧ ∃ (ds : List Byte) (e' : Model), LpsOk e' ∧ ds ≠ [] ∧
      ds <+: wsrc m.memory (m.core.read .rsi) (m.core.read .rdx) ∧
      o = .resume ⟨sysResume m.core ch (lenWord ds), m.memory⟩ e'
        (ds.map (.writeEv (fd32 (m.core.read .rdi))))) ∨
    (m.core.read .rax = 0 ∧ ∃ (bs : List Byte) (e' : Model) (eff : SyscallEffect),
      LpsOk e' ∧ eff.ret = lenWord bs ∧
      (eff = mkEffect (lenWord bs) [(m.core.read .rsi, bs)] [] ∨
        (bs = [] ∧ eff = mkEffect 0 [] [])) ∧
      o = .resume ⟨sysResume m.core ch eff.ret, applyMemoryEffect m.memory eff⟩ e'
        (bs.map (.readEv (fd32 (m.core.read .rdi))))) ∨
    ((m.core.read .rax = 60 ∨ m.core.read .rax = 231) ∧ ∃ fs,
      o = .halt [.exitEv (m.core.read .rdi &&& 255) fs])

private theorem ans_exit {m : MState} {ch : X86FlagChoices.Choice} {e : Model} {o : IoOut Model}
    (hh : exitArm.Handles (trapped ⟨m, none⟩ ch) e) (hout : exitArm.out (trapped ⟨m, none⟩ ch) e o) :
    Ans m ch o := by
  have hr : m.core.read .rax = 60 ∨ m.core.read .rax = 231 := by
    rcases hh with h | h
    · exact .inl (rax_of_toNat (k := 60) h (by norm_num))
    · exact .inr (rax_of_toNat (k := 231) h (by norm_num))
  exact .inr (.inr ⟨hr, e.fs, hout⟩)

private theorem ans_write {segs : List Segment} {m : MState} {ch : X86FlagChoices.Choice}
    {e : Model} {o : IoOut Model} (hok : LpsOk e)
    (hh : (writeArm segs).Handles (trapped ⟨m, none⟩ ch) e)
    (hout : (writeArm segs).out (trapped ⟨m, none⟩ ch) e o) : Ans m ch o := by
  have hr : m.core.read .rax = 1 := rax_of_toNat (k := 1) hh.1 (by norm_num)
  obtain ⟨c, hc, ds, hl, -, hds, rfl⟩ := hout
  have hc' := hok _ _ hc
  subst hc'
  refine .inl ⟨hr, ds, e, hok, ?_, ?_, ?_⟩
  · rintro rfl; simp at hl
  · rw [hds]; exact List.take_prefix _ _
  · rw [resume_eq _ _ _ (by rw [hr]; decide)]
    rfl

private theorem ans_read {segs : List Segment} {m : MState} {ch : X86FlagChoices.Choice}
    {e : Model} {o : IoOut Model} (hok : LpsOk e)
    (hh : (readArm segs).Handles (trapped ⟨m, none⟩ ch) e)
    (hout : (readArm segs).out (trapped ⟨m, none⟩ ch) e o) : Ans m ch o := by
  have hr : m.core.read .rax = 0 := rax_of_toNat (k := 0) hh.1 (by norm_num)
  have hc := hok _ _ hh.2.1
  have h158 : m.core.read .rax ≠ 158#64 := by rw [hr]; decide
  rcases hout with ⟨-, rfl⟩ | ⟨-, bs, -, -, -, rfl⟩
  · refine .inr (.inl ⟨hr, [], e, mkEffect 0 [] [], hok, rfl, .inr ⟨rfl, rfl⟩, ?_⟩)
    rw [resume_eq _ _ _ h158]
    rfl
  · refine .inr (.inl ⟨hr, bs, e.withStdin (e.stdin.take bs.length).2,
      mkEffect (lenWord bs) [(m.core.read .rsi, bs)] [], fun fd c h => hok fd c h,
      rfl, .inl rfl, ?_⟩)
    rw [resume_eq _ _ _ h158]
    show IoOut.resume _ _ (bs.map (Event.readEv 0)) = _
    rw [hc]
    rfl

/-- **LPS's proved arms meet `EnvS1`.** -/
theorem lpsEnv_S1 (segs : List Segment) : EnvS1 (lpsEnv segs) LpsOk LpsChan where
  answers m e ch o hok _ harm := by
    obtain ⟨a, ha, hh, hout⟩ := harm
    obtain rfl | rfl | rfl : a = exitArm ∨ a = writeArm segs ∨ a = readArm segs := by
      simpa only [lpsArms, List.mem_cons, List.not_mem_nil, or_false] using ha
    · exact ans_exit hh hout
    · exact ans_write hok hh hout
    · exact ans_read hok hh hout
  admitsWrite m e ch k hok _ hrax hchan hmod hrdx hk1 hk := by
    refine ⟨e, hok, writeArm segs, by simp [lpsArms], ?_, ?_⟩
    · refine ⟨by show (m.core.read .rax).toNat = 1; rw [hrax]; rfl, _, hchan.1,
        by simpa [wIs0] using hchan.2, hmod, by show (m.core.read .rdx == 0) = false; simpa using hrdx, ?_⟩
      intro h
      have h' : wsrc m.memory (m.core.read .rsi) (m.core.read .rdx) = [] := h
      have hk0 : k = 0 := by simpa [h'] using hk
      omega
    · refine ⟨_, hchan.1, (wsrc m.memory (m.core.read .rsi) (m.core.read .rdx)).take k, ?_, ?_, ?_, ?_⟩
      · rw [List.length_take]; omega
      · exact le_trans (by simp) (wsrc_len m.memory (m.core.read .rsi) (m.core.read .rdx))
      · simp only [List.length_take, Nat.min_eq_left hk]; rfl
      · rw [resume_eq _ _ _ (by rw [hrax]; decide)]
        rfl
  admitsExit m e ch hok _ hr := by
    refine ⟨e.fs, exitArm, by simp [lpsArms], ?_, rfl⟩
    rcases hr with h | h
    · exact .inl (by show (m.core.read .rax).toNat = 60; rw [h]; rfl)
    · exact .inr (by show (m.core.read .rax).toNat = 231; rw [h]; rfl)

theorem initModel_ok (reserved : List (Word × Word)) (brk0 mbase sp : Word) (lim : Int)
    (inp : ProcInput) : LpsOk (initModel reserved brk0 mbase sp lim inp) := by
  intro fd c h
  have h' : fdLookup [(0, FdEntry.channel 0), (1, FdEntry.channel 1), (2, FdEntry.channel 2)] fd =
      some (.channel c) := h
  simp only [fdLookup] at h'
  split_ifs at h' with h0 h1 h2 <;> simp_all

theorem initModel_chan1 (reserved : List (Word × Word)) (brk0 mbase sp : Word) (lim : Int)
    (inp : ProcInput) : LpsChan (initModel reserved brk0 mbase sp lim inp) 1 := ⟨rfl, by decide⟩

end Silmaril.Sim.WasiBridge.G
