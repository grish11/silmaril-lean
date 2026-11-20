module

public import Silmaril.Containers.HttpServe.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Ports.Thms
public import Silmaril.Process.LPS.Probes.KitMemory
public import Silmaril.Proofs.Containers.HttpServe.Walk

/-!
# Proofs: the server's send-retry loop

Proofs for `Silmaril.Containers.HttpServe.Thms`. From the loop head (segment offset 228) with
`k < 40` octets sent, over an abstract core: one iteration on a connection without a pending error
(`iter_goes`: any non-empty prefix of the rest is sent; the pointer and the remaining count move
by its length; the loop continues while octets remain), and with a pending reset or timeout
(`iter_err`: the error, exit 14). `loop`: by strong induction on the remaining count, every
execution from the loop head reaches the drain (offset 263) with all 40 octets sent, or exits 14
with a prefix sent; no task creation. Register reads go through the abstract core's write chain;
the sizes of the decoded instructions appear as `Sz.q.bits` in instance arguments, so the
arithmetic is normalised with `*_qq` lemmas proved by `rfl`.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Containers.HttpServe.Loop

open Silmaril.Containers Silmaril.Containers.Lps Silmaril.Containers.HttpServe
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes
open Silmaril.Proofs.Containers.HttpServe.Walk

theorem okBytes_eq : okBytes.map UInt8.ofBitVec = Fixtures.okResponse :=
  Silmaril.Proofs.Containers.HttpServe.response_in_image

/-- The choices of a send of the rest at `k`: a non-empty prefix of what remains. -/
def SendOk (k : Nat) (ds : List Byte) : Prop :=
  1 ≤ ds.length ∧ ds.length ≤ 40 - k ∧ ds = (okBytes.drop k).take ds.length

theorem clear44 (P : Probe) (core : Silmaril.X86.State) (k : Nat) (hk : k < 40)
    (hrdi : core.read .rdi = 4) (hrsi : core.read .rsi = BitVec.ofNat 64 (4194304 + 345 + k))
    (hrdx : core.read .rdx = BitVec.ofNat 64 (40 - k)) (hr10 : core.read .r10 = 0x4000)
    (hr8 : core.read .r8 = 0) (hr9 : core.read .r9 = 0) :
    NativeX86.All.boundarySuspect 44 (P.sysIn core 44) = false := by
  rw [Probe.boundarySuspect_regs P (by decide +kernel)]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff, hrdi, hrsi, hrdx, hr10, hr8, hr9]
  refine ⟨by decide, ?_, ?_, by decide, by decide, by decide⟩ <;>
    exact Probe.inGuardWindow_of_lt (by simp only [uns, BitVec.toNat_ofNat, taskSizeMaxX86]; omega)

theorem clear_small (P : Probe) (core : Silmaril.X86.State) (num : Nat) (n : Word)
    (noConst : NativeX86.All.constPtrArgs num = [])
    (h0 : uns (core.read .rdi) < taskSizeMaxX86) (h1 : uns (core.read .rsi) < taskSizeMaxX86)
    (h2 : uns (core.read .rdx) < taskSizeMaxX86) (h3 : uns (core.read .r10) < taskSizeMaxX86)
    (h4 : uns (core.read .r8) < taskSizeMaxX86) (h5 : uns (core.read .r9) < taskSizeMaxX86) :
    NativeX86.All.boundarySuspect num (P.sysIn core n) = false := by
  rw [Probe.boundarySuspect_regs P noConst]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff]
  exact ⟨Probe.inGuardWindow_of_lt h0, Probe.inGuardWindow_of_lt h1, Probe.inGuardWindow_of_lt h2,
    Probe.inGuardWindow_of_lt h3, Probe.inGuardWindow_of_lt h4, Probe.inGuardWindow_of_lt h5⟩

theorem small32 (x : BitVec 32) : uns (BitVec.setWidth 64 x) < taskSizeMaxX86 := by
  simp only [uns, BitVec.toNat_setWidth, taskSizeMaxX86]
  have := x.isLt
  omega

theorem send_outP (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)]
    (core : Silmaril.X86.State) (n : Word) (m : Model) (k : Nat) (hk : k < 40) (hn : n = 44)
    (hrdi : core.read .rdi = 4) (hrsi : core.read .rsi = BitVec.ofNat 64 (4194304 + 345 + k))
    (hrdx : core.read .rdx = BitVec.ofNat 64 (40 - k)) (hr10 : core.read .r10 = 0x4000)
    (hr8 : core.read .r8 = 0) (hr9 : core.read .r9 = 0)
    {peer : PeerAddr} {rx : NetStream}
    (hfd : fdLookup m.fds 4 = some (.socket (.connected peer 3 rx)))
    (hs : sendState (.connected peer 3 rx) = .goes 3) (o : Outcome SyscallEffect) :
    Ports.publish [8080] ((probe.launchAt en inp).sysIn core n) m o ↔ ∃ ds, SendOk k ds ∧
      o = .ok ((mkEffect (lenWord ds) [] []).withCopyins
        [(BitVec.ofNat 64 (4194304 + 345 + k), ds.length)]) m (ds.map (.writeEv 3)) := by
  obtain ⟨a, b0, b1, b2, b3, b4, b5⟩ := sysIn_args (probe.launchAt en inp) core n
  subst hn
  have hclear := clear44 (probe.launchAt en inp) core k hk hrdi hrsi hrdx hr10 hr8 hr9
  rw [Ports.publish_of_not (publishedBind_ne (by rw [a]; decide)),
    Ports.dispatches_sendto.spec_iff (by rw [a]; rfl) hclear, b0, b1, b2, b3, b4, b5,
    hrdi, hrsi, hrdx, hr10, hr8, hr9]
  have hsrc : readableBytes ((probe.launchAt en inp).sysIn core 44).mem
      (BitVec.ofNat 64 (4194304 + 345 + k)) (BitVec.ofNat 64 (40 - k)) = (okBytes.drop k).take (40 - k) := by
    unfold readableBytes
    change readableBytesAux (viewByte (probe.launchAt en inp).mem0 .read) _ _ = _
    have hl : (BitVec.ofNat 64 (40 - k)).toNat = 40 - k := by
      simp only [BitVec.toNat_ofNat]; omega
    have hb : (probe.launchAt en inp).base = 4194304 := rfl
    rw [hl, show 4194304 + 345 + k = (probe.launchAt en inp).base + (345 + k) by rw [hb]; omega,
      Probe.readableBytesAux_mem0 _ (345 + k) (40 - k) (by have hs : probe.size = 1409 := rfl; simp only [Probe.launchAt_size, hs]; omega)]
    simp only [Probe.launchAt_bytes, okBytes, List.drop_take, List.take_take, List.drop_drop]
    congr 1
    · omega
  rw [show fd32 (4 : Word) = 4 from rfl]
  have hc : modeledRwCount (BitVec.ofNat 64 (40 - k)) = true := by
    simp only [modeledRwCount, uns, rwBytesMax, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hz : wIs0 (BitVec.ofNat 64 (40 - k)) = false := by
    simp only [wIs0, beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp at this; omega
  have ha : accessOkbX86 (BitVec.ofNat 64 (4194304 + 345 + k)) (uns (BitVec.ofNat 64 (40 - k))) = true := by
    interval_cases k <;> decide
  have hne : (okBytes.drop k).take (40 - k) ≠ [] := by
    intro h
    have := congrArg List.length h
    have hlen : probe.bytes.length = 1409 := by decide
    simp [okBytes, hlen] at this
    omega
  rw [Ports.sendto_goes_iff _ _ _ _ m o hfd hs hc hz ha hsrc hne]
  have hu : uns (BitVec.ofNat 64 (40 - k)) = ((40 - k : Nat) : Int) := by
    simp only [uns, BitVec.toNat_ofNat]; omega
  rw [hu]
  constructor
  · rintro ⟨ds, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨ds, ⟨by omega, by omega, ?_⟩, rfl⟩
    rw [List.take_take, Nat.min_eq_left (by omega)] at h3
    exact h3
  · rintro ⟨ds, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨ds, ⟨by omega, by omega, ?_⟩, rfl⟩
    rw [List.take_take, Nat.min_eq_left (by omega)]
    exact h3

theorem send_errP (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)]
    (core : Silmaril.X86.State) (n : Word) (m : Model) (k : Nat) (hk : k < 40) (hn : n = 44)
    (hrdi : core.read .rdi = 4) (hrsi : core.read .rsi = BitVec.ofNat 64 (4194304 + 345 + k))
    (hrdx : core.read .rdx = BitVec.ofNat 64 (40 - k)) (hr10 : core.read .r10 = 0x4000)
    (hr8 : core.read .r8 = 0) (hr9 : core.read .r9 = 0)
    {peer : PeerAddr} {rx : NetStream} {e : Int}
    (hfd : fdLookup m.fds 4 = some (.socket (.connected peer 3 rx)))
    (hs : sendState (.connected peer 3 rx) = .err e peer 3) (o : Outcome SyscallEffect) :
    Ports.publish [8080] ((probe.launchAt en inp).sysIn core n) m o ↔ ∃ _ : Unit, True ∧
      o = .ok ((mkEffect (errnoRet e) [] []).withCopyins [])
        (m.withFds (fdInsert m.fds 4 (.socket (.reset peer 3)))) [] := by
  obtain ⟨a, b0, b1, b2, b3, b4, b5⟩ := sysIn_args (probe.launchAt en inp) core n
  subst hn
  have hclear := clear44 (probe.launchAt en inp) core k hk hrdi hrsi hrdx hr10 hr8 hr9
  rw [Ports.publish_of_not (publishedBind_ne (by rw [a]; decide)),
    Ports.dispatches_sendto.spec_iff (by rw [a]; rfl) hclear, b0, b1, b2, b3, b4, b5,
    hrdi, hrsi, hrdx, hr10, hr8, hr9, show fd32 (4 : Word) = 4 from rfl]
  have hc : modeledRwCount (BitVec.ofNat 64 (40 - k)) = true := by
    simp only [modeledRwCount, uns, rwBytesMax, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have ha : accessOkbX86 (BitVec.ofNat 64 (4194304 + 345 + k)) (uns (BitVec.ofNat 64 (40 - k))) = true := by
    interval_cases k <;> decide
  rw [Ports.sendto_err_iff _ _ _ _ m o hfd hs hc ha]
  exact ⟨fun h => ⟨(), trivial, h⟩, fun ⟨_, _, h⟩ => h⟩

theorem execN_conseq {sg : List Segment} {sp : Sys SyscallEffect} {o : Oracle}
    {c : Silmaril.Process.LPS.Config (isaOf o)} {Q Q' : Omni.Post (isaOf o)}
    (h : ExecN sg sp c Q) (himp : ∀ tr out, Q tr out → Q' tr out) : ExecN sg sp c Q' :=
  ⟨Omni.exec_conseq h.1 himp, h.2⟩

theorem xor_self' {n : Nat} (x : BitVec n) : x ^^^ x = 0#n := by
  ext i; simp

theorem sub_mix (x y : BitVec 64) :
    @HSub.hSub (BitVec 64) (BitVec 64) (BitVec 64)
      (@instHSub (BitVec Silmaril.X86.Ext.Sz.q.bits) (@BitVec.instSub Silmaril.X86.Ext.Sz.q.bits)) x y = x - y := rfl

theorem add_mix (x y : BitVec 64) :
    @HAdd.hAdd (BitVec 64) (BitVec 64) (BitVec 64)
      (@instHAdd (BitVec Silmaril.X86.Ext.Sz.q.bits) (@BitVec.instAdd Silmaril.X86.Ext.Sz.q.bits)) x y = x + y := rfl

theorem setW_q (x : BitVec 64) : (BitVec.setWidth Silmaril.X86.Ext.Sz.q.bits x : BitVec 64) = x :=
  BitVec.setWidth_eq x

theorem sub_qq (x y : BitVec 64) :
    @HSub.hSub (BitVec Silmaril.X86.Ext.Sz.q.bits) (BitVec Silmaril.X86.Ext.Sz.q.bits)
      (BitVec Silmaril.X86.Ext.Sz.q.bits)
      (@instHSub (BitVec Silmaril.X86.Ext.Sz.q.bits) (@BitVec.instSub Silmaril.X86.Ext.Sz.q.bits))
      x y = x - y := rfl

theorem add_qq (x y : BitVec 64) :
    @HAdd.hAdd (BitVec Silmaril.X86.Ext.Sz.q.bits) (BitVec Silmaril.X86.Ext.Sz.q.bits)
      (BitVec Silmaril.X86.Ext.Sz.q.bits)
      (@instHAdd (BitVec Silmaril.X86.Ext.Sz.q.bits) (@BitVec.instAdd Silmaril.X86.Ext.Sz.q.bits))
      x y = x + y := rfl

theorem and_self_qq (x : BitVec 64) :
    @HAnd.hAnd (BitVec Silmaril.X86.Ext.Sz.q.bits) (BitVec Silmaril.X86.Ext.Sz.q.bits)
      (BitVec Silmaril.X86.Ext.Sz.q.bits)
      (@instHAndOfAndOp (BitVec Silmaril.X86.Ext.Sz.q.bits) (@BitVec.instAndOp Silmaril.X86.Ext.Sz.q.bits))
      x x = x := BitVec.and_self

theorem and_self_q (x : BitVec 64) :
    @HAnd.hAnd (BitVec 64) (BitVec 64) (BitVec 64)
      (@instHAndOfAndOp (BitVec Silmaril.X86.Ext.Sz.q.bits) (@BitVec.instAndOp Silmaril.X86.Ext.Sz.q.bits)) x x = x :=
  BitVec.and_self

set_option hygiene false in
macro "hseval" : tactic =>
  `(tactic| (simp (config := {decide := true}) [Probe.complete, Probe.resume,
            Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write,
            Silmaril.X86.Reg.ofBitVec, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
            Silmaril.X86.Ext.Sz.ofW, Silmaril.X86.Ext.mkReg, Silmaril.X86.Ext.ModRM.ofByte,
            Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.Rex.zero, Silmaril.X86.Ext.Rex.ofByte, x86ExtNative, x86Ext,
            Silmaril.X86.Ext.exec, condLits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN,
            BitVec.msb_eq_decide, hrsi', hrdx', hr12', xor_self']; try rfl))

set_option hygiene false in
macro "astep " off:term:max len:term:max ins:term:max : tactic =>
  `(tactic| refine Silmaril.Containers.Lps.oexecN_instr _ _ (off := $off) (len := $len) (instruction := $ins)
      hh hl (by simp [hrip, hb, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write]) (by oprobe_side) (by oprobe_side) (by oprobe_side) (by oprobe_side)
      (by rfl) ?_)

macro "smallfin" : tactic => `(tactic| try first | exact small32 _ | simp [uns, taskSizeMaxX86])

set_option hygiene false in
macro "lenfin" : tactic => `(tactic| (simp [okBytes, hlen] <;> omega))

macro "aside" : tactic => `(tactic| first | oprobe_side | assumption | sside)

/-- **One iteration of the send loop** on a connection with no pending error. -/
theorem iter_goes (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)] (o : Oracle)
    {peer : PeerAddr} {rx : NetStream} (hs : sendState (.connected peer 3 rx) = .goes 3)
    (k : Nat) (hk : k < 40) (counter : Nat) (core : Silmaril.X86.State) (m : Model)
    (hrip : core.rip = 4194532#64) (hrsi : core.read .rsi = BitVec.ofNat 64 (4194304 + 345 + k))
    (hrdx : core.read .rdx = BitVec.ofNat 64 (40 - k)) (hr12 : core.read .r12 = 4)
    (hh : m.halted = none) (hl : m.vmLazy = [])
    (hfd : fdLookup m.fds 4 = some (.socket (.connected peer 3 rx)))
    (Q : Omni.Post (isaOf o))
    (hnext : ∀ (c' : Silmaril.X86.State) (cnt : Nat) (ds : List Byte), SendOk k ds →
      k + ds.length < 40 → c'.rip = 4194532#64 →
      c'.read .rsi = BitVec.ofNat 64 (4194304 + 345 + (k + ds.length)) →
      c'.read .rdx = BitVec.ofNat 64 (40 - (k + ds.length)) → c'.read .r12 = 4 →
      ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
        ((probe.launchAt en inp).ocfg o c' none cnt m) (fun tr out => Q (ds.map (.writeEv 3) ++ tr) out))
    (hdone : ∀ (c' : Silmaril.X86.State) (cnt : Nat) (ds : List Byte), SendOk k ds →
      k + ds.length = 40 → c'.rip = 4194567#64 → c'.read .r12 = 4 →
      uns (c'.read .r10) < taskSizeMaxX86 → uns (c'.read .r8) < taskSizeMaxX86 →
      uns (c'.read .r9) < taskSizeMaxX86 →
      ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
        ((probe.launchAt en inp).ocfg o c' none cnt m) (fun tr out => Q (ds.map (.writeEv 3) ++ tr) out)) :
    ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
      ((probe.launchAt en inp).ocfg o core none counter m) Q := by
  have hb : (probe.launchAt en inp).base = 4194304 := rfl
  have hb' : probe.base = 4194304 := rfl
  have hrsi' := hrsi
  have hrdx' := hrdx
  have hr12' := hr12
  simp only [Silmaril.X86.State.read] at hrsi' hrdx' hr12'
  apply Silmaril.Containers.Lps.oexecN_instr _ _ (off := 228) (len := 5) (instruction := _)
  all_goals aside
  case rip => simp [hrip, hb, hb']
  apply Silmaril.Containers.Lps.oexecN_instr _ _ (off := 233) (len := 3) (instruction := _)
  all_goals aside
  case rip => simp [hrip, hb, hb']
  apply Silmaril.Containers.Lps.oexecN_instr _ _ (off := 236) (len := 6) (instruction := _)
  all_goals aside
  case rip => simp [hrip, hb, hb']
  apply Silmaril.Containers.Lps.oexecN_instr _ _ (off := 242) (len := 3) (instruction := _)
  all_goals aside
  case rip => simp [hrip, hb, hb']
  apply Silmaril.Containers.Lps.oexecN_instr _ _ (off := 245) (len := 3) (instruction := _)
  all_goals aside
  case rip => simp [hrip, hb, hb']
  apply Silmaril.Containers.Lps.oexecN_trap _ _ (off := 248)
  all_goals aside
  case rip => simp [hrip, hb, hb']
  apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := SendOk k)
  case outcomes =>
    refine send_outP en inp _ _ m k hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfd hs
    all_goals hseval
    case refine_6 =>
      show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .r8) ^^^ BitVec.setWidth 32 (core.regs .r8)) = 0#64
      simp
    case refine_7 =>
      show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .r9) ^^^ BitVec.setWidth 32 (core.regs .r9)) = 0#64
      simp
  case live => intro _ _; exact hh
  case lazy => intro _ _; exact hl
  case inhabited => exact ⟨(okBytes.drop k).take 1, by
    have hlen : probe.bytes.length = 1409 := by decide
    refine ⟨?_, ?_, ?_⟩ <;> lenfin⟩
  case rest =>
    intro ds hds
    obtain ⟨hj1, hj2, -⟩ := id hds
    have hlen : (lenWord ds).toNat = ds.length := Silmaril.Process.LPS.Probes.lenWord_toNat ds (by omega)
    have hz : Silmaril.X86.Ext.isZeroN (lenWord ds) = false := by
      unfold Silmaril.X86.Ext.isZeroN
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg BitVec.toNat h
      rw [hlen] at this
      have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
      rw [h0] at this
      omega
    have hm : decide (9223372036854775808 ≤ (lenWord ds).toNat) = false := by
      rw [hlen]; simp; omega
    have hm' : decide (2 ^ (Silmaril.X86.Ext.Sz.q.bits - 1) ≤
        @BitVec.toNat Silmaril.X86.Ext.Sz.q.bits (lenWord ds)) = false := hm
    have hmsb0 : BitVec.msb (lenWord ds) = false := by
      rw [BitVec.msb_eq_decide]; exact hm
    have hmsb : @BitVec.msb Silmaril.X86.Ext.Sz.q.bits (lenWord ds) = false := hmsb0
    have hz' : @Silmaril.X86.Ext.isZeroN Silmaril.X86.Ext.Sz.q.bits (lenWord ds) = false := hz
    astep 250 3 (.test .q (.reg .rax) .rax)
    refine Silmaril.Containers.Lps.oexecN_instr _ _ (off := 253) (len := 2) (instruction := .jcc8 .le 0x3e#8)
      hh hl (by simp [hrip, hb, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write])
      (by oprobe_side) (by oprobe_side) (by oprobe_side) (by oprobe_side)
      (by simp (config := {decide := true}) only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval,
            Probe.resume, Probe.complete, Silmaril.X86.State.read, Silmaril.X86.State.write,
            Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.logicFlagsN,
            setW_q, and_self_q, and_self_qq, BitVec.msb_eq_decide, hz, hz', hm, hm', hmsb, Bool.xor_false, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.kXor,
            Bool.false_xor, ↓reduceIte]; rfl) ?_
    astep 255 3 (.alu .q .add (.reg .rsi) .rax)
    astep 258 3 (.alu .q .sub (.reg .rdx) .rax)
    have hrdxv : (BitVec.ofNat 64 (40 - k)).toNat = 40 - k := by simp; omega
    by_cases hj : ds.length = 40 - k
    · have h0 : BitVec.ofNat 64 (40 - k) - lenWord ds = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, hlen, hrdxv]
        simp; omega
      have hzs : @Silmaril.X86.Ext.isZeroN Silmaril.X86.Ext.Sz.q.bits
          (BitVec.ofNat 64 (40 - k) - lenWord ds) = true := by
        show (BitVec.ofNat 64 (40 - k) - lenWord ds == 0#64) = true
        rw [h0]; rfl
      refine Silmaril.Containers.Lps.oexecN_instr _ _ (off := 261) (len := 2) (instruction := .jcc8 .ne 0xdd#8)
        hh hl (by simp [hrip, hb, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write])
        (by oprobe_side) (by oprobe_side) (by oprobe_side) (by oprobe_side)
        (by simp (config := {decide := true}) only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval,
              Probe.resume, Probe.complete, Silmaril.X86.State.read, Silmaril.X86.State.write,
              Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.write, hrdx', setW_q,
              sub_qq, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN, hzs, Silmaril.X86.Ext.kNot,
              Option.map_some, Bool.not_true, ↓reduceIte]
            rfl) ?_
      refine hdone _ _ ds hds (by omega) ?_ ?_ ?_ ?_ ?_
      · simp [hrip, Probe.resume, Probe.complete, Silmaril.X86.State.write]
      · simp (config := {decide := true}) [Probe.resume, Probe.complete, Silmaril.X86.State.read,
          Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
          Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, hr12']
      all_goals
        simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
          Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
          Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, ↓reduceIte]
        smallfin
    · have hzs : @Silmaril.X86.Ext.isZeroN Silmaril.X86.Ext.Sz.q.bits
          (BitVec.ofNat 64 (40 - k) - lenWord ds) = false := by
        show (BitVec.ofNat 64 (40 - k) - lenWord ds == 0#64) = false
        rw [beq_eq_false_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_sub, hlen, hrdxv] at this
        simp at this; omega
      refine Silmaril.Containers.Lps.oexecN_instr _ _ (off := 261) (len := 2) (instruction := .jcc8 .ne 0xdd#8)
        hh hl (by simp [hrip, hb, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write])
        (by oprobe_side) (by oprobe_side) (by oprobe_side) (by oprobe_side)
        (by simp (config := {decide := true}) only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval,
              Probe.resume, Probe.complete, Silmaril.X86.State.read, Silmaril.X86.State.write,
              Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.write, hrdx', setW_q,
              sub_qq, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN, hzs, Silmaril.X86.Ext.kNot,
              Option.map_some, Bool.not_false, ↓reduceIte]
            rfl) ?_
      refine hnext _ _ ds hds (by omega) ?_ ?_ ?_ ?_
      · simp [hrip, Probe.resume, Probe.complete, Silmaril.X86.State.write]
      · simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
          Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
          Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, hrsi', setW_q, add_qq,
          ↓reduceIte]
        show BitVec.setWidth 64 (BitVec.ofNat 64 (4194304 + 345 + k) + lenWord ds) = _
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hlen, BitVec.toNat_ofNat]
        omega
      · simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
          Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
          Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, hrdx', setW_q, sub_qq,
          ↓reduceIte]
        show BitVec.setWidth 64 (BitVec.ofNat 64 (40 - k) - lenWord ds) = _
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, hlen, BitVec.toNat_ofNat]
        omega
      · simp (config := {decide := true}) [Probe.resume, Probe.complete, Silmaril.X86.State.read,
          Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
          Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, hr12']
  all_goals aside

theorem errLits2 : errnoRet ECONNRESET = 18446744073709551512#64 ∧
    errnoRet ETIMEDOUT = 18446744073709551506#64 := by decide

/-- **The send loop on a connection with a pending reset or timeout**: the send returns the error,
and the program exits 14. -/
theorem iter_err (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)] (o : Oracle)
    {peer : PeerAddr} {rx : NetStream} {e : Int} (hs : sendState (.connected peer 3 rx) = .err e peer 3)
    (he : e = ECONNRESET ∨ e = ETIMEDOUT)
    (k : Nat) (hk : k < 40) (counter : Nat) (core : Silmaril.X86.State) (m : Model)
    (hrip : core.rip = 4194532#64) (hrsi : core.read .rsi = BitVec.ofNat 64 (4194304 + 345 + k))
    (hrdx : core.read .rdx = BitVec.ofNat 64 (40 - k)) (hr12 : core.read .r12 = 4)
    (hh : m.halted = none) (hl : m.vmLazy = [])
    (hfd : fdLookup m.fds 4 = some (.socket (.connected peer 3 rx)))
    (Q : Omni.Post (isaOf o))
    (hfail : ∀ (c : Silmaril.Process.LPS.Config (isaOf o)) (fs : Fs.FileSystem),
      c.model.halted = some 14 → c.model.killedBy = none → Q [.exitEv 14 fs] (.halt c)) :
    ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
      ((probe.launchAt en inp).ocfg o core none counter m) Q := by
  have hb : (probe.launchAt en inp).base = 4194304 := rfl
  have hb' : probe.base = 4194304 := rfl
  have hrsi' := hrsi
  have hrdx' := hrdx
  have hr12' := hr12
  simp only [Silmaril.X86.State.read] at hrsi' hrdx' hr12'
  astep 228 5 (.movI32 .rax 0x2c#32)
  astep 233 3 (.mov .q (.reg .rdi) .r12)
  astep 236 6 (.movI32 .r10 0x4000#32)
  astep 242 3 (.alu .d .xor (.reg .r8) .r8)
  astep 245 3 (.alu .d .xor (.reg .r9) .r9)
  apply Silmaril.Containers.Lps.oexecN_trap _ _ (off := 248)
  all_goals aside
  case rip => simp [hrip, hb']
  apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := fun _ : Unit => True)
  case outcomes =>
    refine send_errP en inp _ _ m k hk ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfd hs
    all_goals hseval
    case refine_6 =>
      show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .r8) ^^^ BitVec.setWidth 32 (core.regs .r8)) = 0#64
      simp
    case refine_7 =>
      show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .r9) ^^^ BitVec.setWidth 32 (core.regs .r9)) = 0#64
      simp
  case live => intro _ _; exact hh
  case lazy => intro _ _; exact hl
  case inhabited => exact ⟨(), trivial⟩
  case rest =>
    intro _ _
    rcases he with rfl | rfl <;>
    · simp only [errLits2]
      astep 250 3 (.test .q (.reg .rax) .rax)
      refine Silmaril.Containers.Lps.oexecN_instr _ _ (off := 253) (len := 2) (instruction := .jcc8 .le 0x3e#8)
        hh hl (by simp [hrip, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write])
        (by oprobe_side) (by oprobe_side) (by oprobe_side) (by oprobe_side)
        (by simp (config := {decide := true}) only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Cond.eval,
              Probe.resume, Probe.complete, Silmaril.X86.State.read, Silmaril.X86.State.write,
              Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.logicFlagsN,
              setW_q, and_self_q, and_self_qq, BitVec.msb_eq_decide, Silmaril.X86.Ext.isZeroN,
              Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.kXor, ↓reduceIte]
            rfl) ?_
      refine Silmaril.Containers.Lps.oexecN_instr _ _ (off := 317) (len := 5) (instruction := .movI32 .rdi 0xe#32)
        hh hl (by simp [hrip, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write])
        (by oprobe_side) (by oprobe_side) (by oprobe_side) (by oprobe_side) (by rfl) ?_
      refine Silmaril.Containers.Lps.oexecN_instr _ _ (off := 322) (len := 5) (instruction := .movI32 .rax 0x3c#32)
        hh hl (by simp [hrip, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write])
        (by oprobe_side) (by oprobe_side) (by oprobe_side) (by oprobe_side) (by rfl) ?_
      refine Silmaril.Containers.Lps.oexecN_trap _ _ (off := 327) hh hl
        (by simp [hrip, hb', Probe.resume, Probe.complete, Silmaril.X86.State.write])
        (by oprobe_side) (by oprobe_side) ?_
      refine Silmaril.Containers.Lps.oexecN_exit _ _ (status := 14) (by hseval) hh (exit_out _ _ _) ?_ ?_
      · apply clear_small _ _ 60 _ (by decide +kernel)
        · exact small32 _
        · simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
            Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
            Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, hrsi', ↓reduceIte,
            uns, BitVec.toNat_ofNat, taskSizeMaxX86]
          omega
        · simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
            Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
            Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, hrdx', ↓reduceIte,
            uns, BitVec.toNat_ofNat, taskSizeMaxX86]
          omega
        all_goals
          simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
            Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
            Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, ↓reduceIte]
          smallfin
      · exact hfail _ _ (by simp [Silmaril.Process.LPS.Model.withHalted, Silmaril.Process.LPS.Model.halted])
          (by simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.withHalted,
            Silmaril.Process.LPS.Model.halted])
  all_goals aside


theorem mapEv_write3 (b : Byte) : mapEv (.writeEv 3 b) = some [.send (connSock 3) [UInt8.ofBitVec b]] := by
  simp (config := {decide := true}) [mapEv]

theorem mapEvs_writes3 : ∀ ds : List Byte,
    mapEvs (ds.map (.writeEv 3)) = some (ds.map fun b => .send (connSock 3) [UInt8.ofBitVec b])
  | [] => rfl
  | d :: ds => by
    have ih := mapEvs_writes3 ds
    unfold mapEvs at ih ⊢
    rw [List.map_cons, List.mapM_cons, mapEv_write3]
    cases h : List.mapM mapEv (List.map (Event.writeEv 3) ds) with
    | none => rw [h] at ih; cases ih
    | some l =>
      rw [h] at ih
      simp only [Option.map_some, Option.some.injEq] at ih
      simp [ih]

theorem sendState_cases (peer : PeerAddr) (rx : NetStream) :
    sendState (.connected peer 3 rx) = .goes 3 ∨
      ∃ e, (e = ECONNRESET ∨ e = ETIMEDOUT) ∧ sendState (.connected peer 3 rx) = .err e peer 3 := by
  unfold sendState
  cases h : rx.item 0 with
  | inl _ => simp [h]
  | inr e => cases e <;> simp [h]

theorem take_succ_drop {α : Type} (l : List α) (k j : Nat) :
    l.take k ++ (l.drop k).take j = l.take (k + j) := by
  rw [List.take_add]

theorem mapEvs_writes3_app (ds : List Byte) (tr : List Event) (u : List Ev) (h : mapEvs tr = some u) :
    mapEvs (ds.map (.writeEv 3) ++ tr) =
      some ((ds.map fun b => .send (connSock 3) [UInt8.ofBitVec b]) ++ u) := by
  induction ds with
  | nil => simpa using h
  | cons d ds ih =>
    unfold mapEvs at ih ⊢
    rw [List.map_cons, List.cons_append, List.mapM_cons, mapEv_write3]
    cases h2 : List.mapM mapEv (List.map (Event.writeEv 3) ds ++ tr) with
    | none => rw [h2] at ih; cases ih
    | some l =>
      rw [h2] at ih
      simp only [Option.map_some, Option.some.injEq] at ih
      simp [ih]

theorem sendEvs_okBytes (k : Nat) :
    (okBytes.take k).map (fun b => Ev.send (connSock 3) [UInt8.ofBitVec b]) =
      sendEvs (connSock 3) (Fixtures.okResponse.take k) := by
  rw [← okBytes_eq]
  simp only [sendEvs, ← List.map_take, List.map_map, Function.comp_def]

theorem qk_fail {o : Oracle} {k : Nat} {c : Silmaril.Process.LPS.Config (isaOf o)} {fs : Fs.FileSystem}
    (hh : c.model.halted = some 14) (hkill : c.model.killedBy = none) :
    Qk o k [.exitEv 14 fs] (.halt c) := by
  refine ⟨_, mapEvs_writes3_app _ _ [] rfl, c, rfl, hkill, 14, hh, ?_⟩
  refine .inr ⟨by decide, 3, Fixtures.okResponse.take k, List.take_prefix _ _, ?_⟩
  simp only [List.nil_append, List.append_nil]
  exact sendEvs_okBytes k

theorem qk_step {o : Oracle} {k : Nat} {ds : List Byte} (hds : SendOk k ds) (tr : List Event)
    (out : Omni.Outcome (isaOf o)) (h : Qk o (k + ds.length) tr out) :
    Qk o k (ds.map (.writeEv 3) ++ tr) out := by
  unfold Qk at *
  rw [← List.append_assoc, ← List.map_append]
  have e : okBytes.take k ++ ds = okBytes.take (k + ds.length) := by
    conv_lhs => rw [hds.2.2]
    exact take_succ_drop _ _ _
  rw [e]
  exact h

/-- **The send loop**, from the loop head with `k` octets sent, given the drain. -/
theorem loop (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)] (o : Oracle)
    {peer : PeerAddr} {rx : NetStream} (m : Model) (hh : m.halted = none) (hl : m.vmLazy = [])
    (hfd : fdLookup m.fds 4 = some (.socket (.connected peer 3 rx)))
    (hdrain : ∀ (c : Silmaril.X86.State) (cnt : Nat), c.rip = 4194567#64 → c.read .r12 = 4 →
      uns (c.read .r10) < taskSizeMaxX86 → uns (c.read .r8) < taskSizeMaxX86 →
      uns (c.read .r9) < taskSizeMaxX86 →
      ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
        ((probe.launchAt en inp).ocfg o c none cnt m) (Qk o 40)) :
    ∀ r k, 40 - k = r → k < 40 → ∀ (core : Silmaril.X86.State) (cnt : Nat), core.rip = 4194532#64 →
      core.read .rsi = BitVec.ofNat 64 (4194304 + 345 + k) → core.read .rdx = BitVec.ofNat 64 (40 - k) →
      core.read .r12 = 4 →
      ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
        ((probe.launchAt en inp).ocfg o core none cnt m) (Qk o k) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro k hr hk core cnt hrip hrsi hrdx hr12
    rcases sendState_cases peer rx with hs | ⟨e, he, hs⟩
    · refine iter_goes en inp o hs k hk cnt core m hrip hrsi hrdx hr12 hh hl hfd (Qk o k) ?_ ?_
      · intro c' cnt' ds hds hlt h1 h2 h3 h4
        exact execN_conseq (ih (40 - (k + ds.length)) (by have := hds.1; omega) (k + ds.length) rfl hlt
          c' cnt' h1 h2 h3 h4) (qk_step hds)
      · intro c' cnt' ds hds heq h1 h2 h3 h4 h5
        exact execN_conseq (hdrain c' cnt' h1 h2 h3 h4 h5) fun tr out h => qk_step hds tr out (heq ▸ h)
    · exact iter_err en inp o hs he k hk cnt core m hrip hrsi hrdx hr12 hh hl hfd (Qk o k)
        fun c fs h1 h2 => qk_fail h1 h2

/-- **The loop obligation from the drain obligation.** -/
theorem serverLoop_of_drain (hd : Task.serverDrain) : Task.serverLoop := by
  intro en inp hc o counter core m hs
  obtain ⟨hrip, hrsi, hrdx, hr12, hh, hl, peer, rx, hfd⟩ := hs
  have hrip' : core.rip = 4194532#64 := BitVec.eq_of_toNat_eq (by rw [hrip]; rfl)
  have h := loop en inp o m hh hl hfd (fun c cnt h1 h2 h3 h4 h5 => hd en inp hc o cnt c m peer rx h1 h2 h3 h4 h5 hh hl hfd)
    40 0 rfl (by decide) core counter hrip' (by rw [hrsi]; rfl) (by rw [hrdx]; rfl) hr12
  exact execN_conseq h fun tr out q => by simpa [Qk] using q

end Silmaril.Proofs.Containers.HttpServe.Loop
