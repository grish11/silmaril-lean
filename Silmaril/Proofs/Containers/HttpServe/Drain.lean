module

public import Silmaril.Containers.HttpServe.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Ports.Thms
public import Silmaril.Process.LPS.Probes.KitMemory
public import Silmaril.Proofs.Containers.HttpServe.Loop

/-!
# Proofs: the drain and the exit

Proofs for `Silmaril.Containers.HttpServe.Thms`. From the drain's entry (segment offset 263) with
all 40 octets sent: `read(4, buf, 1024)` into the image's buffer (offset 385, after the code and
the response), for every state of the connection's stream: a `FIN` (0), a pending reset or
timeout (that error, the socket reset), or data (a non-empty prefix of at most 1024 octets,
written to the buffer). Then `exit(0)`. After a read that wrote the buffer the remaining
instructions are fetched from the written memory (`Probe.written_fetch`: every code window before
the buffer is unchanged) with the flag-oracle rules over a changed memory (`Lps.oexecN_instrW`,
`oexecN_trapW`, `oexecN_haltW`). Every exit is a successful session: exactly the response sent,
then the drained octets.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Containers.HttpServe.Drain

open Silmaril.Containers Silmaril.Containers.Lps Silmaril.Containers.HttpServe
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes
open Silmaril.Proofs.Containers.HttpServe.Walk Silmaril.Proofs.Containers.HttpServe.Loop

set_option hygiene false in
macro "regfin" : tactic => `(tactic| first | exact h10 | exact h8 | exact h9 | exact small32 _ | decide)

theorem xor_dd (y : BitVec 64) :
    BitVec.setWidth 64 (@HXor.hXor (BitVec Silmaril.X86.Ext.Sz.d.bits) (BitVec Silmaril.X86.Ext.Sz.d.bits)
      (BitVec Silmaril.X86.Ext.Sz.d.bits)
      (@instHXorOfXorOp (BitVec Silmaril.X86.Ext.Sz.d.bits) (@BitVec.instXorOp Silmaril.X86.Ext.Sz.d.bits))
      (BitVec.setWidth Silmaril.X86.Ext.Sz.d.bits y) (BitVec.setWidth Silmaril.X86.Ext.Sz.d.bits y)) = 0#64 := by
  show BitVec.setWidth 64 (BitVec.setWidth 32 y ^^^ BitVec.setWidth 32 y) = 0#64
  simp

theorem read_args (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)]
    (core : Silmaril.X86.State) (n : Word) (m : Model) (hn : n = 0) (hrdi : core.read .rdi = 4)
    (hrsi : core.read .rsi = 4194689#64) (hrdx : core.read .rdx = 1024)
    (h10 : uns (core.read .r10) < taskSizeMaxX86) (h8 : uns (core.read .r8) < taskSizeMaxX86)
    (h9 : uns (core.read .r9) < taskSizeMaxX86) (o : Outcome SyscallEffect) :
    Ports.publish [8080] ((probe.launchAt en inp).sysIn core n) m o ↔
      readSpecX86 4 4194689#64 1024 ((probe.launchAt en inp).sysIn core n) m o := by
  obtain ⟨a, b0, b1, b2, -⟩ := sysIn_args (probe.launchAt en inp) core n
  subst hn
  have hclear := clear_small (probe.launchAt en inp) core 0 0 (by decide +kernel)
    (by rw [hrdi]; decide) (by rw [hrsi]; decide) (by rw [hrdx]; decide) h10 h8 h9
  rw [Ports.publish_of_not (publishedBind_ne (by rw [a]; decide)),
    Ports.dispatches_read.spec_iff (by rw [a]; rfl) hclear, b0, b1, b2, hrdi, hrsi, hrdx]
  rfl

/-- **The exit after the drain**, over the initial memory. -/
theorem tail0 (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)] (o : Oracle)
    (counter : Nat) (core : Silmaril.X86.State) (m : Model)
    (hrip : core.rip = 4194584#64) (hrsi : core.read .rsi = 4194689#64) (hrdx : core.read .rdx = 1024)
    (h10 : uns (core.read .r10) < taskSizeMaxX86) (h8 : uns (core.read .r8) < taskSizeMaxX86)
    (h9 : uns (core.read .r9) < taskSizeMaxX86) (hh : m.halted = none) (hl : m.vmLazy = [])
    (Q : Omni.Post (isaOf o))
    (hpost : ∀ (c : Silmaril.Process.LPS.Config (isaOf o)) (fs : Fs.FileSystem),
      c.model.halted = some 0 → c.model.killedBy = none → Q [.exitEv 0 fs] (.halt c)) :
    ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
      ((probe.launchAt en inp).ocfg o core none counter m) Q := by
  have hb : (probe.launchAt en inp).base = 4194304 := rfl
  have hb' : probe.base = 4194304 := rfl
  have hrsi' := hrsi
  have hrdx' := hrdx
  have hr12' : True := trivial
  simp only [Silmaril.X86.State.read] at hrsi' hrdx' h10 h8 h9
  astep 280 5 (.movI32 .rax 0x3c#32)
  astep 285 2 (.alu .d .xor (.reg .rdi) .rdi)
  apply Silmaril.Containers.Lps.oexecN_trap _ _ (off := 287)
  all_goals aside
  case rip => simp [hrip, hb']
  refine Silmaril.Containers.Lps.oexecN_exit _ _ (status := 0) ?_ hh (exit_out _ _ _) ?_ ?_
  · simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
      Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
      Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, ↓reduceIte,
      Silmaril.X86.Ext.AluOp.resultN, Probe.complete_read]
    exact xor_dd _
  · apply clear_small _ _ 60 _ (by decide +kernel)
    all_goals
      simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
        Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
        Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, ↓reduceIte,
        Silmaril.X86.Ext.AluOp.resultN, Probe.complete_read, hrsi', hrdx']
    · exact small32 _
    · exact h10
    · exact h8
    · exact h9
  · exact hpost _ _ (by simp [Silmaril.Process.LPS.Model.withHalted, Silmaril.Process.LPS.Model.halted])
      (by simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.withHalted,
        Silmaril.Process.LPS.Model.halted])

theorem clear_oW {o : Oracle} (P : Probe) (core : Silmaril.X86.State) (mem : Silmaril.Process.Memory)
    (cnt : Nat) (h0 : uns (core.read .rdi) < taskSizeMaxX86) (h1 : uns (core.read .rsi) < taskSizeMaxX86)
    (h2 : uns (core.read .rdx) < taskSizeMaxX86) (h3 : uns (core.read .r10) < taskSizeMaxX86)
    (h4 : uns (core.read .r8) < taskSizeMaxX86) (h5 : uns (core.read .r9) < taskSizeMaxX86) :
    NativeX86.All.boundarySuspect 60 (sysInput (isaOf o) P.segs
      (⟨⟨⟨core, mem⟩, some 60⟩, cnt⟩ : X86FlagChoices.State) 60) = false := by
  have e : NativeX86.All.boundarySuspect 60 (sysInput (isaOf o) P.segs
      (⟨⟨⟨core, mem⟩, some 60⟩, cnt⟩ : X86FlagChoices.State) 60) =
      [Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].any
        (fun r => NativeX86.All.inGuardWindow (core.read r)) := by
    unfold NativeX86.All.boundarySuspect
    rw [show NativeX86.All.constPtrArgs 60 = [] by decide +kernel, List.any_nil, Bool.or_false]
    rfl
  rw [e]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff]
  exact ⟨Probe.inGuardWindow_of_lt h0, Probe.inGuardWindow_of_lt h1, Probe.inGuardWindow_of_lt h2,
    Probe.inGuardWindow_of_lt h3, Probe.inGuardWindow_of_lt h4, Probe.inGuardWindow_of_lt h5⟩

theorem arg0_oW {o : Oracle} (P : Probe) (core : Silmaril.X86.State) (mem : Silmaril.Process.Memory)
    (cnt : Nat) (n : Word) :
    (sysInput (isaOf o) P.segs (⟨⟨⟨core, mem⟩, some n⟩, cnt⟩ : X86FlagChoices.State) n).arg 0 =
      core.read .rdi := rfl

/-- **The exit after the drain**, over the memory the drain wrote (the buffer, after the code). -/
theorem tailW (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)] (o : Oracle)
    (counter : Nat) (core : Silmaril.X86.State) (m : Model) (bs : List Byte) (hbs : bs.length ≤ 1024)
    (hrip : core.rip = 4194584#64) (hrsi : core.read .rsi = 4194689#64) (hrdx : core.read .rdx = 1024)
    (h10 : uns (core.read .r10) < taskSizeMaxX86) (h8 : uns (core.read .r8) < taskSizeMaxX86)
    (h9 : uns (core.read .r9) < taskSizeMaxX86) (hh : m.halted = none) (hl : m.vmLazy = [])
    (Q : Omni.Post (isaOf o))
    (hpost : ∀ (c : Silmaril.Process.LPS.Config (isaOf o)) (fs : Fs.FileSystem),
      c.model.halted = some 0 → c.model.killedBy = none → Q [.exitEv 0 fs] (.halt c)) :
    ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
      (ocfgM o core ((probe.launchAt en inp).written 385 bs) none counter m) Q := by
  have hb : (probe.launchAt en inp).base = 4194304 := rfl
  have hb' : probe.base = 4194304 := rfl
  have hsz : (probe.launchAt en inp).size = 1409 := rfl
  have hsmall : 385 + bs.length ≤ (probe.launchAt en inp).size := by rw [hsz]; omega
  have hrsi' := hrsi
  have hrdx' := hrdx
  simp only [Silmaril.X86.State.read] at hrsi' hrdx' h10 h8 h9
  refine Silmaril.Containers.Lps.oexecN_instrW _ _ (off := 280) (len := 5) (instruction := .movI32 .rax 0x3c#32)
    hh hl (by simp [hrip, hb']) (by oprobe_side)
    (Probe.written_fetch hsmall (by rw [hsz]; omega) (by omega))
    (Probe.written_fetch hsmall (by rw [hsz]; omega) (by omega)) (by oprobe_side) (by rfl) ?_
  refine Silmaril.Containers.Lps.oexecN_instrW _ _ (off := 285) (len := 2)
    (instruction := .alu .d .xor (.reg .rdi) .rdi)
    hh hl (by simp [hrip, hb']) (by oprobe_side)
    (Probe.written_fetch hsmall (by rw [hsz]; omega) (by omega))
    (Probe.written_fetch hsmall (by rw [hsz]; omega) (by omega)) (by oprobe_side) (by rfl) ?_
  refine Silmaril.Containers.Lps.oexecN_trapW _ _ (off := 287) hh hl (by simp [hrip, hb'])
    (Probe.written_fetch hsmall (by rw [hsz]; omega) (by omega)) (by oprobe_side) ?_
  refine Silmaril.Containers.Lps.oexecN_haltW _ _ (n := 60) (model' := m.withHalted 0) (code := 0)
    (effect := mkEffect 0 [] []) (by decide) hh ?_
    (by simp [Silmaril.Process.LPS.Model.withHalted, Silmaril.Process.LPS.Model.halted])
    (by simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.withHalted,
      Silmaril.Process.LPS.Model.halted])
    (hpost _ _ (by simp [Silmaril.Process.LPS.Model.withHalted, Silmaril.Process.LPS.Model.halted])
      (by simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.withHalted,
        Silmaril.Process.LPS.Model.halted]))
  intro out
  rw [Ports.publish_of_not (publishedBind_ne (by show (60 : Word).toNat ≠ 49; decide))]
  rw [Probe.native_exit_iff _ _ _ rfl (clear_oW _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_), arg0_oW]
  rotate_left
  all_goals
    simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
      Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
      Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, ↓reduceIte,
      Silmaril.X86.Ext.AluOp.resultN, Probe.complete_read, hrsi', hrdx']
  · exact small32 _
  · exact h10
  · exact h8
  · exact h9
  · rw [xor_dd]; rfl

theorem mapEv_read3 (b : Byte) : mapEv (.readEv 3 b) = some [.recv (connSock 3) [UInt8.ofBitVec b]] := by
  simp (config := {decide := true}) [mapEv]

theorem mapEvs_reads3_exit (fs : Fs.FileSystem) : ∀ bs : List Byte,
    mapEvs (bs.map (.readEv 3) ++ [.exitEv 0 fs]) =
      some (bs.map fun b => .recv (connSock 3) [UInt8.ofBitVec b])
  | [] => rfl
  | d :: ds => by
    have ih := mapEvs_reads3_exit fs ds
    unfold mapEvs at ih ⊢
    rw [List.map_cons, List.cons_append, List.mapM_cons, mapEv_read3]
    cases h : List.mapM mapEv (List.map (Event.readEv 3) ds ++ [Event.exitEv 0 fs]) with
    | none => rw [h] at ih; cases ih
    | some l =>
      rw [h] at ih
      simp only [Option.map_some, Option.some.injEq] at ih
      simp [ih]

/-- **A successful session**: all 40 octets sent, then any request octets drained, exit 0. -/
theorem qk_session {o : Oracle} {c : Silmaril.Process.LPS.Config (isaOf o)} {fs : Fs.FileSystem}
    (bs : List Byte) (hh : c.model.halted = some 0) (hkill : c.model.killedBy = none) :
    Qk o 40 (bs.map (.readEv 3) ++ [.exitEv 0 fs]) (.halt c) := by
  refine ⟨_, mapEvs_writes3_app _ _ _ (mapEvs_reads3_exit fs bs), c, rfl, hkill, 0, hh, ?_⟩
  refine .inl ⟨rfl, 3, bs.map UInt8.ofBitVec, ?_⟩
  rw [List.nil_append, sendEvs_okBytes 40, List.take_of_length_le (by decide)]
  simp [recvEvs, List.map_map, Function.comp_def]

set_option hygiene false in
macro "rsimp" : tactic => `(tactic|
  simp (config := {decide := true}) only [Probe.resume, Probe.complete, Silmaril.X86.State.read,
    Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.Sz.write,
    Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Rex.ofByte, Silmaril.X86.Ext.mkReg, ↓reduceIte,
    Silmaril.X86.Ext.AluOp.resultN, Probe.complete_read, hr12'])

set_option hygiene false in
macro "rfin " t:tactic : tactic => `(tactic| first | ($t:tactic) | (rsimp; $t:tactic) | rsimp)

theorem drain (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)] (o : Oracle)
    (counter : Nat) (core : Silmaril.X86.State) (m : Model) (peer : PeerAddr) (rx : NetStream)
    (hrip : core.rip = 4194567#64) (hr12 : core.read .r12 = 4)
    (h10 : uns (core.read .r10) < taskSizeMaxX86) (h8 : uns (core.read .r8) < taskSizeMaxX86)
    (h9 : uns (core.read .r9) < taskSizeMaxX86) (hh : m.halted = none) (hl : m.vmLazy = [])
    (hfd : fdLookup m.fds 4 = some (.socket (.connected peer 3 rx))) :
    ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
      ((probe.launchAt en inp).ocfg o core none counter m) (Qk o 40) := by
  have hb : (probe.launchAt en inp).base = 4194304 := rfl
  have hb' : probe.base = 4194304 := rfl
  have hr12' := hr12
  simp only [Silmaril.X86.State.read] at hr12' h10 h8 h9
  astep 263 2 (.alu .d .xor (.reg .rax) .rax)
  astep 265 3 (.mov .q (.reg .rdi) .r12)
  astep 268 5 (.movI32 .rsi 0x400181#32)
  astep 273 5 (.movI32 .rdx 0x400#32)
  apply Silmaril.Containers.Lps.oexecN_trap _ _ (off := 278)
  all_goals aside
  case rip => simp [hrip, hb']
  cases hi : rx.item 0 with
  | inr e =>
    cases e with
    | fin =>
      apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := fun _ : Unit => True) (ret := fun _ => 0)
        (copyins := fun _ => []) (model' := fun _ => m) (events := fun _ => [])
      case outcomes =>
        intro out
        refine (read_args en inp _ _ m ?_ ?_ ?_ ?_ ?_ ?_ ?_ out).trans ?_
        rotate_right
        · rw [Ports.read_fin_iff _ _ _ m out hfd hi (by decide)]
          exact ⟨fun h => ⟨(), trivial, h⟩, fun ⟨_, _, h⟩ => h⟩
        · rfin (exact xor_dd _)
        · rsimp
        · rsimp
        · rsimp
        · rfin (exact h10)
        · rfin (exact h8)
        · rfin (exact h9)
      case live => intro _ _; exact hh
      case lazy => intro _ _; exact hl
      case inhabited => exact ⟨(), trivial⟩
      case rest =>
        intro _ _
        refine tail0 en inp o _ _ m ?_ ?_ ?_ ?_ ?_ ?_ hh hl _ ?_
        · simp [hrip, Probe.resume, Probe.complete, Silmaril.X86.State.write]
        · rsimp
        · rsimp
        · rfin (exact h10)
        · rfin (exact h8)
        · rfin (exact h9)
        · intro c fs h1 h2
          simpa using qk_session (fs := fs) [] h1 h2
      case other =>
        show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax)) ≠ 158
        simp
      case notClone =>
        show cloneNumber (BitVec.setWidth 64
          (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax))) = false
        simp [cloneNumber]
      case running => exact hh
    | rst =>
      apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := fun _ : Unit => True)
        (ret := fun _ => errnoRet ECONNRESET) (copyins := fun _ => [])
        (model' := fun _ => m.withFds (fdInsert m.fds 4 (.socket (.reset peer 3)))) (events := fun _ => [])
      case outcomes =>
        intro out
        refine (read_args en inp _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ out).trans ?_
        rotate_right
        · rw [Ports.read_err_iff _ _ _ _ out hfd hi (Or.inl ⟨rfl, rfl⟩) (by decide)]
          exact ⟨fun h => ⟨(), trivial, h⟩, fun ⟨_, _, h⟩ => h⟩
        · rfin (exact xor_dd _)
        · rsimp
        · rsimp
        · rsimp
        · rfin (exact h10)
        · rfin (exact h8)
        · rfin (exact h9)
      case live => intro _ _; exact hh
      case lazy => intro _ _; exact hl
      case inhabited => exact ⟨(), trivial⟩
      case rest =>
        intro _ _
        refine tail0 en inp o _ _ (m.withFds (fdInsert m.fds 4 (.socket (.reset peer 3)))) ?_ ?_ ?_ ?_ ?_ ?_ hh hl _ ?_
        · simp [hrip, Probe.resume, Silmaril.X86.State.write]
        · rsimp
        · rsimp
        · rfin (exact h10)
        · rfin (exact h8)
        · rfin (exact h9)
        · intro c fs h1 h2
          simpa using qk_session (fs := fs) [] h1 h2
      case other =>
        show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax)) ≠ 158
        simp
      case notClone =>
        show cloneNumber (BitVec.setWidth 64
          (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax))) = false
        simp [cloneNumber]
      case running => exact hh
    | timedOut =>
      apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := fun _ : Unit => True)
        (ret := fun _ => errnoRet ETIMEDOUT) (copyins := fun _ => [])
        (model' := fun _ => m.withFds (fdInsert m.fds 4 (.socket (.reset peer 3)))) (events := fun _ => [])
      case outcomes =>
        intro out
        refine (read_args en inp _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ out).trans ?_
        rotate_right
        · rw [Ports.read_err_iff _ _ _ _ out hfd hi (Or.inr ⟨rfl, rfl⟩) (by decide)]
          exact ⟨fun h => ⟨(), trivial, h⟩, fun ⟨_, _, h⟩ => h⟩
        · rfin (exact xor_dd _)
        · rsimp
        · rsimp
        · rsimp
        · rfin (exact h10)
        · rfin (exact h8)
        · rfin (exact h9)
      case live => intro _ _; exact hh
      case lazy => intro _ _; exact hl
      case inhabited => exact ⟨(), trivial⟩
      case rest =>
        intro _ _
        refine tail0 en inp o _ _ (m.withFds (fdInsert m.fds 4 (.socket (.reset peer 3)))) ?_ ?_ ?_ ?_ ?_ ?_ hh hl _ ?_
        · simp [hrip, Probe.resume, Silmaril.X86.State.write]
        · rsimp
        · rsimp
        · rfin (exact h10)
        · rfin (exact h8)
        · rfin (exact h9)
        · intro c fs h1 h2
          simpa using qk_session (fs := fs) [] h1 h2
      case other =>
        show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax)) ≠ 158
        simp
      case notClone =>
        show cloneNumber (BitVec.setWidth 64
          (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax))) = false
        simp [cloneNumber]
      case running => exact hh
  | inl b =>
    apply Silmaril.Containers.Lps.oexecN_sysW _ _ (allowed := Ports.ReadOk rx) (ret := lenWord)
      (writes := fun bs => [(4194689#64, bs)]) (copyins := fun _ => [])
      (model' := fun bs => m.withFds (fdInsert m.fds 4 (.socket (.connected peer 3 (rx.take bs.length).2))))
      (events := fun bs => bs.map (.readEv 3))
      (mem' := fun bs => (probe.launchAt en inp).written 385 bs)
    case outcomes =>
      intro out
      refine (read_args en inp _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ out).trans ?_
      rotate_right
      · rw [Ports.read_data_iff _ _ _ _ out hfd hi ?_]
        · exact ⟨fun ⟨bs, h1, h2⟩ => ⟨bs, h1, h2⟩, fun ⟨bs, h1, h2⟩ => ⟨bs, h1, h2⟩⟩
        · intro k hk
          change (readBytesAux (viewByte (probe.launchAt en inp).mem0 .write)
            (BitVec.ofNat 64 ((probe.launchAt en inp).base + 385)) k).isSome = true
          exact Probe.wmem_readBytesAux rfl 385 k (by show 385 + k ≤ 1409; omega)
      · rfin (exact xor_dd _)
      · rsimp
      · rsimp
      · rsimp
      · rfin (exact h10)
      · rfin (exact h8)
      · rfin (exact h9)
    case applied => intro bs _; rfl
    case live => intro _ _; exact hh
    case lazy => intro _ _; exact hl
    case inhabited =>
      refine ⟨[b], ?_, by simp, ?_⟩
      · simp
      · simp [NetStream.take, NetStream.takeFrom, hi]
    case rest =>
      intro bs hbs
      refine tailW en inp o _ _ (m.withFds (fdInsert m.fds 4 (.socket (.connected peer 3 (rx.take bs.length).2)))) bs hbs.2.1 ?_ ?_ ?_ ?_ ?_ ?_ hh hl _ ?_
      · simp [hrip, Probe.resume, Silmaril.X86.State.write]
      · rsimp
      · rsimp
      · rfin (exact h10)
      · rfin (exact h8)
      · rfin (exact h9)
      · intro c fs h1 h2
        exact qk_session bs h1 h2
    case other =>
      show BitVec.setWidth 64 (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax)) ≠ 158
      simp
    case notClone =>
      show cloneNumber (BitVec.setWidth 64
        (BitVec.setWidth 32 (core.regs .rax) ^^^ BitVec.setWidth 32 (core.regs .rax))) = false
      simp [cloneNumber]
    case running => exact hh


/-- **The drain obligation holds.** -/
theorem serverDrain : Task.serverDrain := by
  intro en inp hc o counter core m peer rx h1 h2 h3 h4 h5 hh hl hfd
  exact drain en inp o counter core m peer rx h1 h2 h3 h4 h5 hh hl hfd

end Silmaril.Proofs.Containers.HttpServe.Drain
