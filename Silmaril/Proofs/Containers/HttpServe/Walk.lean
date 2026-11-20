module

public import Silmaril.Containers.HttpServe.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Ports.Thms

public import Silmaril.Process.LPS.Problems.CoreutilsLite.Spec
public import Silmaril.Proofs.Containers.HttpServe.Basic

/-!
# Proofs: the server's instructions from the launch to the send loop

Proofs for `Silmaril.Containers.HttpServe.Thms`. The walk uses the flag-oracle kit rules over the
published-port table (`Lps.oexecN_*`, which also prove clone freedom) and LPS's outcomes of
`socket`, `bind` (published), `listen` and `accept` (`Ports.Thms`, and `bind_published` here).
Every injected failure is followed to its exit (status 10, 11, 13).
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Silmaril.Proofs.Containers.HttpServe.Walk

open Silmaril.Containers Silmaril.Containers.Lps Silmaril.Containers.HttpServe
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes
open Silmaril.Process.LPS.Problems.CoreutilsLite

theorem publishedBind_ne {i : SyscallInput} (h : i.sysno.toNat ≠ 49) : Ports.publishedBind [8080] i = false := by
  simp [Ports.publishedBind, h]

/-- The choices of `socket`: `none` the new descriptor, `some e` an injected error. -/
def sockAllowed (m : Model) : Option Int → Prop
  | none => fdLookup m.fds (allocFd m.fds) = none
  | some e => e ∈ socketErrnos
def sockRet (m : Model) : Option Int → Word
  | none => allocFd m.fds
  | some e => errnoRet e
def sockModel (m : Model) : Option Int → Model
  | none => m.withFds (fdInsert m.fds (allocFd m.fds) (.socket .fresh))
  | some _ => m

theorem sock_out (i : SyscallInput) (m : Model) (hno : i.sysno.toNat = 41)
    (hclear : NativeX86.All.boundarySuspect 41 i = false)
    (h0 : i.arg 0 = 2) (h1 : i.arg 1 = 1) (h2 : i.arg 2 = 0) (o : Outcome SyscallEffect) :
    Ports.publish [8080] i m o ↔ ∃ x, sockAllowed m x ∧
      o = .ok ((mkEffect (sockRet m x) [] []).withCopyins []) (sockModel m x) [] := by
  rw [Ports.publish_of_not (publishedBind_ne (by omega)), Ports.dispatches_socket.spec_iff hno hclear]
  simp only [h0, h1, h2]
  rw [Ports.socket_iff]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨hf, rfl⟩)
    · exact ⟨some e, he, rfl⟩
    · exact ⟨none, hf, rfl⟩
  · rintro ⟨(_ | e), hx, rfl⟩
    · exact .inr ⟨hx, rfl⟩
    · exact .inl ⟨e, hx, rfl⟩

theorem sysIn_args (P : Probe) (core : Silmaril.X86.State) (n : Word) :
    (P.sysIn core n).sysno = n ∧ (P.sysIn core n).arg 0 = core.read .rdi ∧
    (P.sysIn core n).arg 1 = core.read .rsi ∧ (P.sysIn core n).arg 2 = core.read .rdx ∧
    (P.sysIn core n).arg 3 = core.read .r10 ∧ (P.sysIn core n).arg 4 = core.read .r8 ∧
    (P.sysIn core n).arg 5 = core.read .r9 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sock_outP (P : Probe) (core : Silmaril.X86.State) (n : Word) (m : Model) (hn : n = 41)
    (hclear : NativeX86.All.boundarySuspect 41 (P.sysIn core n) = false)
    (h0 : core.read .rdi = 2) (h1 : core.read .rsi = 1) (h2 : core.read .rdx = 0)
    (o : Outcome SyscallEffect) :
    Ports.publish [8080] (P.sysIn core n) m o ↔ ∃ x, sockAllowed m x ∧
      o = .ok ((mkEffect (sockRet m x) [] []).withCopyins []) (sockModel m x) [] := by
  obtain ⟨a, b, c, d, -⟩ := sysIn_args P core n
  subst hn
  exact sock_out _ m (by rw [a]; rfl) hclear (b.trans h0) (c.trans h1) (d.trans h2) o

theorem condLits : Silmaril.X86.Ext.Cond.ofCode 8#4 = .s ∧
    Silmaril.X86.Ext.Cond.ofCode 5#4 = .ne ∧ Silmaril.X86.Ext.Cond.ofCode 14#4 = .le := ⟨rfl, rfl, rfl⟩

macro "seval" : tactic =>
  `(tactic| (simp (config := {decide := true}) [Probe.complete, Probe.resume,
            Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write,
            Silmaril.X86.Reg.ofBitVec, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
            Silmaril.X86.Ext.Sz.ofW, Silmaril.X86.Ext.mkReg, Silmaril.X86.Ext.ModRM.ofByte,
            Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.Rex.zero, Probe.core0, Probe.initial,
            X86Launch.init, initConfigWithStack, x86ExtNative, x86Ext,
            Silmaril.X86.Ext.exec, condLits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN,
            BitVec.msb_eq_decide]; try rfl))

theorem withFds_halted (m : Model) (f : List (Word × FdEntry)) : (m.withFds f).halted = m.halted := rfl
theorem withFds_vmLazy (m : Model) (f : List (Word × FdEntry)) : (m.withFds f).vmLazy = m.vmLazy := rfl
theorem withFds_fds (m : Model) (f : List (Word × FdEntry)) : (m.withFds f).fds = f := rfl
theorem withFds_connIx (m : Model) (f : List (Word × FdEntry)) : (m.withFds f).connIx = m.connIx := rfl
theorem withFds_net (m : Model) (f : List (Word × FdEntry)) : (m.withFds f).net = m.net := rfl
theorem withAccepted_halted (m : Model) (f : List (Word × FdEntry)) : (m.withAccepted f).halted = m.halted := rfl
theorem withAccepted_vmLazy (m : Model) (f : List (Word × FdEntry)) : (m.withAccepted f).vmLazy = m.vmLazy := rfl
theorem withAccepted_fds (m : Model) (f : List (Word × FdEntry)) : (m.withAccepted f).fds = f := rfl

macro "msimp" : tactic =>
  `(tactic| (simp only [withFds_halted, withFds_vmLazy, withAccepted_halted, withAccepted_vmLazy]; rfl))

macro "sside" : tactic => `(tactic| first | oprobe_side | msimp | seval)

macro "sinstr " off:term:max len:term:max : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.oexecN_instr _ _ (off := $off) (len := $len) (instruction := _) <;>
    first | oprobe_side | seval | msimp | skip))
macro "strap " off:term:max : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.oexecN_trap _ _ (off := $off) <;> first | oprobe_side | msimp | skip))

theorem exit_out (P : Probe) (core : Silmaril.X86.State) (m : Model) (o : Outcome SyscallEffect) :
    Ports.publish [8080] (P.sysIn core 60) m o ↔ Probes.spec (P.sysIn core 60) m o :=
  Ports.publish_of_not (publishedBind_ne (by rw [(sysIn_args P core 60).1]; decide)) m o

theorem readBytesAux_mem0 (P : Probe) [Probe.Checked P] (offset count : Nat)
    (fits : offset + count ≤ P.size) :
    readBytesAux (viewByte P.mem0 .read) (BitVec.ofNat 64 (P.base + offset)) count =
      some ((P.bytes.drop offset).take count) := by
  have sizes := (inferInstance : Probe.Checked P).layout.sizes
  induction count generalizing offset with
  | zero => simp [readBytesAux]
  | succ count ih =>
    have bound : offset < P.bytes.length := by omega
    simp only [readBytesAux]
    rw [P.mem0_view offset (by omega), List.getElem?_eq_getElem bound]
    simp only
    have next : BitVec.ofNat 64 (P.base + offset) + 1 = BitVec.ofNat 64 (P.base + (offset + 1)) := by
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    rw [next, ih (offset + 1) (by omega), List.drop_eq_getElem_cons bound]
    rfl

theorem bind_outP (en : ExecEntry) (inp : ProcInput) [Probe.Checked (probe.launchAt en inp)]
    (core : Silmaril.X86.State) (n : Word) (m : Model) (hn : n = 49)
    (hclear : NativeX86.All.boundarySuspect 49 ((probe.launchAt en inp).sysIn core n) = false)
    (hrdi : core.read .rdi = 3) (hrsi : core.read .rsi = BitVec.ofNat 64 ((probe.launchAt en inp).base + 329))
    (hrdx : core.read .rdx = 16) (hfd : fdLookup m.fds 3 = some (.socket .fresh))
    (o : Outcome SyscallEffect) :
    Ports.publish [8080] ((probe.launchAt en inp).sysIn core n) m o ↔ ∃ b : Bool, True ∧
      o = .ok ((mkEffect (if b then 0 else errnoRet EADDRINUSE) [] []).withCopyins
        [(BitVec.ofNat 64 ((probe.launchAt en inp).base + 329), 16)])
        (if b then m.withFds (fdInsert m.fds 3 (.socket .bound)) else m) [] := by
  obtain ⟨a, b0, b1, b2, -⟩ := sysIn_args (probe.launchAt en inp) core n
  subst hn
  have hmem : readBytesMap ((probe.launchAt en inp).sysIn core 49).mem
      (((probe.launchAt en inp).sysIn core 49).arg 1) 16 = some addrBytes := by
    rw [b1, hrsi]
    change readBytesAux (viewByte (probe.launchAt en inp).mem0 .read) _ 16 = _
    rw [readBytesAux_mem0 _ 329 16 (by simp only [Probe.launchAt_size]; decide)]
    simp only [Probe.launchAt_bytes]
    rw [Silmaril.Proofs.Containers.HttpServe.addr_in_image]
  have h := Silmaril.Proofs.Containers.HttpServe.bind_published ((probe.launchAt en inp).sysIn core 49) m o (by rw [a]; rfl) hclear
    (by rw [b2, hrdx]) (by rw [b0, hrdi]; exact hfd) hmem
  rw [h, b0, hrdi, b1, hrsi]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨false, trivial, rfl⟩
    · exact ⟨true, trivial, rfl⟩
  · rintro ⟨(_ | _), -, rfl⟩
    · exact .inl rfl
    · exact .inr rfl

theorem listen_outP (P : Probe) (core : Silmaril.X86.State) (n : Word) (m : Model) (hn : n = 50)
    (hclear : NativeX86.All.boundarySuspect 50 (P.sysIn core n) = false)
    (hrdi : core.read .rdi = 3) (hfd : fdLookup m.fds 3 = some (.socket .bound))
    (o : Outcome SyscallEffect) :
    Ports.publish [8080] (P.sysIn core n) m o ↔ ∃ _ : Unit, True ∧
      o = .ok ((mkEffect 0 [] []).withCopyins []) (m.withFds (fdInsert m.fds 3 (.socket .listening))) [] := by
  obtain ⟨a, b0, -⟩ := sysIn_args P core n
  subst hn
  rw [Ports.publish_of_not (publishedBind_ne (by rw [a]; decide)), Ports.dispatches_listen.spec_iff (by rw [a]; rfl) hclear,
    b0, hrdi, show fd32 (3 : Word) = 3 from rfl]
  rw [Ports.listen_iff _ _ _ m o hfd]
  exact ⟨fun h => ⟨(), trivial, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- The choices of `accept`: `none` the new connection, `some e` an injected error. -/
def accAllowed (m : Model) : Option Int → Prop
  | none => fdLookup m.fds (allocFd m.fds) = none
  | some e => e ∈ acceptErrnos
def accRet : Option Int → Word
  | none => 4
  | some e => errnoRet e
def accModel (m : Model) : Option Int → Model
  | none => m.withAccepted (fdInsert m.fds 4
      (.socket (.connected (nqPeer m.net) (connChannel m.connIx) (nqScript m.net))))
  | some _ => m

theorem accept_outP (P : Probe) (core : Silmaril.X86.State) (n : Word) (m : Model) (hn : n = 43)
    (hclear : NativeX86.All.boundarySuspect 43 (P.sysIn core n) = false)
    (hrdi : core.read .rdi = 3) (hrsi : core.read .rsi = 0) (hrdx : core.read .rdx = 0)
    (hfd : fdLookup m.fds 3 = some (.socket .listening)) (hex : connIxExhausted m.connIx = false)
    (h4 : allocFd m.fds = 4) (o : Outcome SyscallEffect) :
    Ports.publish [8080] (P.sysIn core n) m o ↔ ∃ x, accAllowed m x ∧
      o = .ok ((mkEffect (accRet x) [] []).withCopyins []) (accModel m x) [] := by
  obtain ⟨a, b0, b1, b2, -⟩ := sysIn_args P core n
  subst hn
  rw [Ports.publish_of_not (publishedBind_ne (by rw [a]; decide)), Ports.dispatches_accept.spec_iff (by rw [a]; rfl) hclear,
    b0, b1, b2, hrdi, hrsi, hrdx]
  rw [show fd32 (3 : Word) = 3 from rfl, Ports.accept_iff _ _ m o hfd hex]
  simp only [accRet, accModel, accAllowed, h4]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨hf, rfl⟩)
    · exact ⟨some e, he, rfl⟩
    · exact ⟨none, hf, rfl⟩
  · rintro ⟨(_ | e), hx, rfl⟩
    · exact .inr ⟨hx, rfl⟩
    · exact .inl ⟨e, hx, rfl⟩

macro "sexit " st:term:max : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.oexecN_exit _ _ (status := $st) (outcomes := exit_out _ _ _)
    <;> try oprobe_side))

theorem errLits : errnoRet ENOMEM = 18446744073709551604#64 ∧ errnoRet EMFILE = 18446744073709551592#64 ∧
    errnoRet ENFILE = 18446744073709551593#64 ∧ errnoRet EADDRINUSE = 18446744073709551518#64 ∧
    errnoRet ECONNRESET = 18446744073709551512#64 ∧ errnoRet ETIMEDOUT = 18446744073709551506#64 ∧
    errnoRet EPIPE = 18446744073709551584#64 := by decide

/-- A failure exit meets the server's specification, with nothing sent. -/
theorem post_fail {o : Oracle} {c : Silmaril.Process.LPS.Config (isaOf o)} {k : Word}
    {fs : Fs.FileSystem} (hk : (k.toNat % 256).toUInt8 ∈ failureCode)
    (hh : c.model.halted = some k) (hkill : c.model.killedBy = none) :
    EvPost serveG [] [.exitEv k fs] (.halt c) :=
  ⟨[], rfl, c, rfl, hkill, k, hh, .inr ⟨hk, 0, [], List.nil_prefix, rfl⟩⟩

theorem m0_fds (o : Oracle) (limit : Int) (en : ExecEntry) (inp : ProcInput) :
    ((probe.launchAt en inp).omodel0 o limit).fds = [(0, .channel 0), (1, .channel 1), (2, .channel 2)] :=
  rfl

theorem m0_facts (o : Oracle) (limit : Int) (en : ExecEntry) (inp : ProcInput) :
    ((probe.launchAt en inp).omodel0 o limit).halted = none ∧
    ((probe.launchAt en inp).omodel0 o limit).vmLazy = [] ∧
    ((probe.launchAt en inp).omodel0 o limit).connIx = 0 := ⟨rfl, rfl, rfl⟩

/-- **From the launch to the send loop**: every path either exits with a defined failure status
(10, 11, 13; nothing sent) or reaches the loop's entry, where `Task.serverLoop` takes over. -/
theorem walk (hloop : Task.serverLoop) (o : Oracle) (limit : Int) (en : ExecEntry) (inp : ProcInput)
    [Probe.Checked (probe.launchAt en inp)] :
    ExecN (probe.launchAt en inp).segs (Ports.publish [8080])
      ((probe.launchAt en inp).oinitial o limit) (EvPost serveG []) := by
  rw [Probe.oinitial_at]
  sinstr 120 5
  sinstr 125 5
  sinstr 130 5
  sinstr 135 2
  strap 137
  apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := sockAllowed _) (ret := sockRet _)
    (copyins := fun _ => []) (model' := sockModel _) (events := fun _ => [])
  case outcomes =>
    exact sock_outP _ _ _ _ (by oprobe_eval) (by oprobe_side) (by oprobe_eval) (by oprobe_eval) (by oprobe_eval)
  case live => rintro (_ | _) _ <;> rfl
  case lazy => rintro (_ | _) _ <;> rfl
  case inhabited => exact ⟨some ENOMEM, by simp [sockAllowed, socketErrnos]⟩
  case rest =>
    rintro (_ | e) hx
    · simp only [sockRet, sockModel, m0_fds]
      have h3 : allocFd [(0, FdEntry.channel 0), (1, FdEntry.channel 1), (2, FdEntry.channel 2)] = 3 := by decide
      rw [h3]
      sinstr 139 3
      sinstr 142 6
      sinstr 148 3
      sinstr 151 5
      sinstr 156 3
      sinstr 159 5
      sinstr 164 5
      strap 169
      apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := fun _ : Bool => True)
        (outcomes := bind_outP en inp _ _ _ (by oprobe_eval) (by oprobe_side) (by oprobe_eval)
          (by oprobe_eval) (by oprobe_eval) rfl)
      case live => rintro (_ | _) _ <;> rfl
      case lazy => rintro (_ | _) _ <;> rfl
      case inhabited => exact ⟨true, trivial⟩
      case rest =>
        rintro (_ | _) -
        · simp only [Bool.false_eq_true, ↓reduceIte, errLits]
          sinstr 171 3
          sinstr 174 2
          sinstr 296 5
          sinstr 301 2
          sinstr 322 5
          strap 327
          sexit 11
          apply post_fail
          · decide
          · rfl
          · simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.withHalted]
        · simp only [↓reduceIte]
          sinstr 171 3
          sinstr 174 2
          sinstr 176 5
          sinstr 181 3
          sinstr 184 5
          strap 189
          apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := fun _ : Unit => True)
            (outcomes := listen_outP _ _ _ _ (by oprobe_eval) (by oprobe_side) (by oprobe_eval) rfl)
          case live => intro _ _; rfl
          case lazy => intro _ _; rfl
          case inhabited => exact ⟨(), trivial⟩
          case rest =>
            intro _ _
            sinstr 191 3
            sinstr 194 2
            sinstr 196 5
            sinstr 201 3
            sinstr 204 2
            sinstr 206 2
            strap 208
            apply Silmaril.Containers.Lps.oexecN_sys _ _ (allowed := accAllowed _) (ret := accRet)
              (copyins := fun _ => []) (model' := accModel _) (events := fun _ => [])
            case outcomes =>
              exact accept_outP _ _ _ _ (by oprobe_eval) (by oprobe_side) (by oprobe_eval) (by oprobe_eval)
                (by oprobe_eval) rfl rfl (by simp only [withFds_fds]; decide)
            case live =>
              rintro (_ | _) _ <;> simp only [accModel, Silmaril.Process.LPS.Model.halted,
                Silmaril.Process.LPS.Model.withAccepted, Silmaril.Process.LPS.Model.withFds] <;>
                exact (m0_facts o limit en inp).1
            case lazy =>
              rintro (_ | _) _ <;> simp only [accModel, Silmaril.Process.LPS.Model.vmLazy,
                Silmaril.Process.LPS.Model.withAccepted, Silmaril.Process.LPS.Model.withFds] <;>
                exact (m0_facts o limit en inp).2.1
            case inhabited => exact ⟨some ENOMEM, by simp [accAllowed, acceptErrnos]⟩
            case rest =>
              rintro (_ | e) hx
              · simp only [accRet, accModel]
                sinstr 210 3
                sinstr 213 2
                sinstr 215 3
                sinstr 218 5
                sinstr 223 5
                apply hloop en inp inferInstance
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, _, _, rfl⟩
                all_goals sside
              · simp only [accAllowed, acceptErrnos, List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl | rfl <;>
                · simp only [accRet, accModel, errLits]
                  sinstr 210 3
                  sinstr 213 2
                  sinstr 310 5
                  sinstr 315 2
                  sinstr 322 5
                  strap 327
                  sexit 13
                  apply post_fail
                  · decide
                  · rfl
                  · simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.withHalted]
            all_goals sside
          all_goals sside
      all_goals sside
    · simp only [sockAllowed, socketErrnos, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;>
      · simp only [sockRet, sockModel, errLits]
        sinstr 139 3
        sinstr 142 6
        sinstr 289 5
        sinstr 294 2
        sinstr 322 5
        strap 327
        sexit 10
        apply post_fail
        · decide
        · rfl
        · simp [Silmaril.Process.LPS.Model.killedBy, Silmaril.Process.LPS.Model.withHalted]
  all_goals sside

instance checkedProbe : Probe.Checked probe :=
  ⟨Silmaril.Proofs.Containers.HttpServe.probeLayout, harnessInput_valid,
    probe.snapshot_valid Silmaril.Proofs.Containers.HttpServe.probeLayout,
    by unfold ValidBrk; decide +kernel⟩

/-- **The launch-to-loop reduction**: the remaining loop obligation gives the program obligation. -/
theorem serverSound_of_loop (hloop : Task.serverLoop) : Task.serverSound where
  exec o limit en inp ha := by
    have := probe.checkedAt Silmaril.Proofs.Containers.HttpServe.probeLayout.static ha.1 ha.2
    exact (walk hloop o limit en inp).1
  noClone o limit en inp ha := by
    have := probe.checkedAt Silmaril.Proofs.Containers.HttpServe.probeLayout.static ha.1 ha.2
    exact (walk hloop o limit en inp).2
  launch := ⟨fun _ => clearChoice, probe.entry, probe.input, admissible_harness probe _⟩

end Silmaril.Proofs.Containers.HttpServe.Walk
