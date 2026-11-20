module

public import Silmaril.Containers.HttpServe.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Image.Thms
public import Silmaril.Containers.HttpOnce.Thms
public import Silmaril.Process.LPS.MonadIff
public import Silmaril.Containers.Ports.Thms
public import Silmaril.Containers.Precondition.Thms

/-!
# Proofs: the self-contained HTTP server

Proofs for `Silmaril.Containers.HttpServe.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Proofs.Containers.HttpServe

open Silmaril.Containers Silmaril.Containers.HttpServe Silmaril.Containers.Lps
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

/-! ## Content digests (kernel-checked SHA-256) -/

theorem elf_digest : Silmaril.Crypto.sha256 elf = elfDigest := by decide +kernel
theorem layer_digest : Silmaril.Crypto.sha256 layer = layerDigest := by decide +kernel
theorem config_digest : Silmaril.Crypto.sha256 config = configDigest := by decide +kernel
theorem manifest_digest : Silmaril.Crypto.sha256 manifest = manifestDigest := by decide +kernel

theorem layer_encode : Silmaril.Formats.Tar.encode [entry] = some layer := by decide +kernel

/-! ## The ELF loads to the probe's snapshot -/

theorem probeLayout : probe.Layout := by probe_layout

theorem parse_map : (ELFImage.parse ELFImage.x86Policy (elfBytes elf)).map
    (·.x86Snapshot (elfBytes elf)) = some probe.snapshot := by rfl

theorem imageWf_native : ImageWf x86ExtNative probe.snapshot.image := by
  have v := probe.snapshot_valid probeLayout
  refine ⟨v.2.2.2.2.1, ?_, by decide +kernel⟩
  simp only [imagePhdrsReadable, v.2.2.2.2.2, Bool.and_true]
  decide +kernel

theorem loadElf_elf : loadElf elf = some probe.snapshot := by
  unfold loadElf ELFImage.loadX86
  have h := parse_map
  cases hp : ELFImage.parse ELFImage.x86Policy (elfBytes elf) with
  | none => rw [hp] at h; cases h
  | some r =>
    rw [hp] at h
    have hs : r.x86Snapshot (elfBytes elf) = probe.snapshot := Option.some.inj h
    have hi : r.image (elfBytes elf) = probe.snapshot.image := by rw [← hs]; rfl
    show (if ImageWf x86ExtNative (r.image (elfBytes elf)) then some (r.x86Snapshot (elfBytes elf))
      else none) = some probe.snapshot
    rw [hi]
    simp only [imageWf_native, ↓reduceIte, hs]

/-! ## The OCI image -/

theorem oci_entry : ((Oci.load layout manifestDigest).toOption.map fun f => f.config.entryPath) =
    some (some ["http-serve"]) := by decide +kernel

theorem oci_root : ((Oci.load layout manifestDigest).toOption.map fun f => f.root ["http-serve"]) =
    some (some (.file elf true)) := by decide +kernel

theorem oci_exposed : ((Oci.load layout manifestDigest).toOption.map fun f => f.config.exposed) =
    some [HttpOnce.port] := by decide +kernel

theorem oci_load : ∃ f, Oci.load layout manifestDigest = .ok f ∧
    f.config.entryPath = some ["http-serve"] ∧ f.root ["http-serve"] = some (.file elf true) ∧
    f.config.exposed = [HttpOnce.port] := by
  have h₁ := oci_entry
  have h₂ := oci_root
  have h₃ := oci_exposed
  cases hl : Oci.load layout manifestDigest with
  | error r => rw [hl] at h₁; cases h₁
  | ok f =>
    rw [hl] at h₁ h₂ h₃
    exact ⟨f, rfl, Option.some.inj h₁, Option.some.inj h₂, Option.some.inj h₃⟩

theorem runtime_load : ociRuntime.load image = .ok probe.snapshot := by
  obtain ⟨f, hl, he, hr, -⟩ := oci_load
  show (Oci.load layout manifestDigest).bind runtime.load = _
  rw [hl]
  show runtime.load f = _
  have hp := Shape.entry_program (k := .static) (dec := loadElf) he hr
  simp only [runtime, hp, loadElf_elf]

/-- The response is in the loaded image, where the program points `sendto` at. -/
theorem response_in_image : ((probe.bytes.drop 345).take 40).map UInt8.ofBitVec = Fixtures.okResponse := by
  decide +kernel

/-- The address bytes are in the loaded image, where the program points `bind` at. -/
theorem addr_in_image : (probe.bytes.drop 329).take 16 = addrBytes := by decide +kernel

/-! ## LPS's `bind` to port 8080 -/

theorem bind_port_unmodeled (fd addrp : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (hfd : fdLookup m.fds fd = some (.socket .fresh))
    (hmem : readBytesMap i.mem addrp 16 = some addrBytes) :
    bindSpec fd addrp 16 i m o ↔ o = .unmodeled := by
  unfold bindSpec
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  have hal : sint32 (16 : Word) = 16 := by decide
  have hz : zw (16 : Int) = 16 := by decide
  simp only [hfd, hal, hz, hmem]
  have h1 : ¬ ((16 : Int) < 0 ∨ SOCKADDR_STORAGE_SIZE < 16) := by decide
  have h2 : ¬ ((16 : Int) = 0) := by decide
  have h3 : ¬ ((16 : Int) < SOCKADDR_IN_SIZE) := by decide
  have h4 : ¬ ¬ (saFamilyOf addrBytes = AF_INET ∨
      (saFamilyOf addrBytes = AF_UNSPEC ∧ sinAddrOf addrBytes = INADDR_ANY)) := by decide
  have h5 : ¬ (sinAddrOf addrBytes ≠ INADDR_ANY) := by decide
  have h6 : sinPortOf addrBytes ≠ 0 := by decide
  simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte, ne_eq, not_false_eq_true]
  unfold recordCopyins
  cases o with
  | ok y m₂ evs => simp only [Sys.bind, Sys.unmodeled, reduceCtorEq, false_and, exists_false]
  | unmodeled => simp [Sys.bind, Sys.unmodeled]

/-! ## `bind` to 8080 with the port published -/

/-- The address with its port read as 0. -/
def addrBytes0 : List Byte := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem readBytesAux_some_iff (mp : Word → Option Byte) : ∀ (n : Nat) (a : Word) (bs : List Byte),
    readBytesAux mp a n = some bs ↔
      bs.length = n ∧ ∀ k (hk : k < bs.length), mp (a + BitVec.ofNat 64 k) = some bs[k]
  | 0, a, bs => by
    cases bs <;> simp [readBytesAux]
  | n + 1, a, bs => by
    simp only [readBytesAux]
    cases hm : mp a with
    | none =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hl h
      have := h 0 (by omega)
      simp [hm] at this
    | some b =>
      simp only [Option.map_eq_some_iff]
      constructor
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨hl, hr⟩ := (readBytesAux_some_iff mp n (a + 1) r).1 hr
        refine ⟨by simp [hl], fun k hk => ?_⟩
        cases k with
        | zero => simpa using hm
        | succ k =>
          have := hr k (by simp at hk; omega)
          simp only [List.getElem_cons_succ]
          rw [← this]
          congr 1
          rw [BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]
          omega
      · rintro ⟨hl, h⟩
        cases bs with
        | nil => simp at hl
        | cons c r =>
          have h0 := h 0 (by simp)
          simp [hm] at h0
          subst h0
          refine ⟨r, (readBytesAux_some_iff mp n (a + 1) r).2 ⟨by simpa using hl, fun k hk => ?_⟩, rfl⟩
          have := h (k + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at this
          rw [← this]
          congr 1
          rw [BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]
          omega

theorem zeroPort_read (i : SyscallInput) (a : Word) (h : readBytesMap i.mem a 16 = some addrBytes) :
    readBytesMap (Ports.zeroPort i a).mem a 16 = some addrBytes0 := by
  unfold readBytesMap at h ⊢
  have h16 : (16 : Word).toNat = 16 := rfl
  rw [h16] at h ⊢
  obtain ⟨-, hb⟩ := (readBytesAux_some_iff _ 16 a addrBytes).1 h
  refine (readBytesAux_some_iff _ 16 a addrBytes0).2 ⟨rfl, fun k hk => ?_⟩
  have hk16 : k < 16 := hk
  have e := hb k hk16
  simp only [Ports.zeroPort]
  have ne : ∀ j : Nat, j < 16 → (a + BitVec.ofNat 64 k = a + j ↔ k = j) := by
    intro j hj
    constructor
    · intro h'
      have := congrArg BitVec.toNat (add_left_cancel h')
      simp at this
      omega
    · rintro rfl; rfl
  have e2 := ne 2 (by omega)
  have e3 := ne 3 (by omega)
  simp only [show (2 : Word) = BitVec.ofNat 64 2 from rfl, show (3 : Word) = BitVec.ofNat 64 3 from rfl] at *
  interval_cases k <;> simp_all <;> rfl

/-- LPS's `bind` of a fresh socket to the address with port 0. -/
theorem bind0 (fd addrp : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (hfd : fdLookup m.fds fd = some (.socket .fresh))
    (hmem : readBytesMap i.mem addrp 16 = some addrBytes0) :
    bindSpec fd addrp 16 i m o ↔
      o = .ok ((mkEffect (errnoRet EADDRINUSE) [] []).withCopyins [(addrp, 16)]) m [] ∨
      o = .ok ((mkEffect 0 [] []).withCopyins [(addrp, 16)])
        (m.withFds (fdInsert m.fds fd (.socket .bound))) [] := by
  unfold bindSpec
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  have hal : sint32 (16 : Word) = 16 := by decide
  have hz : zw (16 : Int) = 16 := by decide
  simp only [hfd, hal, hz, hmem]
  have h1 : ¬ ((16 : Int) < 0 ∨ SOCKADDR_STORAGE_SIZE < 16) := by decide
  have h2 : ¬ ((16 : Int) = 0) := by decide
  have h3 : ¬ ((16 : Int) < SOCKADDR_IN_SIZE) := by decide
  have h4 : ¬ ¬ (saFamilyOf addrBytes0 = AF_INET ∨
      (saFamilyOf addrBytes0 = AF_UNSPEC ∧ sinAddrOf addrBytes0 = INADDR_ANY)) := by decide
  have h5 : ¬ (sinAddrOf addrBytes0 ≠ INADDR_ANY) := by decide
  have h6 : ¬ (sinPortOf addrBytes0 ≠ 0) := by decide
  simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]
  unfold recordCopyins
  cases o with
  | unmodeled =>
    simp [Sys.bind, Sys.alt, errnoFrom, Sys.choose, errRet, retOnly, Sys.pure, Sys.setFds, Sys.modify,
      bindErrnos, Bind.bind]
  | ok y m₂ evs =>
    simp [Sys.bind, Sys.alt, errnoFrom, Sys.choose, errRet, retOnly, Sys.pure, Sys.setFds, Sys.modify,
      bindErrnos, Bind.bind]
    constructor
    · rintro ⟨x, (⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩), rfl⟩
      · exact .inl ⟨rfl, rfl, rfl⟩
      · exact .inr ⟨rfl, rfl, rfl⟩
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · exact ⟨_, .inl ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
      · exact ⟨_, .inr ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

theorem publishedBind_server (i : SyscallInput) (hno : i.sysno.toNat = 49)
    (hclear : NativeX86.All.boundarySuspect 49 i = false) (hlen : i.arg 2 = 16)
    (hmem : readBytesMap i.mem (i.arg 1) 16 = some addrBytes) :
    Ports.publishedBind [8080] i = true := by
  have hz : zw (sint32 (16 : Word)) = 16 := by decide
  simp only [Ports.publishedBind, hno, hclear, hlen, hz, hmem]
  decide

/-- **`bind` to 8080 with 8080 published**: from a fresh socket, the outcomes LPS gives port 0:
the injected `EADDRINUSE`, or the socket is bound. -/
theorem bind_published (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (hno : i.sysno.toNat = 49) (hclear : NativeX86.All.boundarySuspect 49 i = false)
    (hlen : i.arg 2 = 16) (hfd : fdLookup m.fds (fd32 (i.arg 0)) = some (.socket .fresh))
    (hmem : readBytesMap i.mem (i.arg 1) 16 = some addrBytes) :
    Ports.publish [8080] i m o ↔
      o = .ok ((mkEffect (errnoRet EADDRINUSE) [] []).withCopyins [(i.arg 1, 16)]) m [] ∨
      o = .ok ((mkEffect 0 [] []).withCopyins [(i.arg 1, 16)])
        (m.withFds (fdInsert m.fds (fd32 (i.arg 0)) (.socket .bound))) [] := by
  rw [Ports.publish_of_published (publishedBind_server i hno hclear hlen hmem), hlen]
  exact bind0 _ _ _ m o hfd (zeroPort_read i _ hmem)

/-! ## The runtime that publishes the declared ports -/

theorem published_load : Ports.ociRuntime.load image = .ok (probe.snapshot, [8080]) := by
  obtain ⟨f, hl, he, hr, hx⟩ := oci_load
  show (Oci.load layout manifestDigest).bind _ = _
  rw [hl]
  have hp := Shape.entry_program (k := .static) (dec := loadElf) he hr
  have hrt : Lps.runtime.load f = .ok probe.snapshot := by simp only [Lps.runtime, hp, loadElf_elf]
  show (Lps.runtime.load f).map _ = _
  rw [hrt, Ports.tcpPorts, hx]
  rfl

/-- **The image obligation reduces to the program obligation.** -/
theorem servesImage_of_sound (h : Task.serverSound) : Task.servesImage := by
  intro b hb
  rw [Runtime.beh_ok published_load] at hb
  obtain ⟨b₀, hr, rfl⟩ := hb
  obtain ⟨hnb, hpost⟩ := Lps.runs_sound h b₀ hr
  refine ⟨hnb, ?_⟩
  match b₀, hpost with
  | .done t (.exited c), hpost =>
    obtain ⟨k, rfl, hg⟩ := hpost t _ rfl
    exact hg
  | .done _ (.signaled _), _ => trivial
  | .done _ (.killed _), _ => trivial
  | .done _ (.refused _), _ => trivial
  | .done _ (.undefined _), _ => trivial
  | .blocked _, _ => trivial
  | .spins _, _ => trivial
  | .reactive _, _ => trivial

/-! ## A successful session, read by the server platform -/

theorem sockTrace_recv (ch : Word) (bs : List UInt8) :
    Http.sockTrace (recvEvs (connSock ch) bs) = bs.map fun b => .recv ch.toNat [b] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [recvEvs, List.map_cons, Http.sockTrace, List.filterMap_cons] at ih ⊢
    rw [ih]
    rfl

theorem sockTrace_send (ch : Word) (bs : List UInt8) :
    Http.sockTrace (sendEvs (connSock ch) bs) = bs.map fun b => .send ch.toNat [b] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [sendEvs, List.map_cons, Http.sockTrace, List.filterMap_cons] at ih ⊢
    rw [ih]
    rfl

theorem sent_recvs (c : Nat) (bs : List UInt8) :
    Servers.Platform.sent c (bs.map fun b => .recv c [b]) = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [Servers.Platform.sent] using ih

theorem sent_sends (c : Nat) (bs : List UInt8) (t : List Servers.Platform.SockEv) :
    Servers.Platform.sent c ((bs.map fun b => .send c [b]) ++ t) = bs ++ Servers.Platform.sent c t := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [Servers.Platform.sent] using ih

theorem sessionOk_sent {t : List Ev} {c : UInt8} (h : SessionOk t c) :
    ∃ ch : Word, Servers.Platform.sent ch.toNat (Http.sockTrace t) = Fixtures.okResponse := by
  obtain ⟨-, ch, req, rfl⟩ := h
  refine ⟨ch, ?_⟩
  rw [Http.sockTrace, List.filterMap_append, ← Http.sockTrace, ← Http.sockTrace, sockTrace_send,
    sockTrace_recv, sent_sends, sent_recvs, List.append_nil]

end Silmaril.Proofs.Containers.HttpServe
