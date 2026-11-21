module

public import Silmaril.Containers.HttpOnce.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Precondition.Thms
public import Silmaril.Containers.Image.Thms
public import Silmaril.Containers.Http.Thms
public import Silmaril.Net.Http1.Framing.Thms

/-!
# Proofs: the real HTTP responder

Proofs for `Silmaril.Containers.HttpOnce.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Proofs.Containers.HttpOnce

open Silmaril.Containers Silmaril.Containers.HttpOnce Silmaril.Containers.Lps
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes
open Silmaril.Process.LPS.Problems.CoreutilsLite

/-! ## Content digests (kernel-checked SHA-256) -/

theorem elf_digest : Silmaril.Crypto.sha256 elf = elfDigest := by decide +kernel
theorem layer_digest : Silmaril.Crypto.sha256 layer = layerDigest := by decide +kernel
theorem config_digest : Silmaril.Crypto.sha256 config = configDigest := by decide +kernel
theorem manifest_digest : Silmaril.Crypto.sha256 manifest = manifestDigest := by decide +kernel

theorem layer_encode : Silmaril.Formats.Tar.encode [entry] = some layer := by decide +kernel

/-! ## The probe -/

theorem probeLayout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨probeLayout, harnessInput_valid, probe.snapshot_valid probeLayout, by unfold ValidBrk; decide +kernel⟩

/-- The 40 octets the program writes. -/
abbrev msgBytes : List Byte := (probe.bytes.drop 154).take 40

theorem msgBytes_eq : msgBytes.map UInt8.ofBitVec = Fixtures.okResponse := by decide +kernel

/-! ## The ELF loads to the probe's snapshot -/

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

/-! ## The OCI image reads to the flat image of the ELF -/

theorem oci_entry : ((Oci.load layout manifestDigest).toOption.map fun f => f.config.entryPath) =
    some (some ["http-ok"]) := by decide +kernel

theorem oci_root : ((Oci.load layout manifestDigest).toOption.map fun f => f.root ["http-ok"]) =
    some (some (.file elf true)) := by decide +kernel

theorem oci_exposed : ((Oci.load layout manifestDigest).toOption.map fun f => f.config.exposed) =
    some [port] := by decide +kernel

theorem oci_load : ∃ f, Oci.load layout manifestDigest = .ok f ∧
    f.config.entryPath = some ["http-ok"] ∧ f.root ["http-ok"] = some (.file elf true) ∧
    f.config.exposed = [port] := by
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

/-! ## Every execution writes a prefix of the response and exits 0 -/

theorem outEvs_map (ds : List Byte) :
    outEvs (ds.map UInt8.ofBitVec) = ds.map fun b => .stdout [UInt8.ofBitVec b] := by
  simp [outEvs]

theorem post_of {ds : List Byte} (delivered : Probe.WritePrefix msgBytes ds) {c : Word}
    {fs : Fs.FileSystem} {o : Oracle} {final : Silmaril.Process.LPS.Config (isaOf o)}
    (hk : final.model.killedBy = none) (hh : final.model.halted = some 0) :
    PrefixPost (outEvs Fixtures.okResponse) 0 [] (ds.map (.writeEv 1) ++ [.exitEv c fs])
      (.halt final) := by
  refine ⟨⟨_, mapEvs_stdout_exit c fs ds, ?_⟩, final, rfl, hk, hh⟩
  rw [List.nil_append, ← msgBytes_eq, outEvs_map]
  exact delivered.2.map _

theorem exec (o : Oracle) (limit : Int) (en : ExecEntry) (inp : ProcInput)
    [Probe.Checked (probe.launchAt en inp)] :
    Omni.Exec (probe.launchAt en inp).segs spec noFilter ((probe.launchAt en inp).oinitial o limit)
      (PrefixPost (outEvs Fixtures.okResponse) 0 []) := by
  rw [Probe.oinitial_at]
  oprobe_instr 120 5 _
  oprobe_instr 125 5 _
  oprobe_instr 130 5 _
  oprobe_instr 135 5 _
  oprobe_trap 140
  oprobe_write 154 40
  intro ds delivered
  oprobe_instr 142 5 _
  oprobe_instr 147 5 _
  oprobe_trap 152
  oprobe_exit 0
  exact post_of delivered (by oprobe_side) (by oprobe_side)

theorem noClone (o : Oracle) (limit : Int) (en : ExecEntry) (inp : ProcInput)
    (ha : Admissible o probe.snapshot en inp) :
    NoCloneFrom probe.snapshot.image.segments (X86Launch.init (isaOf o) probe.snapshot en limit inp) := by
  have := probe.checkedAt probeLayout.static ha.1 ha.2
  show NoCloneFrom (probe.launchAt en inp).segs ((probe.launchAt en inp).oinitial o limit)
  rw [Probe.oinitial_at]
  noclone_instr 120 5 _
  noclone_instr 125 5 _
  noclone_instr 130 5 _
  noclone_instr 135 5 _
  noclone_trap 140
  noclone_write 154 40
  intro ds _
  noclone_instr 142 5 _
  noclone_instr 147 5 _
  noclone_trap 152
  noclone_exit

theorem emits : Emits probe.snapshot 0 (outEvs Fixtures.okResponse) where
  exec o limit en inp ha := by
    have := probe.checkedAt probeLayout.static ha.1 ha.2
    exact exec o limit en inp
  noClone := noClone
  launch := ⟨fun _ => clearChoice, probe.entry, probe.input, admissible_harness probe _⟩
  outputs e he := by
    simp only [outEvs, List.mem_map] at he
    obtain ⟨b, -, rfl⟩ := he
    rfl

/-! ## The reference run writes all of it -/

theorem full_star (o : Oracle) : ∃ tr, ∃ final : Silmaril.Process.LPS.Config (isaOf o),
    Star probe.snapshot.image.segments spec noFilter
      (X86Launch.init (isaOf o) probe.snapshot probe.entry 0 probe.input) tr final ∧
    mapEvs tr = some (outEvs Fixtures.okResponse) ∧ final.model.halted = some 0 ∧
    final.model.killedBy = none := by
  apply Exists.intro
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Star probe.segs spec noFilter (probe.oinitial o 0) _ _
    rw [Probe.oinitial_at]
    oprobe_instr 120 5 _
    oprobe_instr 125 5 _
    oprobe_instr 130 5 _
    oprobe_instr 135 5 _
    oprobe_trap 140
    oprobe_write 154 40 with msgBytes
    oprobe_instr 142 5 _
    oprobe_instr 147 5 _
    oprobe_trap 152
    oprobe_exit 0
  · rw [mapEvs_stdout_exit, ← outEvs_map, msgBytes_eq]
  all_goals oprobe_side

/-! ## The image -/

theorem prefix_outEvs {t : List Ev} {r : List UInt8} (h : t <+: outEvs r) :
    ∃ bs, bs <+: r ∧ t = outEvs bs := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨l₁, l₂, rfl, h₁, -⟩ := List.map_eq_append_iff.1 hu.symm
  exact ⟨l₁, List.prefix_append _ _, h₁.symm⟩


theorem beh_image (b : Beh Ev) (hb : ociRuntime.toRuntime.beh image b) :
    ∃ t, t <+: outEvs Fixtures.okResponse ∧ b = .done t (.exited 0) := by
  rw [Runtime.beh_ok (R := ociRuntime.toRuntime) runtime_load] at hb
  obtain ⟨b₀, hr, rfl⟩ := hb
  exact runs_prefix emits b₀ hr

theorem full_run : ociRuntime.toRuntime.beh image (.done (outEvs Fixtures.okResponse) (.exited 0)) := by
  rw [Runtime.beh_ok (R := ociRuntime.toRuntime) runtime_load]
  obtain ⟨tr, final, hs, hu, hh, hk⟩ := full_star (fun _ => clearChoice)
  exact ⟨_, run_of_star emits (admissible_harness probe _) hs hu hh hk, rfl⟩

theorem okResponse_exact : IsOkResponse Fixtures.okResponse := by
  have he : Fixtures.okResponse =
      [] ++ Silmaril.Net.Http1.encResponse Http.Fixtures.okHead (.content (Fixtures.ascii "ok")) ++ [] := by
    decide
  have h := Silmaril.Net.Http1.parseResponseAt_encode (method := Fixtures.ascii "GET")
    (h := Http.Fixtures.okHead) (b := .content (Fixtures.ascii "ok")) (by decide +kernel)
    (show (Fixtures.ascii "ok").length = 2 by decide) [] []
  unfold IsOkResponse Silmaril.Net.Http1.parseResponse
  rw [he]
  simpa using h

end Silmaril.Proofs.Containers.HttpOnce
