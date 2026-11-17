module

public import Silmaril.Containers.Noop.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Precondition.Thms
public import Silmaril.Containers.Image.Thms
public import Silmaril.Process.LPS.Problems.CoreutilsLite.TrueFalse

/-!
# Proofs: the static no-op ELF in an OCI image

Proofs for `Silmaril.Containers.Noop.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Proofs.Containers.Noop

open Silmaril.Containers Silmaril.Containers.Noop Silmaril.Containers.Lps
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes
open Silmaril.Process.LPS.Problems.CoreutilsLite

/-- The probe of the pinned ELF. -/
abbrev P : Probe := Data.LiteTrue.probe

/-! ## Content digests (kernel-checked SHA-256) -/

theorem elf_digest : Silmaril.Crypto.sha256 elf = elfDigest := by decide +kernel
theorem layer_digest : Silmaril.Crypto.sha256 layer = layerDigest := by decide +kernel
theorem config_digest : Silmaril.Crypto.sha256 config = configDigest := by decide +kernel
theorem manifest_digest : Silmaril.Crypto.sha256 manifest = manifestDigest := by decide +kernel

theorem layer_encode : Silmaril.Formats.Tar.encode [entry] = some layer := by decide +kernel

/-! ## The ELF loads to the probe's snapshot -/

theorem parse_map : (ELFImage.parse ELFImage.x86Policy (elfBytes elf)).map
    (·.x86Snapshot (elfBytes elf)) = some P.snapshot := by rfl

theorem imageWf_native : ImageWf x86ExtNative P.snapshot.image := by
  have v := P.snapshot_valid LiteTrue.layout
  refine ⟨v.2.2.2.2.1, ?_, by decide +kernel⟩
  simp only [imagePhdrsReadable, v.2.2.2.2.2, Bool.and_true]
  decide +kernel

theorem loadElf_elf : loadElf elf = some P.snapshot := by
  unfold loadElf ELFImage.loadX86
  have h := parse_map
  cases hp : ELFImage.parse ELFImage.x86Policy (elfBytes elf) with
  | none => rw [hp] at h; cases h
  | some r =>
    rw [hp] at h
    have hs : r.x86Snapshot (elfBytes elf) = P.snapshot := Option.some.inj h
    have hi : r.image (elfBytes elf) = P.snapshot.image := by rw [← hs]; rfl
    show (if ImageWf x86ExtNative (r.image (elfBytes elf)) then some (r.x86Snapshot (elfBytes elf))
      else none) = some P.snapshot
    rw [hi]
    simp only [imageWf_native, ↓reduceIte, hs]

/-! ## The OCI image reads to the flat image of the ELF -/

theorem oci_entry : ((Oci.load layout manifestDigest).toOption.map fun f => f.config.entryPath) =
    some (some ["noop"]) := by decide +kernel

theorem oci_root : ((Oci.load layout manifestDigest).toOption.map fun f => f.root ["noop"]) =
    some (some (.file elf true)) := by decide +kernel

theorem oci_load : ∃ f, Oci.load layout manifestDigest = .ok f ∧
    f.config.entryPath = some ["noop"] ∧ f.root ["noop"] = some (.file elf true) := by
  have h₁ := oci_entry
  have h₂ := oci_root
  cases hl : Oci.load layout manifestDigest with
  | error r => rw [hl] at h₁; cases h₁
  | ok f =>
    rw [hl] at h₁ h₂
    exact ⟨f, rfl, Option.some.inj h₁, Option.some.inj h₂⟩

theorem runtime_load : ociRuntime.load image = .ok P.snapshot := by
  obtain ⟨f, hl, he, hr⟩ := oci_load
  show (Oci.load layout manifestDigest).bind runtime.load = _
  rw [hl]
  show runtime.load f = _
  have hp := Shape.entry_program (k := .static) (dec := loadElf) he hr
  simp only [runtime, hp, loadElf_elf]

/-! ## The program only exits, with status 0, and never creates a task -/

theorem noClone (o : Oracle) (limit : Int) (en : ExecEntry) (inp : ProcInput)
    (ha : Admissible o P.snapshot en inp) :
    NoCloneFrom P.snapshot.image.segments (X86Launch.init (isaOf o) P.snapshot en limit inp) := by
  have := P.checkedAt LiteTrue.layout.static ha.1 ha.2
  show NoCloneFrom (P.launchAt en inp).segs ((P.launchAt en inp).oinitial o limit)
  rw [Probe.oinitial_at]
  noclone_instr 128 5 _
  noclone_instr 133 2 _
  noclone_trap 135
  noclone_exit

theorem exitOnly : ExitOnly P.snapshot 0 where
  exec o limit en inp ha :=
    Omni.exec_conseq (true_total o limit en inp trivial ha).exec fun tr out h => by
      obtain ⟨final, rfl, hk, code, hh, htr, hc⟩ := h
      subst htr hc
      refine ⟨fun e he => ?_, final, rfl, hk, hh⟩
      simp only [List.mem_singleton] at he
      subst he
      trivial
  noClone := noClone
  launch := ⟨fun _ => clearChoice, P.entry, P.input, admissible_harness P _⟩

/-! ## The image -/

theorem beh_image (b : Beh Ev) :
    ociRuntime.toRuntime.beh image b ↔ b = .done [] (.exited 0) := by
  rw [Runtime.beh_ok (R := ociRuntime.toRuntime) runtime_load]
  constructor
  · rintro ⟨b₀, hr, rfl⟩
    exact runs_eq exitOnly b₀ hr
  · rintro rfl
    exact ⟨_, run_exists exitOnly, rfl⟩

end Silmaril.Proofs.Containers.Noop
