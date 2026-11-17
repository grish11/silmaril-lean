module

public import Silmaril.Containers.Noop.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Precondition.Thms
import Silmaril.Proofs.Containers.Noop.Basic

/-!
# The static no-op ELF in an OCI image: theorems

PROVED (standard axioms; kernel evaluation for the digests, the archive, the JSON documents and
the ELF parse). Proofs are in `Silmaril.Proofs.Containers.Noop`.

**Content digests.** `elf_digest`, `layer_digest`, `config_digest`, `manifest_digest`: SHA-256
(`Silmaril.Crypto.sha256`) of each artifact is its pinned digest. `layer_encode`: the layer is
`Tar.encode [entry]`, so `Tar.decode` reads `entry` back (`Tar.decode_encode`).

**Loading.**

* `loadElf_elf`: LPS's x86-64 loader (`ELFImage.loadX86`) accepts the octets and returns the
  probe's snapshot `Probes.Data.LiteTrue.probe.snapshot`. The parse is evaluated by the kernel;
  the two image checks that the kernel cannot evaluate (the entry instruction is fetchable, the
  program headers are readable) come from the probe kit's `Probe.snapshot_valid`, a theorem, not
  an assumption.
* `runtime_load`: the OCI reader with checked digests, then the entry-point shape, then the loader:
  the image's program is that snapshot.

**The image** (the composed claim). Under `Lps.ociRuntime` (the restricted OCI reader, LPS on the
x86-64 machine for every flag oracle, every admissible launch, every allocation limit, and the
sequential clone policy):

* `beh_image`: the image has exactly one run, `done [] (exited 0)`;
* `wp_image`: the verification precondition of "no undefined behaviour, exit 0, no events" holds
  (total correctness, `wp`);
* `confined_image`: the run is confined to the empty profile: no environment events at all.

From `CoreutilsLite.true_total` (every LPS execution is finite, error free and exits 0), the
clone-freedom of the probe's execution (`noClone`, along its unique-successor chain), and
`Lps.runs_eq`.

**Refusals.** `refuses_tampered` (a layer that does not hash to its digest: `badDigest`),
`refuses_missing` (no config blob: `missingBlob`), `refuses_gzip` (a compressed layer, outside
the profile: `other`).

**What this is not.** A statement about Docker, runc or a Linux kernel. The trust boundary is
the LPS model (its transcription of Linux system calls and the x86-64 semantics behind it), the
admissibility of launches, and the reader's profile. `examples/containers/noop-oci/` runs the
same image under Docker as a differential test, not a proof.
-/

public section

set_option maxRecDepth 100000

namespace Silmaril.Containers.Noop

open Silmaril.Containers Silmaril.Containers.Lps
open Silmaril.Process.LPS.Probes

theorem elf_digest : Silmaril.Crypto.sha256 elf = elfDigest :=
  Silmaril.Proofs.Containers.Noop.elf_digest
theorem layer_digest : Silmaril.Crypto.sha256 layer = layerDigest :=
  Silmaril.Proofs.Containers.Noop.layer_digest
theorem config_digest : Silmaril.Crypto.sha256 config = configDigest :=
  Silmaril.Proofs.Containers.Noop.config_digest
theorem manifest_digest : Silmaril.Crypto.sha256 manifest = manifestDigest :=
  Silmaril.Proofs.Containers.Noop.manifest_digest
theorem layer_encode : Silmaril.Formats.Tar.encode [entry] = some layer :=
  Silmaril.Proofs.Containers.Noop.layer_encode

theorem loadElf_elf : loadElf elf = some Data.LiteTrue.probe.snapshot :=
  Silmaril.Proofs.Containers.Noop.loadElf_elf

theorem runtime_load : ociRuntime.load image = .ok Data.LiteTrue.probe.snapshot :=
  Silmaril.Proofs.Containers.Noop.runtime_load

theorem exitOnly : ExitOnly Data.LiteTrue.probe.snapshot 0 :=
  Silmaril.Proofs.Containers.Noop.exitOnly

theorem beh_image (b : Beh Ev) : ociRuntime.toRuntime.beh image b ↔ b = .done [] (.exited 0) :=
  Silmaril.Proofs.Containers.Noop.beh_image b

/-- **The composed claim**: no undefined behaviour, exit 0, no events, on every run. -/
theorem wp_image : wp ociRuntime.toRuntime exitZeroNoEvents image := fun b hb => by
  rw [(beh_image b).1 hb]
  exact ⟨trivial, rfl, rfl⟩

theorem confined_image :
    pre ociRuntime.toRuntime (Spec.always fun e => Profile.none e.cap = true) image := by
  intro b hb u hu e he
  rw [(beh_image b).1 hb] at hu
  rw [List.eq_nil_of_prefix_nil hu] at he
  cases he

theorem refuses_tampered : refusal? (Oci.load tampered manifestDigest) = some .badDigest := by
  decide +kernel

theorem refuses_missing : refusal? (Oci.load missingConfig manifestDigest) = some .missingBlob := by
  decide +kernel

theorem refuses_gzip :
    refusal? (Oci.load gzipLayout (Silmaril.Crypto.sha256 gzipManifest)) = some .other := by
  decide +kernel

end Silmaril.Containers.Noop
