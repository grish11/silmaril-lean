module

public import Silmaril.Containers.HttpOnce.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Precondition.Thms
public import Silmaril.Containers.Http.Thms
import Silmaril.Proofs.Containers.HttpOnce.Basic

/-!
# A real HTTP responder: theorems

> **Experimental API.** Names and statements in `Silmaril.Containers` may change.

PROVED (standard axioms; kernel evaluation for the digests, the archive, the JSON documents, the
ELF parse and the HTTP reader). Proofs are in `Silmaril.Proofs.Containers.HttpOnce`.

**What is proved, about which object.** The object is the OCI image `image` (pinned digests), read
by the restricted OCI reader and run by the LPS adapter on the x86-64 machine (`Lps.ociRuntime`:
every flag oracle, every admissible launch, every allocation limit, the sequential clone policy
`seqPolicy`, under which thread creation is undefined behaviour).

* `wp_image`: on **every** run there is no undefined behaviour, the run exits with status 0, and its
  events are standard-output octets forming a prefix of the response (`respondsOk`). Total
  correctness: no crash, no blocking, no divergence, no task creation, no other event.
* `full_run`: the run that writes all 40 octets exists (the reference execution, in which `write`
  delivers everything it is asked to).
* `okResponse_exact`: those 40 octets are judged exactly by the verified HTTP/1.1 reader: one
  response to `GET`, head `Http.Fixtures.okHead` (HTTP/1.1, 200), content `ok`, every octet
  consumed (`IsOkResponse`).
* `declared`: the image's configuration declares `8080/tcp`, the port of the HTTP/1.1 interface
  `Http.Fixtures.httpIface`, which is valid and admissible under `tcpOnly` (`Http.Thms`).

**What is not proved.** That every run writes the whole response: LPS allows a short write and
the program does not retry, so `wp_image` says "a prefix". That the response reaches a TCP peer:
the program writes standard output; the accept loop that connects it to port 8080 is the test
harness's (`examples/containers/http-once/docker-test.sh`), outside the image and outside the
model. Protocol conformance of a server: this is one fixed response, judged by one reader.
Nothing here describes Docker, runc or a kernel; the Docker run is a test.
-/

public section

set_option maxRecDepth 100000

namespace Silmaril.Containers.HttpOnce

open Silmaril.Containers Silmaril.Containers.Lps
open Silmaril.Process.LPS.Probes

theorem elf_digest : Silmaril.Crypto.sha256 elf = elfDigest :=
  Silmaril.Proofs.Containers.HttpOnce.elf_digest

theorem layer_digest : Silmaril.Crypto.sha256 layer = layerDigest :=
  Silmaril.Proofs.Containers.HttpOnce.layer_digest

theorem config_digest : Silmaril.Crypto.sha256 config = configDigest :=
  Silmaril.Proofs.Containers.HttpOnce.config_digest

theorem manifest_digest : Silmaril.Crypto.sha256 manifest = manifestDigest :=
  Silmaril.Proofs.Containers.HttpOnce.manifest_digest

theorem layer_encode : Silmaril.Formats.Tar.encode [entry] = some layer :=
  Silmaril.Proofs.Containers.HttpOnce.layer_encode

theorem loadElf_elf : loadElf elf = some probe.snapshot :=
  Silmaril.Proofs.Containers.HttpOnce.loadElf_elf

theorem runtime_load : ociRuntime.load image = .ok probe.snapshot :=
  Silmaril.Proofs.Containers.HttpOnce.runtime_load

/-- The configuration the reader returns declares the HTTP/1.1 interface's port, `8080/tcp`. -/
theorem declared : ∃ f, Oci.load layout manifestDigest = .ok f ∧ f.config.exposed = [port] ∧
    Http.Fixtures.httpIface.Declared f.config := by
  obtain ⟨f, hl, -, -, he⟩ := Silmaril.Proofs.Containers.HttpOnce.oci_load
  exact ⟨f, hl, he, by rw [Http.Iface.Declared, he]; exact List.mem_singleton_self _⟩

/-- Every launch writes a prefix of the response and exits 0, never creating a task. -/
theorem emits : Emits probe.snapshot 0 (outEvs Fixtures.okResponse) :=
  Silmaril.Proofs.Containers.HttpOnce.emits

theorem beh_image (b : Beh Ev) (hb : ociRuntime.toRuntime.beh image b) :
    ∃ t, t <+: outEvs Fixtures.okResponse ∧ b = .done t (.exited 0) :=
  Silmaril.Proofs.Containers.HttpOnce.beh_image b hb

/-- **The composed claim**: no undefined behaviour, exit 0, and a prefix of the response on
standard output, on every run. -/
theorem wp_image : wp ociRuntime.toRuntime respondsOk image := fun b hb => by
  obtain ⟨t, ht, rfl⟩ := beh_image b hb
  exact ⟨trivial, rfl, Silmaril.Proofs.Containers.HttpOnce.prefix_outEvs ht⟩

/-- **The full response is a run.** -/
theorem full_run : ociRuntime.toRuntime.beh image (.done (outEvs Fixtures.okResponse) (.exited 0)) :=
  Silmaril.Proofs.Containers.HttpOnce.full_run

/-- **The exact HTTP judgment** of the full response. -/
theorem okResponse_exact : IsOkResponse Fixtures.okResponse :=
  Silmaril.Proofs.Containers.HttpOnce.okResponse_exact

end Silmaril.Containers.HttpOnce
