module

public import Silmaril.Containers.Lps.Defs
public import Silmaril.Containers.Fixtures.Defs
public import Silmaril.Process.LPS.Probes.Data.LiteTrue

/-!
# The first real fixture: a static no-op ELF in an OCI image

**One pinned artifact.** The program is the 352-octet static x86-64 ELF of the LPS probe
`lite_true` (`Silmaril.Process.LPS.Probes.Data.LiteTrue.fileBytes`: GCC 13.3 `-O2` `true`,
`mov $60,%eax; xor %edi,%edi; syscall`, one `PT_LOAD`), SHA-256
`faf558ec522716eb1b0979289f73782140a1812d73b2ae596040498f1dd74675`, pinned in
`examples/verification-projects/theorem-dev/lps-probes/SHA256SUMS`. `elf` is that list of
octets, and every other artifact is computed from it.

(An earlier experiment packaged `examples/project-formats/example-exec.elf`, 632 octets, SHA-256
`78876f12…ec9f`, with Docker. That file has four program headers and only load facts proved; it
is not used here. `lite_true` is used because LPS already proves it totally correct:
`Silmaril.Process.LPS.Problems.CoreutilsLite.true_total`.)

**The image**, deterministic, `FROM scratch`: one uncompressed layer, the tar archive
`Tar.encode [entry]` of one regular file `noop`, mode `0755`, owner 0, time 0 (2048 octets,
SHA-256 `c2e4b98b…5d14`); a configuration with `Entrypoint ["/noop"]` (185 octets, `d77f6e9c…0260`);
and a manifest (397 octets, `f13b70f2…42d8`). `examples/containers/noop-oci/` holds the same blobs
as files, written by `examples/containers/noop-oci/generate.lean`, for the Docker differential test.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Noop

open Silmaril.Containers Silmaril.Formats

/-- **The pinned ELF**: the octets of `lite_true`. -/
def elf : List UInt8 := Silmaril.Process.LPS.Probes.Data.LiteTrue.fileBytes.map UInt8.ofBitVec

/-- Its SHA-256 digest. -/
def elfDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:faf558ec522716eb1b0979289f73782140a1812d73b2ae596040498f1dd74675").getD []

/-- The layer's only entry. -/
def entry : Tar.Entry := { name := "noop", mode := 493, data := elf }

/-- **The layer**: the tar archive of `entry`. -/
def layer : List UInt8 := (Tar.encode [entry]).getD []

def layerDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:c2e4b98bae96ca80b54509d3067c208b6f9d22d9153e6ae80a83c947787a5d14").getD []

/-- **The configuration.** -/
def configText : String :=
  "{\"architecture\":\"amd64\",\"os\":\"linux\",\"config\":{\"Entrypoint\":[\"/noop\"]},\"rootfs\":{\"type\":\"layers\",\"diff_ids\":[\"sha256:c2e4b98bae96ca80b54509d3067c208b6f9d22d9153e6ae80a83c947787a5d14\"]}}"

def config : List UInt8 := Fixtures.ascii configText

def configDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:d77f6e9c553c0f0a3c2370fc870c57f500b2a0769f056a757365959928ca0260").getD []

/-- **The manifest.** -/
def manifestText : String :=
  "{\"schemaVersion\":2,\"mediaType\":\"application/vnd.oci.image.manifest.v1+json\",\"config\":{\"mediaType\":\"application/vnd.oci.image.config.v1+json\",\"digest\":\"sha256:d77f6e9c553c0f0a3c2370fc870c57f500b2a0769f056a757365959928ca0260\",\"size\":185},\"layers\":[{\"mediaType\":\"application/vnd.oci.image.layer.v1.tar\",\"digest\":\"sha256:c2e4b98bae96ca80b54509d3067c208b6f9d22d9153e6ae80a83c947787a5d14\",\"size\":2048}]}"

def manifest : List UInt8 := Fixtures.ascii manifestText

def manifestDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:f13b70f2cd9336b73436e4c76fd475138a253c140d1a4e2d80dbddd03f2542d8").getD []

/-- **The image layout's blobs.** -/
def layout : Oci.Layout := ⟨[(manifestDigest, manifest), (configDigest, config), (layerDigest, layer)]⟩

/-- **The image**: the layout and the digest of its manifest. -/
def image : Oci.Layout × Oci.Digest := (layout, manifestDigest)

/-- The postcondition of the no-op: no events, exit status 0. -/
def exitZeroNoEvents (t : List Ev) (c : UInt8) : Prop := t = [] ∧ c = 0

/-! ## Images the reader must refuse -/

/-- The reason a read failed, if it did. -/
def refusal? {α : Type} : Except Refusal α → Option Refusal
  | .ok _ => none
  | .error r => some r

/-- The layer with its first octet changed, stored under the original digest. -/
def tampered : Oci.Layout :=
  ⟨[(manifestDigest, manifest), (configDigest, config), (layerDigest, (layer.headD 0 + 1) :: layer.tail)]⟩

/-- The configuration blob is missing. -/
def missingConfig : Oci.Layout := ⟨[(manifestDigest, manifest), (layerDigest, layer)]⟩

/-- A manifest that declares a gzip-compressed layer, stored under its own digest. -/
def gzipManifest : List UInt8 := Fixtures.ascii
  "{\"schemaVersion\":2,\"mediaType\":\"application/vnd.oci.image.manifest.v1+json\",\"config\":{\"mediaType\":\"application/vnd.oci.image.config.v1+json\",\"digest\":\"sha256:d77f6e9c553c0f0a3c2370fc870c57f500b2a0769f056a757365959928ca0260\",\"size\":185},\"layers\":[{\"mediaType\":\"application/vnd.oci.image.layer.v1.tar+gzip\",\"digest\":\"sha256:c2e4b98bae96ca80b54509d3067c208b6f9d22d9153e6ae80a83c947787a5d14\",\"size\":2048}]}"

def gzipLayout : Oci.Layout :=
  ⟨[(Silmaril.Crypto.sha256 gzipManifest, gzipManifest), (configDigest, config), (layerDigest, layer)]⟩

/-- A layer whose only entry is a symbolic link, with a manifest naming it, each stored under its
own digest. -/
def symlinkLayer : List UInt8 :=
  (Silmaril.Formats.Tar.encode [{ name := "noop", typeflag := .symLink, linkname := "/bin/true" }]).getD []

/-- A layer with a whiteout entry. -/
def whiteoutLayer : List UInt8 :=
  (Silmaril.Formats.Tar.encode [{ name := ".wh.noop", mode := 420 }]).getD []

/-- A manifest of the profile for one layer. -/
def manifestFor (l : List UInt8) : List UInt8 := Fixtures.ascii (
  "{\"schemaVersion\":2,\"mediaType\":\"application/vnd.oci.image.manifest.v1+json\",\"config\":{\"mediaType\":\"application/vnd.oci.image.config.v1+json\",\"digest\":\"sha256:d77f6e9c553c0f0a3c2370fc870c57f500b2a0769f056a757365959928ca0260\",\"size\":185},\"layers\":[{\"mediaType\":\"application/vnd.oci.image.layer.v1.tar\",\"digest\":\"sha256:" ++
  String.join ((Silmaril.Crypto.sha256 l).map fun b =>
    String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)]) ++
  "\",\"size\":" ++ toString l.length ++ "}]}")

/-- A layout of the profile around one layer. -/
def layoutFor (l : List UInt8) : Oci.Layout :=
  ⟨[(Silmaril.Crypto.sha256 (manifestFor l), manifestFor l), (configDigest, config),
    (Silmaril.Crypto.sha256 l, l)]⟩

end Silmaril.Containers.Noop
