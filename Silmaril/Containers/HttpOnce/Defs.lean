module

public import Silmaril.Containers.Lps.Defs
public import Silmaril.Containers.Http.Defs
public import Silmaril.Net.Http1.Framing.Defs

/-!
# A real HTTP responder: a static ELF that writes one HTTP/1.1 response

> **Experimental API.** Names and statements in `Silmaril.Containers` may change.

**The program** (`examples/containers/http-once/http_ok.s`, 408 octets, SHA-256
`ac076e37…51d1`): `write(1, response, 40); exit(0)`, where `response` is the 40 octets
`HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok` (`Fixtures.okResponse`, the response of the
model fixture `Fixtures.http`) stored after the code in the one `PT_LOAD`. It ignores the value
`write` returns. Built by the LPS probe build
(`examples/verification-projects/theorem-dev/lps-probes/build.sh`: GNU as and ld, static, no libc, no build-id, stripped, one R+X `PT_LOAD` at `0x400000`).

It speaks HTTP the way an `inetd`-style service does: on standard output, which a socket-activating
supervisor connects to an accepted TCP connection. Its image declares `8080/tcp`
(`config.ExposedPorts`). The listening socket is **not** part of the image and not part of any
theorem here: `examples/containers/http-once/docker-test.sh` serves port 8080 with a small
host-side accept loop that runs one container per connection.

**The image**, deterministic, `FROM scratch`: one uncompressed layer with the regular file
`http-ok` (mode `0755`, owner 0, time 0), a configuration with `Entrypoint ["/http-ok"]` and
`ExposedPorts {"8080/tcp":{}}`, and a manifest; `examples/containers/http-once/layout/` holds the
same blobs (`Generate.lean`).

**The specification** (`respondsOk`): the run exits 0 and its events are standard-output octets
forming a prefix of the response. A prefix, not the response: LPS lets `write` deliver any
non-empty prefix (a short write), and this program does not retry. The full response is the one
the reference run delivers (`Thms.full_run`), and it is judged exactly by the verified HTTP/1.1
reader: `parseResponse` reads the whole 40 octets as the head `Http.Fixtures.okHead` (version
HTTP/1.1, status 200) and the content `ok`, consuming every octet (`IsOkResponse`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.HttpOnce

open Silmaril.Containers Silmaril.Formats
open Silmaril.Process.LPS Silmaril.Process.LPS.Probes

/-- The complete ELF file of `http_ok.s`. -/
def fileBytes : List Byte := [
    0x7f, 0x45, 0x4c, 0x46, 0x02, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x02, 0x00, 0x3e, 0x00, 0x01, 0x00, 0x00, 0x00, 0x78, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x38, 0x00, 0x01, 0x00, 0x40, 0x00, 0x03, 0x00, 0x02, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xc2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00,
    0x00, 0x00, 0xbe, 0x9a, 0x00, 0x40, 0x00, 0xba, 0x28, 0x00, 0x00, 0x00, 0x0f, 0x05, 0xb8, 0x3c,
    0x00, 0x00, 0x00, 0xbf, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x05, 0x48, 0x54, 0x54, 0x50, 0x2f, 0x31,
    0x2e, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4f, 0x4b, 0x0d, 0x0a, 0x43, 0x6f, 0x6e, 0x74, 0x65,
    0x6e, 0x74, 0x2d, 0x4c, 0x65, 0x6e, 0x67, 0x74, 0x68, 0x3a, 0x20, 0x32, 0x0d, 0x0a, 0x0d, 0x0a,
    0x6f, 0x6b, 0x00, 0x2e, 0x73, 0x68, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0x00, 0x2e, 0x74, 0x65,
    0x78, 0x74, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0b, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x78, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xc2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- **The program as a probe of the LPS kit**: the ELF and its one program header. -/
def probe : Probe where
  fileBytes := fileBytes
  header := ⟨0, 0, 2, 62, 1, 4194424, 64, 216, 0, 64, 56, 1, 64, 3, 2⟩
  programHeader := ⟨1, 5, 0, 4194304, 4194304, 194, 194, 4096⟩

/-- **The pinned ELF**, as octets. -/
def elf : List UInt8 := fileBytes.map UInt8.ofBitVec

/-! ## The specification -/

/-- Standard-output events, one per octet (how the LPS adapter reports a write on channel 1). -/
def outEvs (bs : List UInt8) : List Ev := bs.map fun b => .stdout [b]

/-- **The postcondition**: exit status 0, and the events are standard-output octets forming a
prefix of `Fixtures.okResponse`. -/
def respondsOk (t : List Ev) (c : UInt8) : Prop :=
  c = 0 ∧ ∃ bs, bs <+: Fixtures.okResponse ∧ t = outEvs bs

/-- **The exact HTTP judgment** on octets: the verified HTTP/1.1 reader, for a response to `GET`,
reads them as the head `Http.Fixtures.okHead` with the content `ok`, consuming all of them. -/
def IsOkResponse (bs : List UInt8) : Prop :=
  Silmaril.Net.Http1.parseResponse (Fixtures.ascii "GET") ⟨bs.toArray⟩ =
    .ok (Http.Fixtures.okHead, .content (Fixtures.ascii "ok")) bs.length

/-! ## The image -/

/-- The layer's only entry. -/
def entry : Tar.Entry := { name := "http-ok", mode := 493, data := elf }

/-- **The layer**: the tar archive of `entry`. -/
def layer : List UInt8 := (Tar.encode [entry]).getD []

def layerDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:a97c6a7d6320f73a7c3d34f17546070a24be9a33f9d62d64f40358ace9ec4280").getD []

/-- **The configuration**: entry point `/http-ok`, declared port `8080/tcp`. -/
def configText : String :=
  "{\"architecture\":\"amd64\",\"os\":\"linux\",\"config\":{\"Entrypoint\":[\"/http-ok\"],\"ExposedPorts\":{\"8080/tcp\":{}}},\"rootfs\":{\"type\":\"layers\",\"diff_ids\":[\"sha256:a97c6a7d6320f73a7c3d34f17546070a24be9a33f9d62d64f40358ace9ec4280\"]}}"

def config : List UInt8 := Fixtures.ascii configText

def configDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:bec586dacb76754d9fd173bf89ff2ff17b8e43af5a8ce4f6c8b552cb5f7f5a1a").getD []

/-- **The manifest.** -/
def manifestText : String :=
  "{\"schemaVersion\":2,\"mediaType\":\"application/vnd.oci.image.manifest.v1+json\",\"config\":{\"mediaType\":\"application/vnd.oci.image.config.v1+json\",\"digest\":\"sha256:bec586dacb76754d9fd173bf89ff2ff17b8e43af5a8ce4f6c8b552cb5f7f5a1a\",\"size\":219},\"layers\":[{\"mediaType\":\"application/vnd.oci.image.layer.v1.tar\",\"digest\":\"sha256:a97c6a7d6320f73a7c3d34f17546070a24be9a33f9d62d64f40358ace9ec4280\",\"size\":2048}]}"

def manifest : List UInt8 := Fixtures.ascii manifestText

def manifestDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:a709755a1d1efe78a39205ba1832ac25f83de6fc41f732823d954b6e864f9ed5").getD []

/-- **The image layout's blobs.** -/
def layout : Oci.Layout := ⟨[(manifestDigest, manifest), (configDigest, config), (layerDigest, layer)]⟩

/-- **The image**: the layout and the digest of its manifest. -/
def image : Oci.Layout × Oci.Digest := (layout, manifestDigest)

/-- The declared port, as `Http.Fixtures.httpIface` serves HTTP/1.1 on it. -/
def port : PortSpec := ⟨.tcp, 8080⟩

def elfDigest : Oci.Digest :=
  (Oci.digestOf? "sha256:ac076e372af6ece5fce3a67e3d91c2099ae5f22d390c84145f2380fb3c5a51d1").getD []

end Silmaril.Containers.HttpOnce
