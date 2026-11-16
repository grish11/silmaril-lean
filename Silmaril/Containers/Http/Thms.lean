module

public import Silmaril.Containers.Http.Defs
public import Silmaril.Containers.Fixtures.Thms
import Silmaril.Proofs.Containers.Http.Basic

/-!
# Containers as HTTP servers: theorems

PROVED (standard axioms). Longer proofs are in `Silmaril.Proofs.Containers.Http`.

**Versions, transports and profiles.**

* `HttpVersion.http1_valid`: the HTTP/1 versions are valid `HTTP-version`s of
  `Silmaril.Net.Http1`;
* `Iface.admissible_mono`: admissibility is monotone in the profile;
* `Iface.h3_not_admissible_tcpOnly`, `Iface.admissible_tcpOnly`: HTTP/3 is not admissible
  under TCP-only; every TCP version is;
* `Iface.h3_admissible_udpOnly`: HTTP/3 is admissible under UDP-only;
* `Iface.not_admissible_vsockOnly`: no HTTP interface over IP is admissible under vsock-only.

**The HTTP fixture** (relative to the small runtime model).

* `httpIface_valid`, `httpIface_declared`, `httpIface_admissible`: HTTP/1.1 on 8080/tcp is
  valid, declared by the image and admissible under TCP-only;
* `okResponse_parses`: its response octets parse, by the verified HTTP/1.1 head parser, to a
  head with version `HTTP/1.1` and status 200 (`okHead`), followed by the content `ok`;
* `http_sent`: on every connection of every socket trace of its server platform, the octets
  sent are copies of that response.

**Platforms.** `platform_view_iff_linux`: the server platform of a runtime model is the Linux
process platform of `Silmaril.Servers` at the socket semantics it defines, so the core
model, satisfaction and refinement of `Silmaril.Servers.Platform` apply unchanged.
-/

public section

namespace Silmaril.Containers.Http

open Silmaril.Containers Silmaril.Containers.Fixtures Silmaril.Servers

theorem HttpVersion.http1_valid (v : HttpVersion) (w : Silmaril.Net.Http1.Version)
    (h : v.http1 = some w) : w.Valid := by
  cases v <;> cases h <;> decide

namespace Iface

theorem admissible_mono {P Q : Profile} (hPQ : P.Le Q) {i : Iface} (h : i.Admissible P) :
    i.Admissible Q := h.imp (hPQ _) (hPQ _)

theorem h3_not_admissible_tcpOnly (p : PortSpec) : ¬ Iface.Admissible Profile.tcpOnly ⟨.h3, p⟩ := by
  rintro (h | h) <;> cases h

theorem admissible_tcpOnly {v : HttpVersion} (hv : v.proto = .tcp) (p : PortSpec) :
    Iface.Admissible Profile.tcpOnly ⟨v, p⟩ := by
  left; simp [hv, Proto.sockType, Profile.tcpOnly]

theorem h3_admissible_udpOnly (p : PortSpec) : Iface.Admissible Profile.udpOnly ⟨.h3, p⟩ :=
  .inl rfl

theorem not_admissible_vsockOnly (i : Iface) : ¬ i.Admissible Profile.vsockOnly := by
  rintro (h | h) <;> cases h

end Iface

theorem httpIface_valid : Fixtures.httpIface.Valid := ⟨by decide, rfl⟩

theorem httpIface_declared : Fixtures.httpIface.Declared http.config := List.mem_singleton_self _

theorem httpIface_admissible : Fixtures.httpIface.Admissible Profile.tcpOnly :=
  Iface.admissible_tcpOnly rfl _

theorem okHead_version : Fixtures.okHead.line.version = .http11 ∧ Fixtures.okHead.line.code = 200 :=
  ⟨rfl, rfl⟩

theorem okResponse_parses :
    Silmaril.Net.Http1.parseResponseHead ⟨okResponse.toArray⟩ =
      .ok Fixtures.okHead (Silmaril.Net.Http1.encResponseHead Fixtures.okHead).length :=
  Silmaril.Proofs.Containers.Http.okResponse_parses

theorem http_sent (fr : Platform.Framing) {tr : List Platform.SockEv}
    (h : (platform small fr).runs http tr) (c : Platform.ConnId) :
    ∃ n, Platform.sent c tr = (List.replicate n okResponse).flatten :=
  Silmaril.Proofs.Containers.Http.http_sent fr h c

theorem platform_view_iff_linux {I P : Type} (R : Runtime I P Ev) (fr : Platform.Framing)
    (i : I) (inp : Silmaril.Cli.Input) (t : List Platform.ConnId × Platform.ConnLog) :
    (platform R fr).view i t ↔ (Platform.linux fr).view (fun _ tr => (platform R fr).runs i tr, inp) t :=
  Iff.rfl

end Silmaril.Containers.Http
