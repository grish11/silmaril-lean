module

public import Silmaril.Containers.Fixtures.Defs
public import Silmaril.Servers.Platform.Defs
public import Silmaril.Net.Http1.Message.Defs

/-!
# Containers as HTTP servers: interfaces, profiles and the server platform

**Experimental API** (`docs/projects/containers.md`): definitions and statements may change.

This module connects container runtime models to the server semantics of `Silmaril.Servers`
and the HTTP syntax of `Silmaril.Net.Http1`.

**HTTP interfaces.** An HTTP interface (`Iface`) is a protocol version and the port it is served
on. It is **valid** (`Iface.Valid`) when the port is not 0 and its transport is the version's:
HTTP/1.0, HTTP/1.1 and HTTP/2 run over TCP, HTTP/3 over QUIC, so UDP (RFC 9114 §3).
It is **declared** by a configuration (`Iface.Declared`) when the configuration exposes that
port, and **admissible** under a profile (`Iface.Admissible`) when the profile allows IP sockets
of the transport's type. So an HTTP/3 server is not admissible under `tcpOnly`, and no HTTP
interface over IP is admissible under `vsockOnly`: an HTTP service inside a Nitro Enclave needs
a proxy on the parent side, which is part of the deployment, not of the image.

HTTP/1 versions are those of `Silmaril.Net.Http1` (`HttpVersion.http1`); the HTTP/2 and HTTP/3
framings are not connected here.

**The server platform of a runtime model.** `platform R fr` reads the runs of images under a
runtime model `R` as a `Silmaril.Servers.Platform`: its observations are the TCP socket events
of the runs' finite prefixes (`sockTrace`), read per connection through an HTTP/1.1 framing
`fr` exactly as `Platform.linux fr` reads a Linux process. Through it, every notion of the
server institution (satisfaction of trace sentences, refinement across platforms, the
per-connection core model `Platform.connModel`) applies to containers under any runtime model.
Only finite prefixes are observed, so these are safety (partial-correctness) statements.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Http

open Silmaril.Containers Silmaril.Servers

/-- HTTP protocol versions. -/
inductive HttpVersion where
  | h1_0
  | h1_1
  | h2
  | h3
  deriving DecidableEq, Repr

/-- The transport a version runs over (HTTP/3: QUIC, over UDP). -/
def HttpVersion.proto : HttpVersion → Proto
  | .h3 => .udp
  | _ => .tcp

/-- The `HTTP-version` of the HTTP/1 versions (RFC 9112 §2.3). -/
def HttpVersion.http1 : HttpVersion → Option Silmaril.Net.Http1.Version
  | .h1_0 => some ⟨1, 0⟩
  | .h1_1 => some .http11
  | _ => none

/-- **An HTTP interface**: a version served on a port. -/
structure Iface where
  version : HttpVersion
  port : PortSpec
  deriving DecidableEq, Repr

/-- **A valid interface**: a real port, with the version's transport. -/
def Iface.Valid (i : Iface) : Prop := i.port.Valid ∧ i.port.proto = i.version.proto

/-- The configuration declares the interface's port. -/
def Iface.Declared (cfg : Config) (i : Iface) : Prop := i.port ∈ cfg.exposed

/-- **Admissible under a profile**: the profile allows IP sockets of the transport's type. -/
def Iface.Admissible (P : Profile) (i : Iface) : Prop :=
  P (.sock .inet4 i.version.proto.sockType) = true ∨
    P (.sock .inet6 i.version.proto.sockType) = true

/-- **The TCP socket event of an event**, for the server platforms of `Silmaril.Servers`
(connections are named by their descriptors). -/
def toSockEv : Ev → Option Platform.SockEv
  | .accept s c => if s.isTcp then some (.accept c.fd) else none
  | .recv s bs => if s.isTcp then some (.recv s.fd bs) else none
  | .send s bs => if s.isTcp then some (.send s.fd bs) else none
  | .close s => if s.isTcp then some (.close s.fd) else none
  | _ => none

/-- The TCP socket events of a trace. -/
def sockTrace (t : List Ev) : List Platform.SockEv := t.filterMap toSockEv

/-- **The server platform of a runtime model**: images, observed through the TCP socket events of
finite prefixes of their runs, read per connection by an HTTP/1.1 framing. -/
def platform {I P : Type} (R : Runtime I P Ev) (fr : Platform.Framing) :
    Platform (List Platform.ConnId × Platform.ConnLog) where
  Impl := I
  Obs := List Platform.SockEv
  runs i tr := ∃ b u, R.beh i b ∧ b.Prefix u ∧ tr = sockTrace u
  reads tr t := t = (Platform.accepted tr, Platform.connLog fr tr)

/-! ## The HTTP fixture's interface and response -/

/-- The interface of the HTTP fixture: HTTP/1.1 on 8080/tcp. -/
def Fixtures.httpIface : Iface := ⟨.h1_1, ⟨.tcp, Fixtures.httpPort⟩⟩

/-- The head of the fixture's response, in the syntax of `Silmaril.Net.Http1`. -/
def Fixtures.okHead : Silmaril.Net.Http1.ResponseHead :=
  ⟨⟨.http11, 200, Fixtures.ascii "OK"⟩, [⟨Fixtures.ascii "Content-Length", Fixtures.ascii "2"⟩]⟩

end Silmaril.Containers.Http
