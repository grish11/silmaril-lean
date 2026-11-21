module

public import Silmaril.Containers.Image.Defs

/-!
# Environment interaction: events, capabilities and restricted profiles

**Experimental API** (`docs/projects/containers.md`): definitions and statements may change.

What a containerised process does to its environment is a sequence of **events** (`Ev`):
socket operations, file reads and writes, standard streams, the clock and randomness, and
starting other programs. Each socket event carries the socket it acts on (`Sock`: descriptor,
address family and type), so whether an event is allowed can be read off the event alone.

Every event has a **capability** (`Ev.cap`), the kind of access it needs, and a **profile**
(`Profile`) is a set of capabilities. Named profiles:

| Profile | Capabilities | Typical use |
| --- | --- | --- |
| `Profile.none` | nothing | pure computation reporting only an exit status |
| `Profile.stdio` | standard streams | batch jobs |
| `Profile.vsockOnly` | `AF_VSOCK` sockets | the enclave side of AWS Nitro Enclaves, whose only channel to its parent is vsock |
| `Profile.tcpOnly` | IPv4 and IPv6 stream sockets | an HTTP/1.1 or HTTP/2 server |
| `Profile.udpOnly` | IPv4 and IPv6 datagram sockets | DNS, QUIC and HTTP/3 |
| `Profile.networkOnly` | TCP and UDP | network services without local IPC |
| `Profile.networkUnix` | TCP, UDP and Unix-domain sockets | a service with a local control socket |
| `Profile.readOnlyFs` | file reads | combined with the above |

Profiles are ordered by inclusion (`Profile.Le`) and combined by union (`Profile.sup`).
`Confined P t` says every event of the trace `t` has a capability in `P`.

**Two readings of a profile.** A profile can be *proved of a program* (its semantics only
produces confined traces) or *enforced by a runtime* (seccomp filters, network namespaces, a
VM with only a vsock device): a runtime that enforces `P` stops the process at the first
event outside `P` (`Silmaril.Containers.Runtime.enforce`). The two agree exactly on programs
that are confined (`Runtime.Thms.enforce_eq_of_confined`). A profile is a statement about which
channels are used; it is not information-flow control: a program confined to `tcpOnly` can
still leak a secret over TCP (see `Behaviour.Noninterference`).

**Inputs and outputs.** `Ev.isInput` marks the events whose payload the environment chooses
(received octets, accepted connections, file contents read, the clock, randomness). This is what
separates environmental nondeterminism from the program's own (`Behaviour.DetUpToInputs`).

**Not Nitro by itself.** `vsockOnly` describes the channels of a process inside an enclave. An
AWS Nitro Enclave is also a separate VM booted from an enclave image file (EIF), measured into
PCRs and attested; those obligations belong to the runtime model, not to the profile
(docs/projects/containers.md, "Nitro Enclaves").

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers

/-- Socket address families. -/
inductive Family where
  | inet4
  | inet6
  | unix
  | vsock
  deriving DecidableEq, Repr

/-- Socket types. -/
inductive SockType where
  /-- `SOCK_STREAM`: TCP for the IP families. -/
  | stream
  /-- `SOCK_DGRAM`: UDP for the IP families. -/
  | dgram
  /-- `SOCK_SEQPACKET`. -/
  | seqpacket
  deriving DecidableEq, Repr

/-- A vsock address: a context identifier and a port (`struct sockaddr_vm`). -/
structure VsockAddr where
  cid : UInt32
  port : UInt32
  deriving DecidableEq, Repr

/-- `VMADDR_CID_ANY`: bind to whatever context identifier this VM has. -/
def VsockAddr.cidAny : UInt32 := 0xFFFFFFFF

/-- Socket addresses. -/
inductive Addr where
  | inet (a : Silmaril.Net.Ip.SockAddr)
  | unix (path : Path)
  | vsock (a : VsockAddr)
  deriving DecidableEq, Repr

/-- A socket as the events see it: its descriptor, family and type. -/
structure Sock where
  fd : Nat
  family : Family
  type : SockType
  deriving DecidableEq, Repr

/-- A TCP socket: an IP family, stream type. -/
def Sock.isTcp (s : Sock) : Bool :=
  s.type == .stream && (s.family == .inet4 || s.family == .inet6)

/-- The socket type of a transport. -/
def Proto.sockType : Proto → SockType
  | .tcp => .stream
  | .udp => .dgram

/-- **An event** between a process and its environment. -/
inductive Ev where
  /-- A socket was created. -/
  | socket (s : Sock)
  /-- A socket was bound to an address. -/
  | bind (s : Sock) (a : Addr)
  /-- A socket started listening. -/
  | listen (s : Sock)
  /-- A connection was accepted on a listening socket, as the socket `c`. -/
  | accept (s : Sock) (c : Sock)
  /-- A socket was connected to an address. -/
  | connect (s : Sock) (a : Addr)
  /-- Octets were sent. -/
  | send (s : Sock) (bs : List UInt8)
  /-- Octets were received. -/
  | recv (s : Sock) (bs : List UInt8)
  /-- A socket was closed. -/
  | close (s : Sock)
  /-- A file was read. -/
  | read (p : Path) (bs : List UInt8)
  /-- A file was written. -/
  | write (p : Path) (bs : List UInt8)
  /-- Octets from standard input. -/
  | stdin (bs : List UInt8)
  /-- Octets to standard output. -/
  | stdout (bs : List UInt8)
  /-- Octets to standard error. -/
  | stderr (bs : List UInt8)
  /-- The clock was read. -/
  | clock (t : Nat)
  /-- Random octets were obtained. -/
  | random (bs : List UInt8)
  /-- Another program was started. -/
  | spawn (p : Path)
  deriving DecidableEq, Repr

/-- **Capabilities**: the kinds of access an event needs. -/
inductive Cap where
  | sock (f : Family) (t : SockType)
  | fsRead
  | fsWrite
  | stdio
  | clock
  | random
  | spawn
  deriving DecidableEq, Repr

/-- The capability an event needs. -/
def Ev.cap : Ev → Cap
  | .socket s | .bind s _ | .listen s | .accept s _ | .connect s _ | .send s _ | .recv s _
  | .close s => .sock s.family s.type
  | .read .. => .fsRead
  | .write .. => .fsWrite
  | .stdin _ | .stdout _ | .stderr _ => .stdio
  | .clock _ => .clock
  | .random _ => .random
  | .spawn _ => .spawn

/-- The events whose payload the environment chooses. -/
def Ev.isInput : Ev → Bool
  | .accept .. | .recv .. | .read .. | .stdin _ | .clock _ | .random _ => true
  | _ => false

/-- **A profile**: the capabilities a process may use. -/
abbrev Profile : Type := Cap → Bool

namespace Profile

/-- `P ≤ Q`: everything `P` allows, `Q` allows. -/
def Le (P Q : Profile) : Prop := ∀ c, P c = true → Q c = true

/-- The union of two profiles. -/
def sup (P Q : Profile) : Profile := fun c => P c || Q c

/-- No capability. -/
def none : Profile := fun _ => false

/-- Standard streams only. -/
def stdio : Profile
  | .stdio => true
  | _ => false

/-- **vsock sockets only.** -/
def vsockOnly : Profile
  | .sock .vsock _ => true
  | _ => false

/-- **TCP only**: stream sockets of either IP family. -/
def tcpOnly : Profile
  | .sock .inet4 .stream | .sock .inet6 .stream => true
  | _ => false

/-- **UDP only**: datagram sockets of either IP family. -/
def udpOnly : Profile
  | .sock .inet4 .dgram | .sock .inet6 .dgram => true
  | _ => false

/-- **Network only**: TCP and UDP. -/
def networkOnly : Profile := tcpOnly.sup udpOnly

/-- Unix-domain sockets of any type. -/
def unixSockets : Profile
  | .sock .unix _ => true
  | _ => false

/-- **Network and Unix-domain sockets.** -/
def networkUnix : Profile := networkOnly.sup unixSockets

/-- File reads only. -/
def readOnlyFs : Profile
  | .fsRead => true
  | _ => false

end Profile

/-- **Confinement**: every event of the trace is allowed by the profile. -/
def Confined (P : Profile) (t : List Ev) : Prop := ∀ e ∈ t, P e.cap = true

/-- The ports a trace binds IP sockets to. -/
def boundPorts : List Ev → List Silmaril.Net.Ip.Port
  | [] => []
  | .bind _ (.inet a) :: t => a.port :: boundPorts t
  | _ :: t => boundPorts t

/-- **Binds only declared ports**: every IP bind is to a valid port the configuration declares
for the socket's transport (`Config.exposed`). -/
def BindsDeclared (cfg : Config) (t : List Ev) : Prop :=
  ∀ s a, Ev.bind s (.inet a) ∈ t →
    ∃ q ∈ cfg.exposed, q.Valid ∧ q.port = a.port ∧
      (s.type = .stream ∧ q.proto = .tcp ∨ s.type = .dgram ∧ q.proto = .udp)

end Silmaril.Containers
