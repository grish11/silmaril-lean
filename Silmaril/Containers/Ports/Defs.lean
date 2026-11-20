module

public import Silmaril.Containers.Lps.Defs
public import Silmaril.Process.LPS.Sys.SocketCore

/-!
# Published ports: a runtime model whose `bind` covers the image's declared ports

> **Experimental API.** Names and statements in `Silmaril.Containers` may change.

**Why an extension.** LPS models `bind` on `INADDR_ANY` only for port 0 (`bindSpec`): any other
port is `unmodeled`, because whether a fixed port can be bound depends on the rest of the host.
A container runtime that publishes the image's declared ports gives the process exactly that
knowledge.

* `publish ports`: LPS's native x86-64 table, except that a `bind` of `INADDR_ANY` to a port in
  `ports` is LPS's own `bindSpec` with the port read as 0: the outcomes LPS gives port 0 (the
  injected `EADDRINUSE`, or the socket is bound). Nothing else changes; `Thms.publish_nil`:
  `publish []` is LPS's table.
* `ociRuntime pol`: read the OCI image, load its entry point, and run it on the adapter over
  `publish (tcpPorts config)`, the TCP ports **the image's configuration declares**, under the
  clone policy `pol`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Ports

open Silmaril.Containers Silmaril.Containers.Mach
open Silmaril.Process.LPS Silmaril.Process.LPS.Sys

/-- The port octets of the `struct sockaddr_in` at `addrp` (`sin_port`, offsets 2 and 3) read as
0, where they are readable; every other octet as it is. -/
def zeroPort (i : SyscallInput) (addrp : Word) : SyscallInput :=
  { i with mem := fun a => if a = addrp + 2 ∨ a = addrp + 3 then (i.mem a).map fun _ => 0 else i.mem a }

/-- **A bind to a published port**: system call 49 (`bind`) off the boundary guard, on an
`AF_INET` address `INADDR_ANY` whose port is non-zero and in `ports`. -/
def publishedBind (ports : List Nat) (i : SyscallInput) : Bool :=
  i.sysno.toNat == 49 && !NativeX86.All.boundarySuspect 49 i &&
    match readBytesMap i.mem (i.arg 1) (zw (sint32 (i.arg 2))) with
    | some bs => saFamilyOf bs == AF_INET && sinAddrOf bs == INADDR_ANY &&
        decide (0 < sinPortOf bs) && decide ((sinPortOf bs).toNat ∈ ports)
    | none => false

/-- **The native x86-64 table with published TCP ports**: a bind to a published port is LPS's
`bindSpec` on the same input with the port read as 0, so it has exactly the outcomes LPS gives
`bind` to port 0 (the injected `EADDRINUSE`, or the socket is bound); every other call, including
every other `bind`, is LPS's table `Probes.spec`. -/
def publish (ports : List Nat) : Sys SyscallEffect := fun i m o =>
  if publishedBind ports i = true then
    bindSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (zeroPort i (i.arg 1)) m o
  else Probes.spec i m o

/-- The outcome of a call that returns the error `e` and leaves the model `m`. -/
def errOut (e : Int) (m : Silmaril.Process.LPS.Model) : Silmaril.Process.LPS.Outcome SyscallEffect :=
  .ok (mkEffect (errnoRet e) [] []) m []

/-- The octets a `read` of 1024 from a connection's stream `rx` may deliver: a non-empty prefix of
the stream, at most 1024 octets. -/
def ReadOk (rx : Silmaril.Process.LPS.NetStream) (bs : List Silmaril.Process.LPS.Byte) : Prop :=
  1 ≤ bs.length ∧ bs.length ≤ 1024 ∧ (rx.take bs.length).1 = bs

/-- The TCP ports a configuration declares. -/
def tcpPorts (cfg : Config) : List Nat :=
  cfg.exposed.filterMap fun p => if p.proto = .tcp then some p.port.toNat else none

/-- **The runtime model that publishes declared ports**: the OCI reader, the entry-point shape
and LPS's loader; then the adapter over `publish (tcpPorts config)` under the clone policy `pol`. -/
def ociRuntime (pol : ClonePolicy := seqPolicy) :
    Runtime (Oci.Layout × Oci.Digest) (Silmaril.Process.LPS.Machines.X86Launch.Snapshot × List Nat) Ev where
  load i := (Oci.load i.1 i.2).bind fun f =>
    (Lps.runtime.load f).map fun snap => (snap, tcpPorts f.config)
  sem p := (Lps.lpsWith (publish p.2)).runsWith pol p.1
  obs := Eq

end Silmaril.Containers.Ports
