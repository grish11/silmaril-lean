module

public import Silmaril.Containers.Ports.Defs
import Silmaril.Proofs.Containers.Ports.Basic
import Silmaril.Proofs.Containers.Ports.Socket
public import Silmaril.Process.LPS.Sys.Socket
public import Silmaril.Process.LPS.Probes.Kit
public import Silmaril.Process.LPS.Probes.KitMemory

/-!
# Published ports: theorems

> **Experimental API.** Names and statements in `Silmaril.Containers` may change.

PROVED (standard axioms). `publish_nil`: with no published port the table is LPS's native table,
so the extension leaves the base model unchanged. `publish_of_not`: off a bind to a published
port it is LPS's table. `publish_of_published`: on one, it is LPS's `bindSpec` with the port read
as 0.

**The socket calls of a one-connection server**, LPS's own outcomes (not the extension's):
`socket_iff` (`socket(AF_INET, SOCK_STREAM, 0)`: an injected `ENOMEM`/`EMFILE`/`ENFILE`, or the
lowest free descriptor, a fresh socket), `listen_iff` (on a bound socket: 0, listening),
`accept_iff` (on a listening socket, no address, flags 0: an injected error, or the lowest free
descriptor, connected to the head of the launch's connection queue on channel `3 + connIx`),
`sendto_goes_iff` (`MSG_NOSIGNAL`, no address, on a connection with no pending error: any
non-empty prefix of the source, one `writeEv` per octet, the model unchanged), `sendto_err_iff`
(with a pending reset or timeout: that error, the socket left reset). `dispatches_*`: the native
x86-64 table dispatches 41, 50, 43, 44 to these arms.
-/

public section

namespace Silmaril.Containers.Ports

open Silmaril.Process.LPS

abbrev PModel := Silmaril.Process.LPS.Model
abbrev POutcome := Silmaril.Process.LPS.Outcome SyscallEffect

theorem publish_nil : publish [] = Probes.spec := Silmaril.Proofs.Containers.Ports.publish_nil

theorem publish_of_not {ports : List Nat} {i : SyscallInput} (h : publishedBind ports i = false)
    (m : PModel) (o : POutcome) : publish ports i m o ↔ Probes.spec i m o :=
  Silmaril.Proofs.Containers.Ports.publish_of_not h m o

theorem publish_of_published {ports : List Nat} {i : SyscallInput} (h : publishedBind ports i = true)
    (m : PModel) (o : POutcome) :
    publish ports i m o ↔ bindSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (zeroPort i (i.arg 1)) m o :=
  Silmaril.Proofs.Containers.Ports.publish_of_published h m o

theorem socket_iff (i : SyscallInput) (m : PModel) (o : POutcome) :
    socketSpec 2 1 0 i m o ↔
      (∃ e ∈ socketErrnos, o = errOut e m) ∨
      (fdLookup m.fds (allocFd m.fds) = none ∧
        o = .ok (mkEffect (allocFd m.fds) [] []) (m.withFds (fdInsert m.fds (allocFd m.fds) (.socket .fresh))) []) :=
  Silmaril.Proofs.Containers.Ports.socket_iff i m o

theorem listen_iff (fd b : Word) (i : SyscallInput) (m : PModel) (o : POutcome)
    (hfd : fdLookup m.fds fd = some (.socket .bound)) :
    listenSpec fd b i m o ↔
      o = .ok (mkEffect 0 [] []) (m.withFds (fdInsert m.fds fd (.socket .listening))) [] :=
  Silmaril.Proofs.Containers.Ports.listen_iff fd b i m o hfd

theorem accept_iff (fd : Word) (i : SyscallInput) (m : PModel) (o : POutcome)
    (hfd : fdLookup m.fds fd = some (.socket .listening)) (hex : connIxExhausted m.connIx = false) :
    accept4Spec fd 0 0 0 i m o ↔
      (∃ e ∈ acceptErrnos, o = errOut e m) ∨
      (fdLookup m.fds (allocFd m.fds) = none ∧
        o = .ok (mkEffect (allocFd m.fds) [] [])
          (m.withAccepted (fdInsert m.fds (allocFd m.fds)
            (.socket (.connected (nqPeer m.net) (connChannel m.connIx) (nqScript m.net))))) []) :=
  Silmaril.Proofs.Containers.Ports.accept_iff fd i m o hfd hex

/-- `sendto(fd, buf, count, MSG_NOSIGNAL, NULL, 0)` on a connection whose stream has no pending
error, with a readable source: any non-empty prefix of the source is sent. -/
theorem sendto_goes_iff (fd buf count : Word) (i : SyscallInput) (m : PModel) (o : POutcome)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {bs : List Byte}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hs : sendState (.connected peer ch rx) = .goes ch)
    (hc : modeledRwCount count = true) (hz : wIs0 count = false)
    (ha : accessOkbX86 buf (uns count) = true)
    (hb : readableBytes i.mem buf count = bs) (hne : bs ≠ []) :
    sendtoSpecX86 fd buf count 0x4000 0 0 i m o ↔
      ∃ ds : List Byte, (1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ uns count ∧ ds = bs.take ds.length) ∧
        o = .ok ((mkEffect (lenWord ds) [] []).withCopyins [(buf, ds.length)]) m (ds.map (.writeEv ch)) :=
  Silmaril.Proofs.Containers.Ports.sendto_goes_iff fd buf count i m o hfd hs hc hz ha hb hne

/-- The same call with a pending reset or timeout `e`: the error, the socket left reset. -/
theorem sendto_err_iff (fd buf count : Word) (i : SyscallInput) (m : PModel) (o : POutcome)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {e : Int}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hs : sendState (.connected peer ch rx) = .err e peer ch)
    (hc : modeledRwCount count = true) (ha : accessOkbX86 buf (uns count) = true) :
    sendtoSpecX86 fd buf count 0x4000 0 0 i m o ↔
      o = .ok ((mkEffect (errnoRet e) [] []).withCopyins [])
        (m.withFds (fdInsert m.fds fd (.socket (.reset peer ch)))) [] :=
  Silmaril.Proofs.Containers.Ports.sendto_err_iff fd buf count i m o hfd hs hc ha

theorem dispatches_socket :
    Probes.Dispatches 41 (fun i => socketSpec (i.arg 0) (i.arg 1) (i.arg 2)) :=
  Silmaril.Proofs.Containers.Ports.dispatches_socket

theorem dispatches_listen :
    Probes.Dispatches 50 (fun i => listenSpec (fd32 (i.arg 0)) (i.arg 1)) :=
  Silmaril.Proofs.Containers.Ports.dispatches_listen

theorem dispatches_accept :
    Probes.Dispatches 43 (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) 0) :=
  Silmaril.Proofs.Containers.Ports.dispatches_accept

theorem dispatches_sendto :
    Probes.Dispatches 44 (fun i => sendtoSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)) :=
  Silmaril.Proofs.Containers.Ports.dispatches_sendto

/-- `read(fd, buf, 1024)` on a connection whose stream has ended (`FIN`): 0, nothing changes. -/
theorem read_fin_iff (fd buf : Word) (i : SyscallInput) (m : PModel) (o : POutcome)
    {peer : PeerAddr} {ch : Word} {rx : NetStream}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hi : rx.item 0 = .inr .fin) (ha : accessOkbX86 buf 1024 = true) :
    readSpecX86 fd buf 1024 i m o ↔ o = .ok (mkEffect 0 [] []) m [] :=
  Silmaril.Proofs.Containers.Ports.read_fin_iff fd buf i m o hfd hi ha

/-- The same with a pending reset or timeout: that error, the socket left reset. -/
theorem read_err_iff (fd buf : Word) (i : SyscallInput) (m : PModel) (o : POutcome)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {e : NetEnd} {err : Int}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hi : rx.item 0 = .inr e) (he : (e = .rst ∧ err = ECONNRESET) ∨ (e = .timedOut ∧ err = ETIMEDOUT))
    (ha : accessOkbX86 buf 1024 = true) :
    readSpecX86 fd buf 1024 i m o ↔
      o = .ok (mkEffect (errnoRet err) [] []) (m.withFds (fdInsert m.fds fd (.socket (.reset peer ch)))) [] :=
  Silmaril.Proofs.Containers.Ports.read_err_iff fd buf i m o hfd hi he ha

/-- The same with data waiting, into a writable buffer: a non-empty prefix of the stream (at most
1024 octets), written to the buffer, one `readEv` per octet, the stream advanced. -/
theorem read_data_iff (fd buf : Word) (i : SyscallInput) (m : PModel) (o : POutcome)
    {peer : PeerAddr} {ch : Word} {rx : NetStream} {b : Byte}
    (hfd : fdLookup m.fds fd = some (.socket (.connected peer ch rx)))
    (hi : rx.item 0 = .inl b)
    (writable : ∀ k ≤ 1024, (readBytesAux i.wmem buf k).isSome = true) :
    readSpecX86 fd buf 1024 i m o ↔ ∃ bs, ReadOk rx bs ∧
      o = .ok (mkEffect (lenWord bs) [(buf, bs)] [])
        (m.withFds (fdInsert m.fds fd (.socket (.connected peer ch (rx.take bs.length).2))))
        (bs.map (.readEv ch)) :=
  Silmaril.Proofs.Containers.Ports.read_data_iff fd buf i m o hfd hi writable

set_option maxRecDepth 100000 in
theorem dispatches_read :
    Probes.Dispatches 0 (fun i => readSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)) :=
  Probes.dispatches_read

end Silmaril.Containers.Ports
