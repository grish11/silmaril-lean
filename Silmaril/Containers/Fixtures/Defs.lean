module

public import Silmaril.Containers.Precondition.Defs

/-!
# Fixtures: the smallest containers, under an explicit small runtime model

**Experimental API** (`docs/projects/containers.md`): definitions and statements may change.

**The model.** Programs are a tiny language (`Tiny`) whose semantics is given directly as sets
of runs (`Tiny.sem`), and image contents are such programs or data (`Blob`). The runtime model
`small` reads the executable file at the entry point (`Shape.entry`), refuses any image without
one, and adds nothing to the program's runs. Everything proved about the fixtures is relative
to this model: it says nothing about Docker, runc, a Linux kernel or an ELF file. Replacing
`Tiny.sem` by the Linux process semantics of an ELF executable (`Silmaril.Process`,
`Silmaril.Elf`) is the refinement step these fixtures are meant to be compared against
(docs/projects/containers.md).

**The fixtures** (each a flat image with the program at `/app`):

| Image | Program | Profile | What is proved |
| --- | --- | --- | --- |
| `noop` | exit 0 | `none` | total correctness: exits 0 with no events |
| `crash` | `SIGSEGV` at once | `none` | every partial-correctness spec, no total-correctness spec |
| `spin` | loops silently | `none` | the same; it trace-refines `noop` but does not refine it |
| `http` | HTTP/1.1 on TCP port 8080, one fixed response per connection | `tcpOnly` | confined, binds only its declared port, sends only the response, never stops under a live environment; under a vsock-only enforcing runtime it is killed before its first event |
| `nitro` | vsock port 5005: accept, read a request, answer `f` of it, exit 0 | `vsockOnly` | confined; totally correct when the environment is live; unchanged by a vsock-only enforcing runtime |

**Simplifications of the model.** A request arrives in one `recv` and a response leaves in one
`send` (no fragmentation, no partial writes); there is one connection at a time; socket
descriptors are fixed (3 for the listening socket, 4 for the connection); nothing fails
(no `EADDRINUSE`, no resets). Environment choices are the request octets and whether the
environment connects and sends at all (`blocked` runs).

**Executable checks.** `Tiny.run` computes the run a program has for a script of environment
inputs, and `Tiny.run_sound` proves that what it computes is a run of `Tiny.sem`. The checks in
`Silmaril.Containers.Fixtures.Examples` evaluate the loader and `Tiny.run` on these images:
they test this model, not any container runtime.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Fixtures

/-- The functions the vsock fixture can compute. -/
inductive Fn where
  | id
  | reverse
  | const (bs : List UInt8)
  deriving DecidableEq, Repr

/-- Apply a function. -/
def Fn.apply : Fn → List UInt8 → List UInt8
  | .id, x => x
  | .reverse, x => x.reverse
  | .const bs, _ => bs

/-- **Programs of the small model.** -/
inductive Tiny where
  /-- Exit with a status, with no events. -/
  | exit (code : UInt8)
  /-- Crash with a signal, with no events. -/
  | crash (sig : Nat)
  /-- Loop forever without events. -/
  | spin
  /-- Listen on TCP `port` (IPv4, any address); for each connection, read a request, send
  `resp`, close. -/
  | httpServe (port : Silmaril.Net.Ip.Port) (resp : List UInt8)
  /-- Listen on vsock `port`; accept one connection, read a request `x`, send `f x`, close,
  exit 0. -/
  | vsockCompute (port : UInt32) (f : Fn)
  deriving DecidableEq, Repr

/-- **Image contents**: a program or data. -/
inductive Blob where
  | prog (p : Tiny)
  | data (bs : List UInt8)
  deriving DecidableEq, Repr

/-! ## Sockets and traces -/

/-- The listening socket of a family. -/
def lsock (f : Family) : Sock := ⟨3, f, .stream⟩

/-- The connection socket of a family. -/
def csock (f : Family) : Sock := ⟨4, f, .stream⟩

/-- The IPv4 wildcard address at a port. -/
def anyV4 (port : Silmaril.Net.Ip.Port) : Addr := .inet (.v4 port ⟨0, 0, 0, 0⟩)

/-- The HTTP server's start: socket, bind, listen. -/
def httpSetup (port : Silmaril.Net.Ip.Port) : List Ev :=
  [.socket (lsock .inet4), .bind (lsock .inet4) (anyV4 port), .listen (lsock .inet4)]

/-- One HTTP connection: accept, receive the request, send the response, close. -/
def httpSession (resp req : List UInt8) : List Ev :=
  [.accept (lsock .inet4) (csock .inet4), .recv (csock .inet4) req, .send (csock .inet4) resp,
    .close (csock .inet4)]

/-- The events of the HTTP server after serving the requests `reqs`. -/
def httpTrace (port : Silmaril.Net.Ip.Port) (resp : List UInt8) (reqs : List (List UInt8)) :
    List Ev :=
  httpSetup port ++ (reqs.map (httpSession resp)).flatten

/-- The vsock fixture's start: socket, bind to any CID at `port`, listen. -/
def vsockSetup (port : UInt32) : List Ev :=
  [.socket (lsock .vsock), .bind (lsock .vsock) (.vsock ⟨VsockAddr.cidAny, port⟩),
    .listen (lsock .vsock)]

/-- The vsock fixture's whole run on the request `x`. -/
def vsockTrace (port : UInt32) (f : Fn) (x : List UInt8) : List Ev :=
  vsockSetup port ++ [.accept (lsock .vsock) (csock .vsock), .recv (csock .vsock) x,
    .send (csock .vsock) (f.apply x), .close (csock .vsock)]

/-- **The runs of the HTTP server.** -/
inductive HttpRun (port : Silmaril.Net.Ip.Port) (resp : List UInt8) : Beh Ev → Prop where
  /-- Waiting for a connection after serving `reqs`. -/
  | waitAccept (reqs) : HttpRun port resp (.blocked (httpTrace port resp reqs))
  /-- Waiting for a request on a connection after serving `reqs`. -/
  | waitRecv (reqs) : HttpRun port resp
      (.blocked (httpTrace port resp reqs ++ [.accept (lsock .inet4) (csock .inet4)]))
  /-- Serving forever: every prefix is a prefix of a finite run. -/
  | forever (f : Nat → Ev) (h : ∀ n, ∃ reqs, (List.range n).map f <+: httpTrace port resp reqs) :
      HttpRun port resp (.reactive f)

/-- **The runs of the vsock fixture.** -/
inductive VsockRun (port : UInt32) (f : Fn) : Beh Ev → Prop where
  | waitAccept : VsockRun port f (.blocked (vsockSetup port))
  | waitRecv : VsockRun port f
      (.blocked (vsockSetup port ++ [.accept (lsock .vsock) (csock .vsock)]))
  | done (x) : VsockRun port f (.done (vsockTrace port f x) (.exited 0))

/-- **The semantics of the small model.** -/
def Tiny.sem : ProcSem Tiny Ev
  | .exit c => (· = .done [] (.exited c))
  | .crash s => (· = .done [] (.signaled s))
  | .spin => (· = .spins [])
  | .httpServe port resp => HttpRun port resp
  | .vsockCompute port f => VsockRun port f

/-- **A run for a script of environment inputs**: the requests the environment sends, in
order; the run ends blocked when the script is exhausted. -/
def Tiny.run : Tiny → List (List UInt8) → Beh Ev
  | .exit c, _ => .done [] (.exited c)
  | .crash s, _ => .done [] (.signaled s)
  | .spin, _ => .spins []
  | .httpServe port resp, reqs => .blocked (httpTrace port resp reqs)
  | .vsockCompute port _, [] => .blocked (vsockSetup port)
  | .vsockCompute port f, x :: _ => .done (vsockTrace port f x) (.exited 0)

/-! ## The small runtime model and the images -/

/-- The program in a blob. -/
def Blob.prog? : Blob → Option Tiny
  | .prog p => some p
  | .data _ => none

/-- **The shape of the fixtures**: a program at the entry point. -/
def shape : Shape Blob Tiny := Shape.entry .static Blob.prog?

/-- **The small runtime model**: the entry-point shape and `Tiny.sem`, adding nothing. -/
def small : Runtime (Flat Blob) Tiny Ev := Runtime.ofShape shape Tiny.sem

/-- An image with the program `p` at `/app`, and the ports it declares. -/
def image (p : Tiny) (exposed : List PortSpec := []) : Flat Blob where
  config := { entrypoint := ["/app"], exposed }
  root := Tree.empty.set ["app"] (some (.file (.prog p) true))

/-- The octets of an ASCII string (a structural definition, so that the kernel can evaluate it
on literals; characters above U+00FF are truncated). -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- The response of the HTTP fixture: `HTTP/1.1 200 OK`, two octets of content. -/
def okResponse : List UInt8 := ascii "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok"

/-- The port of the HTTP fixture. -/
def httpPort : Silmaril.Net.Ip.Port := 8080

/-- The port of the vsock fixture. -/
def nitroPort : UInt32 := 5005

def noop : Flat Blob := image (.exit 0)
def crash : Flat Blob := image (.crash 11)
def spin : Flat Blob := image .spin
def http : Flat Blob := image (.httpServe httpPort okResponse) [⟨.tcp, httpPort⟩]
def nitro : Flat Blob := image (.vsockCompute nitroPort .reverse)

/-- **The specification of the HTTP example**: every event is a TCP socket event, everything sent
is the fixed `HTTP/1.1 200 OK` response, and every bound port is a valid port the image declares. -/
def httpSpec : Spec Ev := fun b =>
  Spec.always (fun e => Profile.tcpOnly e.cap = true ∧ ∀ s bs, e = .send s bs → bs = okResponse) b ∧
    Spec.safe (BindsDeclared http.config) b

/-- **The specification of the vsock example**: every event is a vsock event, and, when the
environment supplies the awaited input, the service exits 0 having answered each request with it
reversed. -/
def vsockSpec : Spec Ev := fun b =>
  Spec.always (fun e => Profile.vsockOnly e.cap = true) b ∧
    Spec.under Beh.notBlocked (Spec.totalCorrect fun t c =>
      c = 0 ∧ ∀ x, Ev.recv (csock .vsock) x ∈ t → Ev.send (csock .vsock) x.reverse ∈ t) b

/-- **A checker on contents**: the entry point is the program `exit 0`. A decidable,
concrete sufficient precondition for "exit 0 with no events" (`Thms.noopCheck_sufficient`);
by `Thms.wp_exit0_iff` it is also necessary under `small`. -/
def noopCheck (img : Flat Blob) : Bool :=
  match small.load img with
  | .ok (.exit c) => c == 0
  | _ => false

end Silmaril.Containers.Fixtures
