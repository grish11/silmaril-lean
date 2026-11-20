import Silmaril.Containers.Noop.Thms
import Silmaril.Containers.Fixtures.Thms
import Silmaril.Containers.Mini.Thms
import Silmaril.Containers.Http.Thms
import Silmaril.Containers.HttpServe.Thms

/-!
# The container examples, runnable

    lake env lean --run examples/containers/Examples.lean            # all examples
    lake env lean --run examples/containers/Examples.lean http-serve # one
    lake env lean --run examples/containers/Examples.lean --json F   # the explorer's data

For each example: what the image is, how it is run (runtime, machine, clone policy, profile), the
specification, the run the theorem proves, and the theorems (their names are checked when this
file is elaborated). The model examples are also **executed** here, on sample inputs, and the
computed run is compared with the proved one; the real example reads its committed OCI layout with
the same reader the proof uses. Whether a claim is proved is the registry's verdict (the explorer's
Containers tab, `sil project check`), not something this file asserts.
-/

open Silmaril.Containers

/-! ## Printing runs -/

def bytesText (bs : List UInt8) : String :=
  let s := String.ofList (bs.map fun b => Char.ofNat b.toNat)
  let line := (s.splitOn "\r\n").headD s
  if bs.length ≤ 24 then s!"{repr s}" else s!"{repr line}… ({bs.length} bytes)"

def famText : Family → String
  | .inet4 => "inet4" | .inet6 => "inet6" | .unix => "unix" | .vsock => "vsock"

def evText : Ev → String
  | .socket s => s!"socket({famText s.family})"
  | .bind _ (.inet a) => s!"bind(port {a.port.toNat})"
  | .bind _ (.vsock a) => s!"bind(vsock port {a.port.toNat})"
  | .bind _ _ => "bind"
  | .listen _ => "listen"
  | .accept _ _ => "accept"
  | .connect _ _ => "connect"
  | .send _ bs => s!"send {bytesText bs}"
  | .recv _ bs => s!"recv {bytesText bs}"
  | .close _ => "close"
  | .stdout bs => s!"stdout {bytesText bs}"
  | .stderr bs => s!"stderr {bytesText bs}"
  | .stdin bs => s!"stdin {bytesText bs}"
  | .read _ _ => "read" | .write _ _ => "write" | .clock _ => "clock" | .random _ => "random"
  | .spawn _ => "spawn"

def ubText : UB → String
  | .threadCreate => "thread creation" | .stuck => "stuck" | .noInit => "no initial state"
  | .unmodeled => "unmodelled" | .memory => "memory" | .other => "other"

def stopText : Stop → String
  | .exited c => s!"exit {c.toNat}"
  | .signaled s => s!"killed by signal {s}"
  | .killed _ => "killed by the runtime"
  | .refused _ => "refused"
  | .undefined u => s!"UNDEFINED BEHAVIOUR ({ubText u})"

def runText : Beh Ev → String
  | .done t s => String.intercalate "; " (t.map evText ++ [stopText s])
  | .blocked t => String.intercalate "; " (t.map evText ++ ["(waits for the next connection)"])
  | .spins t => String.intercalate "; " (t.map evText ++ ["(runs forever)"])
  | .reactive _ => "(serves forever)"

/-! ## The examples -/

structure Example where
  id : String
  title : String
  fixture : String
  image : String
  digests : List (String × String) := []
  shape : String
  runtime : String
  machine : String
  policy : String
  profile : String
  spec : String
  verdict : String
  run : String
  theorems : List Lean.Name
  command : String
  /-- The program's source, when the image is real. -/
  source : String := ""
  /-- The run computed now, by executing the model or reading the image (`none`: not executable). -/
  executed : Option String := none

def getRoot : List UInt8 := Fixtures.ascii "GET / HTTP/1.1\r\nHost: localhost\r\n\r\n"

def hex (bs : List UInt8) : String := String.join (bs.map fun b =>
  String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)])

/-- A real example's image, read now from the committed files with `Oci.load`. -/
def readImage (dir : System.FilePath) (manifest config layer : Oci.Digest) : IO String := do
  let root : System.FilePath := dir / "layout/blobs/sha256"
  let mut blobs : List (Oci.Digest × List UInt8) := []
  for d in [manifest, config, layer] do
    blobs := (d, (← IO.FS.readBinFile (root / hex d)).toList) :: blobs
  return match Oci.load ⟨blobs⟩ manifest with
    | .error r => s!"refused: {repr r}"
    | .ok img =>
      match img.config.entryPath with
      | some p =>
        match img.root p with
        | some (.file c _) =>
          s!"read /{String.intercalate "/" p}: {c.length} bytes, sha256 {hex (Silmaril.Crypto.sha256 c)}; " ++
          (match Lps.loadElf c with | some _ => "loads as a static x86-64 ELF" | none => "does not load") ++
          (if img.config.exposed.isEmpty then "" else
            s!"; declares {String.intercalate ", " (img.config.exposed.map fun p =>
              s!"{p.port.toNat}/{match p.proto with | .tcp => "tcp" | .udp => "udp"}")}")
        | _ => "no file at the entry point"
      | none => "no entry point"

def examples : List Example := [
  { id := "containers.noop.oci_wp", title := "No-op: a static ELF that exits 0", fixture := "real"
    image := "OCI layout examples/containers/noop-oci/layout (FROM scratch, one layer, /noop)"
    digests := [("manifest", "sha256:" ++ hex Noop.manifestDigest), ("config", "sha256:" ++ hex Noop.configDigest),
      ("layer", "sha256:" ++ hex Noop.layerDigest), ("/noop (ELF)", "sha256:" ++ hex Noop.elfDigest)]
    shape := "static x86-64 ELF at the entry point"
    runtime := "Lps.ociRuntime: OCI reader with checked SHA-256, then LPS"
    machine := "LPS x86-64 (Lps.lps), every flag oracle and admissible launch"
    policy := "seqPolicy (thread creation is undefined)"
    profile := "none: no events at all"
    spec := "no undefined behaviour, exit 0, no events (wp)"
    verdict := "holds", run := "exit 0"
    theorems := [``Noop.wp_image, ``Noop.beh_image, ``Noop.runtime_load, ``Noop.elf_digest]
    command := "examples/containers/noop-oci/docker-test.sh" },
  { id := "containers.http_serve.oci_wlp", title := "http-serve: a real HTTP/1.1 server on 8080/tcp", fixture := "real"
    image := "OCI layout examples/containers/http-serve/layout (FROM scratch, one layer, /http-serve, ExposedPorts 8080/tcp)"
    digests := [("manifest", "sha256:" ++ hex HttpServe.manifestDigest),
      ("config", "sha256:" ++ hex HttpServe.configDigest), ("layer", "sha256:" ++ hex HttpServe.layerDigest),
      ("/http-serve (ELF, from http_serve.s)", "sha256:" ++ hex HttpServe.elfDigest)]
    shape := "static x86-64 ELF at the entry point"
    runtime := "Ports.ociRuntime: OCI reader with checked SHA-256, the declared 8080/tcp published, then LPS"
    machine := "LPS x86-64 (Lps.lpsWith (Ports.publish [8080])), every flag oracle, launch and connection queue"
    policy := "seqPolicy (thread creation is undefined)"
    profile := "TCP on the declared port"
    spec := "no undefined behaviour; every exit is exactly `HTTP/1.1 200 OK … ok` then the drained request (exit 0), or a defined failure 10/11/13/14 with at most a prefix sent (wlp: waiting for a peer may not end)"
    verdict := "holds"
    run := "socket; bind 8080; listen; accept; send the 40-octet response, retrying short sends; read once; exit 0"
    theorems := [``HttpServe.servesImage, ``HttpServe.sessionOk_exact, ``HttpServe.bind_published,
      ``HttpServe.published_load, ``HttpServe.elf_digest]
    command := "examples/containers/http-serve/docker-test.sh"
    source := "examples/containers/http-serve/http_serve.s" },
  { id := "containers.examples.crash_wlp", title := "Crash: killed by SIGSEGV", fixture := "model"
    image := "Mini program [crash 11] at /app", shape := "program at the entry point"
    runtime := "Mini.machRT", machine := "Mini (a straight-line model machine)"
    policy := "seqPolicy", profile := "none"
    spec := "no undefined behaviour, partial correctness (wlp)"
    verdict := "holds: a crash is defined behaviour", run := "killed by signal 11"
    theorems := [``Mini.crashNow_wlp, ``Mini.crashNow_run]
    command := "lake env lean --run examples/containers/Examples.lean crash"
    executed := some (runText (Mini.result Mini.crashNow)) },
  { id := "containers.examples.crash_wp", title := "Crash: it does not exit", fixture := "model"
    image := "Mini program [crash 11] at /app", shape := "program at the entry point"
    runtime := "Mini.machRT", machine := "Mini", policy := "seqPolicy", profile := "none"
    spec := "no undefined behaviour, exits (wp)"
    verdict := "fails: the program is killed, it never exits", run := "killed by signal 11"
    theorems := [``Mini.crashNow_not_wp]
    command := "lake env lean --run examples/containers/Examples.lean crash"
    executed := some (runText (Mini.result Mini.crashNow)) },
  { id := "containers.mini.thread_spawn_wlp", title := "Thread creation: undefined under a sequential machine"
    fixture := "model"
    image := "Mini program [clone(pthread_create flags 0x3d0f00), exit 0] at /app"
    shape := "program at the entry point", runtime := "Mini.machRT", machine := "Mini"
    policy := "seqPolicy: CLONE_THREAD/CLONE_VM requests are undefined behaviour", profile := "none"
    spec := "no undefined behaviour (wlp)"
    verdict := "fails: the run reaches undefined behaviour", run := "UNDEFINED BEHAVIOUR (thread creation)"
    theorems := [``Mini.threadSpawn_not_wlp, ``Mini.threadSpawn_run, ``Mini.threadSpawn_not_wlp_restrict_noUB]
    command := "lake env lean --run examples/containers/Examples.lean thread"
    executed := some (runText (Mini.result Mini.threadSpawn)) },
  { id := "containers.examples.http", title := "HTTP/1.1 server on 8080/tcp (model)", fixture := "model"
    image := "program httpServe 8080 at /app, ExposedPorts 8080/tcp"
    shape := "program at the entry point", runtime := "Fixtures.small", machine := "Tiny (the fixtures' model language)"
    policy := "no task creation in the model", profile := "tcpOnly"
    spec := "no undefined behaviour; TCP only; every response is `HTTP/1.1 200 OK` (parsed by the verified HTTP/1.1 parser); only declared ports"
    verdict := "holds", run := "socket; bind(port 8080); listen; then per connection: accept; recv; send the response; close"
    theorems := [``Fixtures.http_vpre, ``Http.okResponse_parses, ``Http.httpIface_valid,
      ``Http.httpIface_admissible, ``Http.http_sent]
    command := "lake env lean --run examples/containers/Examples.lean http"
    executed := some (runText (Fixtures.Tiny.run (.httpServe Fixtures.httpPort Fixtures.okResponse) [getRoot])) },
  { id := "containers.examples.vsock", title := "vsock compute service (the enclave side of a Nitro Enclave)"
    fixture := "model"
    image := "program vsockCompute 5005 reverse at /app", shape := "program at the entry point"
    runtime := "Fixtures.small", machine := "Tiny", policy := "no task creation in the model"
    profile := "vsockOnly"
    spec := "no undefined behaviour; vsock only; answers its request reversed and exits 0 when the environment sends one"
    verdict := "holds", run := "socket(vsock); bind(vsock port 5005); listen; accept; recv x; send reverse x; close; exit 0"
    theorems := [``Fixtures.nitro_vpre, ``Fixtures.nitro_total, ``Fixtures.nitro_enforce_vsock]
    command := "lake env lean --run examples/containers/Examples.lean vsock"
    executed := some (runText (Fixtures.Tiny.run (.vsockCompute Fixtures.nitroPort .reverse) [[1, 2, 3]])) }]

/-- Short names for the command line. -/
def short : String → Option String
  | "noop" => some "containers.noop.oci_wp"
  | "http-serve" => some "containers.http_serve.oci_wlp"
  | "crash" => some "containers.examples.crash_wlp"
  | "thread" => some "containers.mini.thread_spawn_wlp"
  | "http" => some "containers.examples.http"
  | "vsock" => some "containers.examples.vsock"
  | _ => none

/-! ## Output -/

def jstr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c = '"' then "\\\"" else if c = '\\' then "\\\\" else if c.toNat < 32 then " " else c.toString) ++ "\""

def jobj (kvs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (kvs.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

def jarr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def Example.json (e : Example) : String := jobj [
  ("id", jstr e.id), ("title", jstr e.title), ("fixture", jstr e.fixture), ("image", jstr e.image),
  ("digests", jarr (e.digests.map fun (k, v) => jobj [("name", jstr k), ("value", jstr v)])),
  ("shape", jstr e.shape), ("runtime", jstr e.runtime), ("machine", jstr e.machine),
  ("policy", jstr e.policy), ("profile", jstr e.profile), ("spec", jstr e.spec),
  ("expected", jstr e.verdict), ("run", jstr e.run),
  ("executed", match e.executed with | some s => jstr s | none => "null"),
  ("theorems", jarr (e.theorems.map fun n => jstr n.toString)), ("command", jstr e.command),
  ("source", if e.source = "" then "null" else jstr e.source)]

def Example.text (e : Example) (noop serve : String) : String :=
  let exec := match e.executed with
    | some s => s!"\n  executed now:  {s}{if e.fixture = "model" then "" else ""}"
    | none => ""
  s!"{e.title}  [{e.fixture}]  ({e.id})\n" ++
  s!"  image:     {e.image}\n" ++
  String.join (e.digests.map fun (k, v) => s!"             {k} {v}\n") ++
  s!"  runtime:   {e.runtime}\n  machine:   {e.machine}\n  policy:    {e.policy}\n" ++
  s!"  profile:   {e.profile}\n  spec:      {e.spec}\n  expected:  {e.verdict}\n" ++
  s!"  proved run: {e.run}" ++ exec ++
  (if e.id = "containers.noop.oci_wp" then s!"\n  image read now: {noop}" else "") ++
  (if e.id = "containers.http_serve.oci_wlp" then s!"\n  image read now: {serve}" else "") ++
  (if e.source = "" then "" else s!"\n  source:    {e.source}") ++
  s!"\n  theorems:  {String.intercalate ", " (e.theorems.map toString)}\n  try:       {e.command}\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--json", path] =>
    IO.FS.writeFile path (jobj [("kind", jstr "silmaril.containers.examples/v1"),
      ("experimental", "true"), ("examples", jarr (examples.map Example.json))] ++ "\n")
    IO.println s!"wrote {path} ({examples.length} examples)"
    return 0
  | _ =>
    let pick := match args with
      | [n] => (short n).getD n
      | _ => ""
    let noop ← readImage "examples/containers/noop-oci" Noop.manifestDigest Noop.configDigest Noop.layerDigest
    let serve ← readImage "examples/containers/http-serve" HttpServe.manifestDigest HttpServe.configDigest
      HttpServe.layerDigest
    let chosen := examples.filter fun e => pick = "" || e.id = pick ||
      (pick = "containers.examples.crash_wlp" && e.id = "containers.examples.crash_wp")
    if chosen.isEmpty then
      IO.eprintln s!"unknown example {pick}; try noop, http-serve, crash, thread, http, vsock"
      return 1
    IO.println "Container examples (experimental API). Verdicts: the registry (explorer, Containers tab).\n"
    for e in chosen do IO.println (e.text noop serve)
    return 0
