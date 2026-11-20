module

public import Silmaril.Containers.Fixtures.Defs
public import Silmaril.Containers.Precondition.Thms
import Silmaril.Proofs.Containers.Fixtures.Basic

/-!
# Fixtures: theorems under the small runtime model

PROVED (standard axioms), **relative to the small runtime model** `small` (the entry-point
shape and `Tiny.sem`). Proofs are in `Silmaril.Proofs.Containers.Fixtures`.

**No-op, crash, spin: partial against total correctness.**

* `noop_wp`, `noop_confined`: the no-op image exits 0 with no events, under profile `none`;
* `crash_wlp`, `crash_not_wp`: the crashing image satisfies every weakest liberal precondition
  and no weakest precondition;
* `spin_wlp`, `spin_not_wp`: the same for the silently diverging image;
* `spin_traceRefines_noop`, `spin_not_refines_noop`: it has the finite traces of the no-op
  image but not its runs.

**From a specification to contents.**

* `wp_exit0_iff`: the weakest precondition of "exit 0 with no events" is exactly "the entry
  point is the program `exit 0`", a predicate on the configuration and the files;
* `noopCheck_iff`, `noopCheck_sufficient`: a decidable checker on contents that is a concrete
  sufficient precondition.

**HTTP over TCP.**

* `http_confined`: every run is confined to `tcpOnly`; `http_not_vsock`: not to `vsockOnly`;
* `http_binds_declared`: it binds only the port it declares (8080/tcp, valid);
* `http_sends_only`: everything it sends is the fixed `HTTP/1.1 200 OK` response;
* `http_never_stops`: under a live environment it never stops (it waits or serves forever);
* `http_enforce_vsock`: under a runtime that enforces vsock-only, its only run is a policy
  kill before any event.

**vsock compute (the process inside a Nitro Enclave; not the enclave's boot or attestation).**

* `nitro_confined`: every run is confined to `vsockOnly`;
* `nitro_enforce_vsock`: enforcing vsock-only changes none of its runs;
* `nitro_total`: under a live environment it exits 0 having answered each request reversed.

**Nondeterminism.** `echoOnce_det`: a program whose runs differ only in its input is
deterministic up to inputs; `coin_not_det`: one that chooses its output is not.

**Testing oracle.** `run_sound`: every run `Tiny.run` computes for a script of inputs is a run of
`Tiny.sem`, so the executable checks in `Fixtures.Examples` evaluate runs of the model.
-/

public section

namespace Silmaril.Containers.Fixtures

theorem load_image (p : Tiny) (e : List PortSpec) : small.load (image p e) = .ok p := rfl

theorem beh_image (p : Tiny) (e : List PortSpec) (b : Beh Ev) :
    small.beh (image p e) b ↔ Tiny.sem p b :=
  Silmaril.Proofs.Containers.Fixtures.beh_image p e b

theorem noop_wp : wp small (fun t c => t = [] ∧ c = 0) noop :=
  Silmaril.Proofs.Containers.Fixtures.noop_wp

theorem noop_confined : pre small (Spec.always fun e => Profile.none e.cap = true) noop :=
  Silmaril.Proofs.Containers.Fixtures.noop_confined

theorem crash_wlp (post : List Ev → UInt8 → Prop) : wlp small post crash :=
  Silmaril.Proofs.Containers.Fixtures.crash_wlp post

theorem crash_not_wp (post : List Ev → UInt8 → Prop) : ¬ wp small post crash :=
  Silmaril.Proofs.Containers.Fixtures.crash_not_wp post

theorem spin_wlp (post : List Ev → UInt8 → Prop) : wlp small post spin :=
  Silmaril.Proofs.Containers.Fixtures.spin_wlp post

theorem spin_not_wp (post : List Ev → UInt8 → Prop) : ¬ wp small post spin :=
  Silmaril.Proofs.Containers.Fixtures.spin_not_wp post

theorem spin_traceRefines_noop : (small.beh spin).TraceRefines (small.beh noop) :=
  Silmaril.Proofs.Containers.Fixtures.spin_traceRefines_noop

theorem spin_not_refines_noop : ¬ (small.beh spin).Refines (small.beh noop) :=
  Silmaril.Proofs.Containers.Fixtures.spin_not_refines_noop

theorem wp_exit0_iff (img : Flat Blob) :
    wp small (fun t c => t = [] ∧ c = 0) img ↔ small.load img = .ok (.exit 0) :=
  Silmaril.Proofs.Containers.Fixtures.wp_exit0_iff img

theorem noopCheck_iff (img : Flat Blob) :
    noopCheck img = true ↔ small.load img = .ok (.exit 0) :=
  Silmaril.Proofs.Containers.Fixtures.noopCheck_iff img

/-- `noopCheck` as a concrete sufficient precondition in the language of checkers, for the
verification precondition (no undefined behaviour, and total correctness). -/
def noopCheck_sufficient :
    VSufficientIn (Assertions.bool (Flat Blob)) small
      (Spec.totalCorrect fun t c => t = [] ∧ c = 0) :=
  ⟨noopCheck, fun img h => (wp_exit0_iff img).2 ((noopCheck_iff img).1 h)⟩

theorem http_confined : pre small (Spec.always fun e => Profile.tcpOnly e.cap = true) http :=
  Silmaril.Proofs.Containers.Fixtures.http_confined

theorem http_not_vsock :
    ¬ pre small (Spec.always fun e => Profile.vsockOnly e.cap = true) http :=
  Silmaril.Proofs.Containers.Fixtures.http_not_vsock

theorem http_binds_declared : pre small (Spec.safe (BindsDeclared http.config)) http :=
  Silmaril.Proofs.Containers.Fixtures.http_binds_declared

theorem http_sends_only :
    pre small (Spec.always fun e => ∀ s bs, e = .send s bs → bs = okResponse) http :=
  Silmaril.Proofs.Containers.Fixtures.http_sends_only

theorem http_never_stops : pre small (Spec.under Beh.notBlocked fun b => ¬ b.Stopped) http :=
  Silmaril.Proofs.Containers.Fixtures.http_never_stops

theorem http_enforce_vsock (b : Beh Ev) :
    (small.enforce Profile.vsockOnly).beh http b ↔ b = .done [] (.killed .policy) :=
  Silmaril.Proofs.Containers.Fixtures.http_enforce_vsock b

theorem nitro_confined :
    pre small (Spec.always fun e => Profile.vsockOnly e.cap = true) nitro :=
  Silmaril.Proofs.Containers.Fixtures.nitro_confined

theorem nitro_enforce_vsock (b : Beh Ev) :
    (small.enforce Profile.vsockOnly).beh nitro b ↔ small.beh nitro b :=
  Silmaril.Proofs.Containers.Fixtures.nitro_enforce_vsock b

theorem nitro_total :
    pre small (Spec.under Beh.notBlocked (Spec.totalCorrect fun t c =>
      c = 0 ∧ ∀ x, Ev.recv (csock .vsock) x ∈ t → Ev.send (csock .vsock) x.reverse ∈ t))
      nitro :=
  Silmaril.Proofs.Containers.Fixtures.nitro_total

theorem echoOnce_det :
    Model.DetUpToInputs Ev.isInput
      (fun b => ∃ x, b = .done [.stdin x, .stdout x] (.exited 0)) :=
  Silmaril.Proofs.Containers.Fixtures.echoOnce_det

theorem coin_not_det :
    ¬ Model.DetUpToInputs Ev.isInput
      (fun b => b = .done [.stdout [0]] (.exited 0) ∨ b = .done [.stdout [1]] (.exited 0)) :=
  Silmaril.Proofs.Containers.Fixtures.coin_not_det

theorem run_sound (p : Tiny) (inputs : List (List UInt8)) : Tiny.sem p (Tiny.run p inputs) :=
  Silmaril.Proofs.Containers.Fixtures.run_sound p inputs

/-- **The HTTP example, verified**: no undefined behaviour, TCP only, only the HTTP/1.1 200
response, only declared ports. -/
theorem http_vpre : vpre small httpSpec http := Silmaril.Proofs.Containers.Fixtures.http_vpre

/-- **The vsock example, verified**: no undefined behaviour, vsock only, and total correctness
when the environment supplies the input. -/
theorem nitro_vpre : vpre small vsockSpec nitro := Silmaril.Proofs.Containers.Fixtures.nitro_vpre

end Silmaril.Containers.Fixtures
