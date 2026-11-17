module

public import Silmaril.Project.Shapes.Consequence.Defs
public import Silmaril.Containers.Mini.Thms
public import Silmaril.Containers.Check.Thms

/-!
# The logic graph: container obligations as problem shapes and consequence systems

Registrations of the `Containers` region in the project registry
(`docs/projects/containers.md`, "Obligations as consequence systems and acceptors"). This is a
view: it imports the generic registry (`Silmaril.Project`) and `Silmaril.Containers`, and nothing
imports it but the project dump (`silmaril.toml`). So `Containers` does not depend on `Project`,
and `Project` does not depend on `Containers`. Lean checks every record and every answer; the
answers point at the region's theorems.

**Shapes.** Every behavioural shape is a **verified** obligation: it includes "no undefined
behaviour" (`vpre`), never raw satisfaction (`pre`).

| name | statement |
| --- | --- |
| `silmaril.shapes.containers.vpre` | `vpre R φ i`: every run of `i` under `R` has no undefined behaviour and satisfies `φ` |
| `silmaril.shapes.containers.wlp` | `wlp R post i`: no undefined behaviour, partial correctness |
| `silmaril.shapes.containers.wp` | `wp R post i`: no undefined behaviour, total correctness |
| `silmaril.shapes.containers.vsufficient` | `VSufficient R Q φ`: `Q` implies the verification precondition |
| `silmaril.shapes.containers.checker_sound` | `Accept.Sound check (vset R φ)`: a checker accepts only images satisfying `vpre R φ` |
| `silmaril.shapes.containers.preserves_ub` | `R'.PreservesUB R`: a runtime model keeps every run with undefined behaviour of another |
| `silmaril.shapes.containers.seq_agrees` | `SeqAgrees R₁ R₂ i`: the transfer obligation between machines |
| `silmaril.shapes.containers.monitor_correct` | `vmonitor ok` is correct for `vlang ok` (interleaved protocol) |

**Consequence systems**: `containers.mini.vsys` (`vsys Mini.machRT`), `containers.mini.raw` (raw
satisfaction, a comparison), `containers.mini.no_ub_check` (the judgements of `Mini.noUBCheck`).

**Instances**, each with an answer:

| instance | shape | expect |
| --- | --- | --- |
| `containers.mini.hello_wp` | `wp` | THM |
| `containers.mini.thread_spawn_wlp` | `wlp` | UNS (thread creation is undefined) |
| `containers.mini.thread_spawn_wlp_assume_no_ub` | `wlp` under `restrict Spec.noUB` | UNS (the certificate policy keeps it) |
| `containers.mini.tcp_then_thread_wlp_enforce` | `wlp` under vsock-only enforcement | THM (pre-empted, under faithful enforcement) |
| `containers.mini.no_ub_check_sound` | `checker_sound` | THM |
| `containers.mini.restrict_preserves_ub` | `preserves_ub` | THM |
| `containers.monitor_correct_stdio` | `monitor_correct` | THM |
| `containers.mini.vsys_sound_raw` | `consequence.sound_at` (`vsys` for `raw`) | THM |
| `containers.mini.raw_sound_vsys` | `consequence.sound_at` (`raw` for `vsys`) | CSA |
| `containers.mini.check_sound_vsys` | `consequence.sound_at` (the checker for `vsys`) | THM |
-/

@[expose] public section

namespace Silmaril.LogicGraph.Consequence.Containers

open Silmaril.Containers Silmaril.Containers.Check Silmaril.Containers.Mach Silmaril.Containers.Mini

/-- **The verification precondition.** -/
@[problem "silmaril.shapes.containers.vpre"
  (title := "Every run of an image under a runtime model has no undefined behaviour and meets a specification")]
def VPre {I P E : Type} (R : Runtime I P E) (φ : Spec E) (i : I) : Prop := vpre R φ i

/-- **The weakest liberal precondition** (no undefined behaviour, partial correctness). -/
@[problem "silmaril.shapes.containers.wlp"
  (title := "An image has no undefined behaviour and is partially correct under a runtime model")]
def Wlp {I P E : Type} (R : Runtime I P E) (post : List E → UInt8 → Prop) (i : I) : Prop :=
  wlp R post i

/-- **The weakest precondition** (no undefined behaviour, total correctness). -/
@[problem "silmaril.shapes.containers.wp"
  (title := "An image has no undefined behaviour and is totally correct under a runtime model")]
def Wp {I P E : Type} (R : Runtime I P E) (post : List E → UInt8 → Prop) (i : I) : Prop :=
  wp R post i

/-- **A verified sufficient precondition.** -/
@[problem "silmaril.shapes.containers.vsufficient"
  (title := "A predicate on images implies the verification precondition")]
def VSufficientShape {I P E : Type} (R : Runtime I P E) (Q : I → Prop) (φ : Spec E) : Prop :=
  VSufficient R Q φ

/-- **A sound checker** for the verification precondition. -/
@[problem "silmaril.shapes.containers.checker_sound"
  (title := "A decidable checker accepts only images meeting the verification precondition")]
def CheckerSound {I P E : Type} (R : Runtime I P E) (check : I → Bool) (φ : Spec E) : Prop :=
  Silmaril.Accept.Sound check (vset R φ)

/-- **A runtime transformer preserves undefined behaviour.** -/
@[problem "silmaril.shapes.containers.preserves_ub"
  (title := "A runtime model keeps every run with undefined behaviour of another")]
def PreservesUBShape {I P P' E : Type} (R' : Runtime I P' E) (R : Runtime I P E) : Prop :=
  R'.PreservesUB R

/-- **Agreement between machines** on an image. -/
@[problem "silmaril.shapes.containers.seq_agrees"
  (title := "Every run of an image under one runtime model is a run under another")]
def SeqAgreesShape {I P P' E : Type} (R₁ : Runtime I P' E) (R₂ : Runtime I P E) (i : I) :
    Prop :=
  SeqAgrees R₁ R₂ i

/-- **The no-undefined-behaviour monitor is correct.** -/
@[problem "silmaril.shapes.containers.monitor_correct"
  (title := "The observation monitor is correct for its language in the interleaved protocol")]
def MonitorCorrect {E : Type} (ok : E → Bool) : Prop :=
  (vmonitor ok).CorrectInterleaved (vlang ok)

end Silmaril.LogicGraph.Consequence.Containers

open Silmaril.Containers Silmaril.Containers.Check Silmaril.Containers.Mini Silmaril.LogicGraph.Consequence.Containers

namespace Silmaril.LogicGraph.Consequence.Containers.Answers

/-! ## Systems -/

silmaril consequence_system containers.mini.vsys := Silmaril.Containers.Mini.miniVsys
  (title := "Images of the minimal machine ⊢ specifications: every run has no undefined behaviour and meets the specification")
silmaril consequence_system containers.mini.raw := Silmaril.Containers.Mini.miniRawsys
  (title := "Images of the minimal machine ⊢ specifications, raw satisfaction (not sound for vsys)")
silmaril consequence_system containers.mini.no_ub_check := Silmaril.Containers.Mini.miniCheckSys
  (title := "The judgements of the decidable no-undefined-behaviour checker on contents")

/-! ## Behaviour -/

silmaril instance containers.mini.hello_wp (expect := THM)
  (title := "hello: no undefined behaviour, prints hi and exits 0") := silmaril.shapes.containers.wp
  (R := Silmaril.Containers.Mini.machRT) (post := Silmaril.Containers.Mini.helloPost)
  (i := Silmaril.Containers.Mini.mimage Silmaril.Containers.Mini.hello)

@[answers "containers.mini.hello_wp" thm]
public theorem hello_wp_answer : Wp Mini.machRT helloPost (Mini.mimage Mini.hello) :=
  Mini.hello_wp

silmaril instance containers.mini.thread_spawn_wlp (expect := UNS)
  (title := "pthread_create under the sequential machine: undefined behaviour") :=
  silmaril.shapes.containers.wlp
  (R := Silmaril.Containers.Mini.machRT) (post := Silmaril.Containers.Mini.anyPost)
  (i := Silmaril.Containers.Mini.mimage Silmaril.Containers.Mini.threadSpawn)

@[answers "containers.mini.thread_spawn_wlp" csa]
public theorem thread_spawn_wlp_answer : ¬ Wlp Mini.machRT anyPost (Mini.mimage Mini.threadSpawn) :=
  Mini.threadSpawn_not_wlp _

silmaril instance containers.mini.thread_spawn_wlp_assume_no_ub (expect := UNS)
  (title := "Assuming no undefined behaviour does not hide thread creation") :=
  silmaril.shapes.containers.wlp
  (R := Silmaril.Containers.Runtime.restrict Silmaril.Containers.Mini.machRT
    Silmaril.Containers.Spec.noUB)
  (post := Silmaril.Containers.Mini.anyPost)
  (i := Silmaril.Containers.Mini.mimage Silmaril.Containers.Mini.threadSpawn)

@[answers "containers.mini.thread_spawn_wlp_assume_no_ub" csa]
public theorem thread_spawn_wlp_assume_no_ub_answer :
    ¬ Wlp (Mini.machRT.restrict Spec.noUB) anyPost (Mini.mimage Mini.threadSpawn) :=
  Mini.threadSpawn_not_wlp_restrict_noUB _

silmaril instance containers.mini.tcp_then_thread_wlp_enforce (expect := THM)
  (title := "Vsock-only enforcement stops a TCP socket before a thread is created") :=
  silmaril.shapes.containers.wlp
  (R := Silmaril.Containers.Runtime.enforce Silmaril.Containers.Mini.machRT
    Silmaril.Containers.Profile.vsockOnly)
  (post := Silmaril.Containers.Mini.anyPost)
  (i := Silmaril.Containers.Mini.mimage Silmaril.Containers.Mini.tcpThenThread)

@[answers "containers.mini.tcp_then_thread_wlp_enforce" thm]
public theorem tcp_then_thread_wlp_enforce_answer :
    Wlp (Mini.machRT.enforce Profile.vsockOnly) anyPost (Mini.mimage Mini.tcpThenThread) :=
  Mini.tcpThenThread_wlp_enforce _

/-! ## Checkers, transformers, monitors -/

silmaril instance containers.mini.no_ub_check_sound (expect := THM)
  (title := "The no-undefined-behaviour checker on contents is sound") :=
  silmaril.shapes.containers.checker_sound
  (R := Silmaril.Containers.Mini.machRT) (check := Silmaril.Containers.Mini.noUBCheck)
  (φ := Silmaril.Containers.Spec.partialCorrect Silmaril.Containers.Mini.anyPost)

@[answers "containers.mini.no_ub_check_sound" thm]
public theorem no_ub_check_sound_answer :
    CheckerSound Mini.machRT Mini.noUBCheck (Spec.partialCorrect anyPost) :=
  fun img h => Mini.noUBCheck_sound img h

silmaril instance containers.mini.restrict_preserves_ub (expect := THM)
  (title := "Assuming no undefined behaviour keeps every run that has it") :=
  silmaril.shapes.containers.preserves_ub
  (R' := Silmaril.Containers.Runtime.restrict Silmaril.Containers.Mini.machRT
    Silmaril.Containers.Spec.noUB)
  (R := Silmaril.Containers.Mini.machRT)

@[answers "containers.mini.restrict_preserves_ub" thm]
public theorem restrict_preserves_ub_answer :
    PreservesUBShape (Mini.machRT.restrict Spec.noUB) Mini.machRT :=
  Runtime.preservesUB_restrict _ _

silmaril instance containers.monitor_correct_stdio (expect := THM)
  (title := "The monitor for standard streams and no undefined behaviour is correct") :=
  silmaril.shapes.containers.monitor_correct
  (ok := Silmaril.Containers.Mini.allowed Silmaril.Containers.Profile.stdio)

@[answers "containers.monitor_correct_stdio" thm]
public theorem monitor_correct_stdio_answer : MonitorCorrect (allowed Profile.stdio) :=
  vmonitor_correctInterleaved _

/-! ## Consequence shapes -/

open Silmaril.Project.Shapes.Consequence in
section

silmaril instance containers.mini.vsys_sound_raw (expect := THM)
  (title := "The verified system is sound for raw satisfaction") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Containers.Mini.miniVsys) (T := Silmaril.Containers.Mini.miniRawsys)

@[answers "containers.mini.vsys_sound_raw" thm]
public theorem vsys_sound_raw_answer : ∀ Γ φ, SoundAt miniVsys miniRawsys Γ φ :=
  fun Γ φ => vsys_sound_raw Mini.machRT Γ φ

silmaril instance containers.mini.raw_sound_vsys (expect := CSA)
  (title := "Raw satisfaction is sound for the verified system (fails: thread creation)") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Containers.Mini.miniRawsys) (T := Silmaril.Containers.Mini.miniVsys)

@[answers "containers.mini.raw_sound_vsys" csa]
public theorem raw_sound_vsys_answer : ∃ Γ φ, ¬ SoundAt miniRawsys miniVsys Γ φ :=
  ⟨_, Spec.partialCorrect anyPost, fun h =>
    Mini.threadSpawn_not_wlp anyPost (h (Mini.threadSpawn_partial anyPost))⟩

silmaril instance containers.mini.check_sound_vsys (expect := THM)
  (title := "The checker's judgements are sound for the verified system") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Containers.Mini.miniCheckSys) (T := Silmaril.Containers.Mini.miniVsys)

@[answers "containers.mini.check_sound_vsys" thm]
public theorem check_sound_vsys_answer : ∀ Γ φ, SoundAt miniCheckSys miniVsys Γ φ :=
  fun Γ φ => Mini.noUBCheck_sys_sound Γ φ

end

end Silmaril.LogicGraph.Consequence.Containers.Answers

namespace Silmaril.LogicGraph.Consequence.Containers

/-- **The registered instances**, with what each is about. -/
public def catalogue : List (String × ObligationKind) :=
  [("containers.mini.hello_wp", .behaviour), ("containers.mini.thread_spawn_wlp", .machine),
   ("containers.mini.thread_spawn_wlp_assume_no_ub", .machine),
   ("containers.mini.tcp_then_thread_wlp_enforce", .security),
   ("containers.mini.no_ub_check_sound", .behaviour),
   ("containers.mini.restrict_preserves_ub", .machine),
   ("containers.monitor_correct_stdio", .security),
   ("containers.mini.vsys_sound_raw", .behaviour), ("containers.mini.raw_sound_vsys", .behaviour),
   ("containers.mini.check_sound_vsys", .behaviour)]

end Silmaril.LogicGraph.Consequence.Containers
