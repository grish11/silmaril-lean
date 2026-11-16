module

public import Silmaril.Containers.Shapes.Defs
public import Silmaril.Containers.Mini.Thms
public import Silmaril.Containers.Check.Thms
public import Silmaril.Project.Shapes.Consequence.Defs

/-!
# Container problems: registered systems, instances and answers

**Consequence systems** (`silmaril consequence_system`):

| name | system |
| --- | --- |
| `containers.mini.vsys` | `vsys Mini.machRT`: images ⊢ specifications, with no undefined behaviour |
| `containers.mini.raw` | `rawsys Mini.machRT`: raw satisfaction (a comparison) |
| `containers.mini.no_ub_check` | the judgements of the checker `Mini.noUBCheck` |

**Instances** (`silmaril instance`), each with an answer checked at elaboration:

| instance | shape | expect |
| --- | --- | --- |
| `containers.mini.hello_wp` | `wp` | THM |
| `containers.mini.thread_spawn_wlp` | `wlp` | UNS (thread creation is undefined) |
| `containers.mini.thread_spawn_wlp_assume_no_ub` | `wlp` under `restrict Spec.noUB` | UNS (an assumption does not hide it) |
| `containers.mini.tcp_then_thread_wlp_enforce` | `wlp` under vsock-only enforcement | THM (pre-empted) |
| `containers.mini.no_ub_check_sound` | `checker_sound` | THM |
| `containers.mini.restrict_preserves_ub` | `preserves_ub` | THM |
| `containers.monitor_correct_stdio` | `monitor_correct` | THM |
| `containers.mini.vsys_sound_raw` | `consequence.sound_at` (`vsys` for `raw`) | THM |
| `containers.mini.raw_sound_vsys` | `consequence.sound_at` (`raw` for `vsys`) | CSA |
| `containers.mini.check_sound_vsys` | `consequence.sound_at` (the checker for `vsys`) | THM |
-/

namespace Silmaril.Containers.Shapes.Answers

open Silmaril.Containers Silmaril.Containers.Shapes Silmaril.Containers.Check

/-! ## Systems -/

silmaril consequence_system containers.mini.vsys := Silmaril.Containers.Shapes.miniVsys
  (title := "Images of the minimal machine ⊢ specifications: every run has no undefined behaviour and meets the specification")
silmaril consequence_system containers.mini.raw := Silmaril.Containers.Shapes.miniRawsys
  (title := "Images of the minimal machine ⊢ specifications, raw satisfaction (not sound for vsys)")
silmaril consequence_system containers.mini.no_ub_check := Silmaril.Containers.Shapes.miniCheckSys
  (title := "The judgements of the decidable no-undefined-behaviour checker on contents")

/-! ## Behaviour -/

silmaril instance containers.mini.hello_wp (expect := THM)
  (title := "hello: no undefined behaviour, prints hi and exits 0") := silmaril.shapes.containers.wp
  (R := Silmaril.Containers.Mini.machRT) (post := Silmaril.Containers.Shapes.helloPost)
  (i := Silmaril.Containers.Mini.mimage Silmaril.Containers.Mini.hello)

@[answers "containers.mini.hello_wp" thm]
public theorem hello_wp_answer : Wp Mini.machRT helloPost (Mini.mimage Mini.hello) :=
  Mini.hello_wp

silmaril instance containers.mini.thread_spawn_wlp (expect := UNS)
  (title := "pthread_create under the sequential machine: undefined behaviour") :=
  silmaril.shapes.containers.wlp
  (R := Silmaril.Containers.Mini.machRT) (post := Silmaril.Containers.Shapes.anyPost)
  (i := Silmaril.Containers.Mini.mimage Silmaril.Containers.Mini.threadSpawn)

@[answers "containers.mini.thread_spawn_wlp" csa]
public theorem thread_spawn_wlp_answer : ¬ Wlp Mini.machRT anyPost (Mini.mimage Mini.threadSpawn) :=
  Mini.threadSpawn_not_wlp _

silmaril instance containers.mini.thread_spawn_wlp_assume_no_ub (expect := UNS)
  (title := "Assuming no undefined behaviour does not hide thread creation") :=
  silmaril.shapes.containers.wlp
  (R := Silmaril.Containers.Runtime.restrict Silmaril.Containers.Mini.machRT
    Silmaril.Containers.Spec.noUB)
  (post := Silmaril.Containers.Shapes.anyPost)
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
  (post := Silmaril.Containers.Shapes.anyPost)
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
  (φ := Silmaril.Containers.Spec.partialCorrect Silmaril.Containers.Shapes.anyPost)

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
  (ok := Silmaril.Containers.Shapes.allowed Silmaril.Containers.Profile.stdio)

@[answers "containers.monitor_correct_stdio" thm]
public theorem monitor_correct_stdio_answer : MonitorCorrect (allowed Profile.stdio) :=
  vmonitor_correctInterleaved _

/-! ## Consequence shapes -/

open Silmaril.Project.Shapes.Consequence in
section

silmaril instance containers.mini.vsys_sound_raw (expect := THM)
  (title := "The verified system is sound for raw satisfaction") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Containers.Shapes.miniVsys) (T := Silmaril.Containers.Shapes.miniRawsys)

@[answers "containers.mini.vsys_sound_raw" thm]
public theorem vsys_sound_raw_answer : ∀ Γ φ, SoundAt miniVsys miniRawsys Γ φ :=
  fun Γ φ => vsys_sound_raw Mini.machRT Γ φ

silmaril instance containers.mini.raw_sound_vsys (expect := CSA)
  (title := "Raw satisfaction is sound for the verified system (fails: thread creation)") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Containers.Shapes.miniRawsys) (T := Silmaril.Containers.Shapes.miniVsys)

@[answers "containers.mini.raw_sound_vsys" csa]
public theorem raw_sound_vsys_answer : ∃ Γ φ, ¬ SoundAt miniRawsys miniVsys Γ φ :=
  ⟨_, Spec.partialCorrect anyPost, fun h =>
    Mini.threadSpawn_not_wlp anyPost (h (Mini.threadSpawn_partial anyPost))⟩

silmaril instance containers.mini.check_sound_vsys (expect := THM)
  (title := "The checker's judgements are sound for the verified system") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Containers.Shapes.miniCheckSys) (T := Silmaril.Containers.Shapes.miniVsys)

@[answers "containers.mini.check_sound_vsys" thm]
public theorem check_sound_vsys_answer : ∀ Γ φ, SoundAt miniCheckSys miniVsys Γ φ :=
  fun Γ φ => Mini.noUBCheck_sys_sound Γ φ

end

end Silmaril.Containers.Shapes.Answers

namespace Silmaril.Containers.Shapes

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

end Silmaril.Containers.Shapes
