module

public import Silmaril.Containers.Mini.Defs
public import Silmaril.Containers.Machine.Thms
public import Silmaril.Containers.Check.Thms
import Silmaril.Proofs.Containers.Mini.Basic

/-!
# The minimal machine: theorems

PROVED (standard axioms), relative to the runtime model `machRT` over the machine `mini`.
Proofs are in `Silmaril.Proofs.Containers.Mini`.

**The runs, exactly.** `runs_iff`: a program that emits no input event has exactly one run,
`result p`. Undefined behaviour does not remove it: falling off the end is
`undefined stuck`, a `clone` is `undefined (r.ub)`.

**Weakest preconditions on contents.** `wlp_iff`, `wp_iff`: for such a program at the entry
point, `wlp` is exactly "its run has no undefined behaviour and is partially correct", and `wp`
the same with total correctness. **No undefined behaviour is a conjunct of both.**

**Consequence systems and checkers.** `rawsys_not_sound`: raw satisfaction is not sound for the
verified system (the thread-creating image is the counterexample); `noUBCheck_sound`,
`noUBCheck_sys_sound`: a decidable checker on contents for "no undefined behaviour" is a verified
sufficient precondition, so its system is sound for `vsys machRT`.

**The fixtures.**

* `hello_wp`: prints `hi` and exits 0;
* `threadSpawn_run`, `threadSpawn_not_wlp`: `clone` with `pthread_create`'s flags is
  `undefined threadCreate`, and no `wlp` holds; `threadSpawn_partial`: yet it satisfies every
  partial-correctness specification taken alone, which is why `wlp` includes `noUB`;
  `threadSpawn_not_wlp_restrict`, `_mayKill`, `_enforce`, `_restrict_noUB`: no runtime
  assumption (not even "no undefined behaviour"), kill or enforcement hides it;
* `vforkExit_run`, `vforkExit_not_wlp`: `vfork` shares the address space: `threadCreate`;
* `forkExit_run`, `forkExit_not_wlp`: `fork` creates a process, which this model does not give
  a semantics: `unmodeled`, and no `wlp` holds;
* `fallOff_run`, `fallOff_not_wlp`: a program that runs off its end is stuck after its event;
* `spinForever_wlp`, `spinForever_not_wp`: no undefined behaviour is not termination;
* `tcpThenThread_not_wlp`, `tcpThenThread_wlp_enforce`: a program that opens a TCP socket and
  then creates a thread has undefined behaviour, and satisfies `wlp` under vsock-only
  enforcement, which stops it at the socket: the thread creation is **pre-empted** (never
  reached), which relies on faithful enforcement; enforcement never hides undefined behaviour
  that is reached (`threadSpawn_not_wlp_enforce`);
* `noTasks_threadSpawn_exits`: `machinePolicy` with a machine that does not implement threads
  turns the thread request into a step that creates nothing; a parallel machine needs its own
  policy *and* states and steps that implement task creation.
-/

public section

namespace Silmaril.Containers.Mini

open Silmaril.Containers Silmaril.Containers.Mach

theorem runs_iff {p : List Instr} (hp : OutputOnly p) (b : Beh Ev) :
    mini.Run seqPolicy p b ↔ b = result p :=
  Silmaril.Proofs.Containers.Mini.runs_iff hp b

theorem beh_mimage {p : List Instr} (hp : OutputOnly p) (b : Beh Ev) :
    machRT.beh (mimage p) b ↔ b = result p :=
  Silmaril.Proofs.Containers.Mini.beh_mimage hp b

theorem wlp_iff {p : List Instr} (hp : OutputOnly p) (post : List Ev → UInt8 → Prop) :
    wlp machRT post (mimage p) ↔ Spec.noUB (result p) ∧ Spec.partialCorrect post (result p) :=
  Silmaril.Proofs.Containers.Mini.wlp_iff hp post

theorem wp_iff {p : List Instr} (hp : OutputOnly p) (post : List Ev → UInt8 → Prop) :
    wp machRT post (mimage p) ↔ Spec.noUB (result p) ∧ Spec.totalCorrect post (result p) :=
  Silmaril.Proofs.Containers.Mini.wp_iff hp post

theorem pre_iff {p : List Instr} (hp : OutputOnly p) (φ : Spec Ev) :
    pre machRT φ (mimage p) ↔ φ (result p) :=
  Silmaril.Proofs.Containers.Mini.pre_iff hp φ

/-! ## The fixtures -/

theorem hello_out : OutputOnly hello := by intro e he; simp [hello] at he; subst he; rfl
theorem threadSpawn_out : OutputOnly threadSpawn := by intro e he; simp [threadSpawn] at he
theorem vforkExit_out : OutputOnly vforkExit := by intro e he; simp [vforkExit] at he
theorem forkExit_out : OutputOnly forkExit := by intro e he; simp [forkExit] at he
theorem fallOff_out : OutputOnly fallOff := by intro e he; simp [fallOff] at he; subst he; rfl
theorem spinForever_out : OutputOnly spinForever := by intro e he; simp [spinForever] at he

theorem hello_wp :
    wp machRT (fun t c => t = [.stdout (Fixtures.ascii "hi")] ∧ c = 0) (mimage hello) :=
  (wp_iff hello_out _).2 ⟨trivial, rfl, rfl⟩

theorem threadSpawn_run (b : Beh Ev) :
    machRT.beh (mimage threadSpawn) b ↔ b = .done [] (.undefined .threadCreate) :=
  beh_mimage threadSpawn_out b

theorem threadSpawn_not_wlp (post : List Ev → UInt8 → Prop) :
    ¬ wlp machRT post (mimage threadSpawn) :=
  not_wlp_of_undefined ((threadSpawn_run _).2 rfl) post

theorem threadSpawn_partial (post : List Ev → UInt8 → Prop) :
    pre machRT (Spec.partialCorrect post) (mimage threadSpawn) :=
  (pre_iff threadSpawn_out _).2 trivial

/-- No runtime assumption hides the thread creation. -/
theorem threadSpawn_not_wlp_restrict (A : Spec Ev) (post : List Ev → UInt8 → Prop) :
    ¬ wlp (machRT.restrict A) post (mimage threadSpawn) :=
  not_vpre_of_preservesUB (Runtime.preservesUB_restrict _ A) ((threadSpawn_run _).2 rfl) _

/-- Runtime kills do not hide it. -/
theorem threadSpawn_not_wlp_mayKill (ks : Kill → Prop) (post : List Ev → UInt8 → Prop) :
    ¬ wlp (machRT.mayKill ks) post (mimage threadSpawn) :=
  not_vpre_of_preservesUB (Runtime.preservesUB_mayKill _ ks) ((threadSpawn_run _).2 rfl) _

/-- Enforcing a profile does not hide it: the thread creation is reached with no event, so there
is nothing to stop before it. -/
theorem threadSpawn_not_wlp_enforce (Pr : Profile) (post : List Ev → UInt8 → Prop) :
    ¬ wlp (machRT.enforce Pr) post (mimage threadSpawn) :=
  not_vpre_of_undefined (Runtime.enforce_keeps_reached_ub ((threadSpawn_run _).2 rfl)
    fun _ hu _ he => by rw [List.eq_nil_of_prefix_nil hu] at he; cases he) _

/-- Assuming away undefined behaviour itself does not hide it either: `restrict` keeps every
run with undefined behaviour, whatever the assumption. -/
theorem threadSpawn_not_wlp_restrict_noUB (post : List Ev → UInt8 → Prop) :
    ¬ wlp (machRT.restrict Spec.noUB) post (mimage threadSpawn) :=
  threadSpawn_not_wlp_restrict _ post

theorem vforkExit_run (b : Beh Ev) :
    machRT.beh (mimage vforkExit) b ↔ b = .done [] (.undefined .threadCreate) :=
  beh_mimage vforkExit_out b

theorem vforkExit_not_wlp (post : List Ev → UInt8 → Prop) : ¬ wlp machRT post (mimage vforkExit) :=
  not_wlp_of_undefined ((vforkExit_run _).2 rfl) post

theorem forkExit_run (b : Beh Ev) :
    machRT.beh (mimage forkExit) b ↔ b = .done [] (.undefined .unmodeled) :=
  beh_mimage forkExit_out b

theorem forkExit_not_wlp (post : List Ev → UInt8 → Prop) : ¬ wlp machRT post (mimage forkExit) :=
  not_wlp_of_undefined ((forkExit_run _).2 rfl) post

theorem fallOff_run (b : Beh Ev) :
    machRT.beh (mimage fallOff) b ↔
      b = .done [.stdout (Fixtures.ascii "x")] (.undefined .stuck) :=
  beh_mimage fallOff_out b

theorem fallOff_not_wlp (post : List Ev → UInt8 → Prop) : ¬ wlp machRT post (mimage fallOff) :=
  not_wlp_of_undefined ((fallOff_run _).2 rfl) post

theorem spinForever_wlp (post : List Ev → UInt8 → Prop) : wlp machRT post (mimage spinForever) :=
  (wlp_iff spinForever_out post).2 ⟨trivial, trivial⟩

theorem spinForever_not_wp (post : List Ev → UInt8 → Prop) :
    ¬ wp machRT post (mimage spinForever) :=
  fun h => ((wp_iff spinForever_out post).1 h).2

/-! ## Pre-emption and policies -/

theorem tcpThenThread_not_wlp (post : List Ev → UInt8 → Prop) :
    ¬ wlp machRT post (mimage tcpThenThread) :=
  Silmaril.Proofs.Containers.Mini.tcpThenThread_not_wlp post

theorem tcpThenThread_wlp_enforce (post : List Ev → UInt8 → Prop) :
    wlp (machRT.enforce Profile.vsockOnly) post (mimage tcpThenThread) :=
  Silmaril.Proofs.Containers.Mini.tcpThenThread_wlp_enforce post

theorem noTasks_threadSpawn_exits :
    (machR.withMachine mini machinePolicy).toRuntime.beh (mimage threadSpawn)
      (.done [] (.exited 0)) :=
  Silmaril.Proofs.Containers.Mini.noTasks_threadSpawn_exits

/-! ## Consequence systems and checkers -/

open Silmaril.Containers.Check Silmaril.Consequence in
/-- **Raw satisfaction is not sound for the verified system**: the thread-creating image derives
every partial-correctness specification in `rawsys`, and none in `vsys`. -/
theorem rawsys_not_sound : ¬ System.Sound (rawsys machRT) (vsys machRT) := fun h =>
  threadSpawn_not_wlp (fun _ _ => True)
    (h _ (Spec.partialCorrect fun _ _ => True) (threadSpawn_partial _))

theorem noUBCheck_sound (img : Flat (List Instr)) (h : noUBCheck img = true) :
    wlp machRT (fun _ _ => True) img :=
  Silmaril.Proofs.Containers.Mini.noUBCheck_sound img h

open Silmaril.Containers.Check Silmaril.Consequence in
/-- **The checker's system is sound for the verified system.** -/
theorem noUBCheck_sys_sound :
    System.Sound (checkSys noUBCheck (Spec.partialCorrect fun _ _ => True)) (vsys machRT) :=
  (checkSys_sound_iff_vsufficient _ _ _).2 noUBCheck_sound

end Silmaril.Containers.Mini
