module

public import Silmaril.Containers.Mini.Defs
public import Silmaril.Containers.Machine.Thms
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

**The fixtures.**

* `hello_wp`: prints `hi` and exits 0;
* `threadSpawn_run`, `threadSpawn_not_wlp`: `clone` with `pthread_create`'s flags is
  `undefined threadCreate`, and no `wlp` holds; `threadSpawn_partial`: yet it satisfies every
  partial-correctness specification taken alone, which is why `wlp` includes `noUB`;
* `vforkExit_run`, `vforkExit_not_wlp`: `vfork` shares the address space: `threadCreate`;
* `forkExit_run`, `forkExit_not_wlp`: `fork` creates a process, which this model does not give
  a semantics: `unmodeled`, and no `wlp` holds;
* `fallOff_run`, `fallOff_not_wlp`: a program that runs off its end is stuck after its event;
* `spinForever_wlp`, `spinForever_not_wp`: no undefined behaviour is not termination.
-/

public section

namespace Silmaril.Containers.Mini

open Silmaril.Containers Silmaril.Containers.Mach

theorem runs_iff {p : List Instr} (hp : OutputOnly p) (b : Beh Ev) :
    mini.Run p b ↔ b = result p :=
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

end Silmaril.Containers.Mini
