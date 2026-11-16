module

public import Silmaril.Containers.Machine.Defs
public import Silmaril.Containers.Precondition.Thms

/-!
# Machine semantics: theorems

PROVED (standard axioms); every proof is short and stays inline.

**Task creation.**

* `CloneReq.kind_fork`, `kind_vfork`, `kind_pthread`, `kind_clone3_thread`,
  `kind_clone_vm`: `fork` creates a process, `vfork` and `clone(CLONE_VM)` a task sharing the
  address space, and glibc's `pthread_create` flags and `clone3` with `CLONE_THREAD` a thread;
* `CloneReq.ub_thread`, `ub_process`: the sequential policy makes the first two
  `threadCreate` and process creation `unmodeled`.

**Undefined behaviour is never vacuous.** For any machine `M` and a loader that loads the
image to `p`:

* `beh_ofMachine`: the runs of the image are the machine's runs of `p` under `seqPolicy`
  (`Runtime.ofMachine` is the sequential reading; `MachRuntime` takes any policy);
* `not_wlp_of_clone`: if some execution reaches a task-creation request, no `wlp` holds;
* `not_wlp_of_stuck`: if some execution reaches a stuck state, no `wlp` holds;
* `not_wlp_of_noInit`: if `p` has no initial state, no `wlp` holds.

**The machine in the runtime.** `MachRuntime.beh_iff`: the runs of an image under a machine
runtime are exactly the refusal of the loader, or the machine's runs of the loaded program
transformed by what the runtime adds. `MachRuntime.not_vpre_of_run`,
`not_vpre_restrict_of_run`, `not_vpre_mayKill_of_run`: a machine run with undefined behaviour
refutes every verification precondition, under the runtime and under assumptions or kills
added to it (when what the runtime adds keeps undefined behaviour, `Runtime.ObsKeepsUB`).

**Transfer.** `MachRuntime.wlp_withMachine`: replacing the machine keeps a `wlp` given
`SeqAgrees`; `wlp_transfer`: a `wlp` proved under a sequential runtime holds under another
(for example a parallel one) **given** `SeqAgrees`; without it nothing transfers.
-/

public section

namespace Silmaril.Containers.Mach

open Silmaril.Containers

namespace CloneReq

/-- The flags glibc's `pthread_create` passes to `clone`: `CLONE_VM | CLONE_FS | CLONE_FILES |
CLONE_SIGHAND | CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS | CLONE_PARENT_SETTID |
CLONE_CHILD_CLEARTID`. -/
def pthreadFlags : UInt64 := 0x3d0f00

theorem kind_fork : CloneReq.fork.kind = .process := by decide
theorem kind_vfork : CloneReq.vfork.kind = .sharedVm := by decide
theorem kind_pthread : (CloneReq.clone pthreadFlags).kind = .thread := by decide
theorem kind_clone3_thread : (CloneReq.clone3 (CLONE_VM ||| CLONE_THREAD)).kind = .thread := by
  decide
theorem kind_clone_vm : (CloneReq.clone (CLONE_VM ||| SIGCHLD)).kind = .sharedVm := by decide

theorem ub_thread {r : CloneReq} (h : r.kind = .thread ∨ r.kind = .sharedVm) :
    r.ub = .threadCreate := by
  unfold ub; rcases h with h | h <;> rw [h]

theorem ub_process {r : CloneReq} (h : r.kind = .process) : r.ub = .unmodeled := by
  unfold ub; rw [h]

end CloneReq

variable {I P E : Type}

theorem beh_ofMachine {load : I → Except Refusal P} {M : MachineSem P E} {i : I} {p : P}
    (hl : load i = .ok p) (b : Beh E) :
    (Runtime.ofMachine load M).beh i b ↔ M.Run seqPolicy p b := by
  rw [Runtime.beh_ok (R := Runtime.ofMachine load M) hl]
  exact ⟨fun ⟨_, h, he⟩ => he ▸ h, fun h => ⟨b, h, rfl⟩⟩

theorem not_wlp_of_clone {load : I → Except Refusal P} {M : MachineSem P E} {i : I} {p : P}
    (hl : load i = .ok p) {s s' s'' : M.State} {t : List E} {r : CloneReq} (hs : M.load p s)
    (hx : M.Exec seqPolicy s t s') (hc : M.step s' (.clone r) s'') (post : List E → UInt8 → Prop) :
    ¬ wlp (Runtime.ofMachine load M) post i :=
  not_wlp_of_undefined ((beh_ofMachine hl _).2 (.clone hs hx hc rfl)) post

theorem not_wlp_of_stuck {load : I → Except Refusal P} {M : MachineSem P E} {i : I} {p : P}
    (hl : load i = .ok p) {s s' : M.State} {t : List E} (hs : M.load p s)
    (hx : M.Exec seqPolicy s t s')
    (hst : M.Stuck s') (post : List E → UInt8 → Prop) :
    ¬ wlp (Runtime.ofMachine load M) post i :=
  not_wlp_of_undefined ((beh_ofMachine hl _).2 (.stuck hs hx hst)) post

theorem not_wlp_of_noInit {load : I → Except Refusal P} {M : MachineSem P E} {i : I} {p : P}
    (hl : load i = .ok p) (h : ∀ s, ¬ M.load p s) (post : List E → UInt8 → Prop) :
    ¬ wlp (Runtime.ofMachine load M) post i :=
  not_wlp_of_undefined ((beh_ofMachine hl _).2 (.noInit h)) post

namespace MachRuntime

theorem beh_iff (R : MachRuntime I P E) (i : I) (b : Beh E) :
    R.toRuntime.beh i b ↔
      (∃ r, R.load i = .error r ∧ b = .done [] (.refused r)) ∨
        ∃ p, R.load i = .ok p ∧ ∃ b₀, R.machine.Run R.policy p b₀ ∧ R.obs b₀ b := by
  cases hl : R.load i with
  | error r =>
    rw [Runtime.beh_error (R := R.toRuntime) hl]
    exact ⟨fun h => .inl ⟨r, rfl, h⟩, fun h => h.elim (fun ⟨_, he, hb⟩ => by cases he; exact hb)
      fun ⟨_, he, _⟩ => nomatch he⟩
  | ok p =>
    rw [Runtime.beh_ok (R := R.toRuntime) hl]
    exact ⟨fun h => .inr ⟨p, rfl, h⟩, fun h => h.elim (fun ⟨_, he, _⟩ => nomatch he)
      fun ⟨_, he, hb⟩ => by cases he; exact hb⟩

/-- **Undefined behaviour of the machine is seen**: if the machine has a run of the loaded
program with undefined behaviour, and what the runtime adds keeps undefined behaviour, no
verification precondition holds, under the runtime or under any restriction, kill or
enforcement of it. -/
theorem not_vpre_of_run {R : MachRuntime I P E} (hobs : Runtime.ObsKeepsUB R.obs) {i : I}
    {p : P} (hl : R.load i = .ok p) {t : List E} {u : UB}
    (hr : R.machine.Run R.policy p (.done t (.undefined u))) (φ : Spec E) : ¬ vpre R.toRuntime φ i :=
  not_vpre_of_undefined (Runtime.beh_of_sem_undefined (R := R.toRuntime) hobs hl hr id) φ

theorem not_vpre_restrict_of_run {R : MachRuntime I P E} (hobs : Runtime.ObsKeepsUB R.obs)
    {i : I} {p : P} (hl : R.load i = .ok p) {t : List E} {u : UB}
    (hr : R.machine.Run R.policy p (.done t (.undefined u))) (A : Spec E) (φ : Spec E) :
    ¬ vpre (R.toRuntime.restrict A) φ i :=
  not_vpre_of_preservesUB (Runtime.preservesUB_restrict _ A)
    (Runtime.beh_of_sem_undefined (R := R.toRuntime) hobs hl hr id) φ

theorem not_vpre_mayKill_of_run {R : MachRuntime I P E} (hobs : Runtime.ObsKeepsUB R.obs)
    {i : I} {p : P} (hl : R.load i = .ok p) {t : List E} {u : UB}
    (hr : R.machine.Run R.policy p (.done t (.undefined u))) (ks : Kill → Prop) (φ : Spec E) :
    ¬ vpre (R.toRuntime.mayKill ks) φ i :=
  not_vpre_of_preservesUB (Runtime.preservesUB_mayKill _ ks)
    (Runtime.beh_of_sem_undefined (R := R.toRuntime) hobs hl hr id) φ

/-- **Replacing the machine**: a `wlp` proved over one machine holds over another given
`SeqAgrees` between the two runtimes. Without such an agreement nothing is claimed. -/
theorem wlp_withMachine {R : MachRuntime I P E} {M : MachineSem P E} {pol : ClonePolicy}
    {i : I} (hagree : SeqAgrees (R.withMachine M pol).toRuntime R.toRuntime i)
    {post : List E → UInt8 → Prop} (h : wlp R.toRuntime post i) :
    wlp (R.withMachine M pol).toRuntime post i := fun b hb => h b (hagree b hb)

end MachRuntime

theorem wlp_transfer {P' : Type} {Rpar : Runtime I P' E} {Rseq : Runtime I P E} {i : I}
    (hagree : SeqAgrees Rpar Rseq i) {post : List E → UInt8 → Prop} (h : wlp Rseq post i) :
    wlp Rpar post i := fun b hb => h b (hagree b hb)

end Silmaril.Containers.Mach
