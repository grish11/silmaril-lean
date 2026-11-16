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

* `beh_ofMachine`: the runs of the image are the machine's runs of `p`;
* `not_wlp_of_clone`: if some execution reaches a task-creation request, no `wlp` holds;
* `not_wlp_of_stuck`: if some execution reaches a stuck state, no `wlp` holds;
* `not_wlp_of_noInit`: if `p` has no initial state, no `wlp` holds.

**Transfer.** `wlp_transfer`: a `wlp` proved under a sequential runtime holds under another
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
    (hl : load i = .ok p) (b : Beh E) : (Runtime.ofMachine load M).beh i b ↔ M.Run p b := by
  rw [Runtime.beh_ok (R := Runtime.ofMachine load M) hl]
  exact ⟨fun ⟨_, h, he⟩ => he ▸ h, fun h => ⟨b, h, rfl⟩⟩

theorem not_wlp_of_clone {load : I → Except Refusal P} {M : MachineSem P E} {i : I} {p : P}
    (hl : load i = .ok p) {s s' s'' : M.State} {t : List E} {r : CloneReq} (hs : M.load p s)
    (hx : M.Exec s t s') (hc : M.step s' (.clone r) s'') (post : List E → UInt8 → Prop) :
    ¬ wlp (Runtime.ofMachine load M) post i :=
  not_wlp_of_undefined ((beh_ofMachine hl _).2 (.clone hs hx hc)) post

theorem not_wlp_of_stuck {load : I → Except Refusal P} {M : MachineSem P E} {i : I} {p : P}
    (hl : load i = .ok p) {s s' : M.State} {t : List E} (hs : M.load p s) (hx : M.Exec s t s')
    (hst : M.Stuck s') (post : List E → UInt8 → Prop) :
    ¬ wlp (Runtime.ofMachine load M) post i :=
  not_wlp_of_undefined ((beh_ofMachine hl _).2 (.stuck hs hx hst)) post

theorem not_wlp_of_noInit {load : I → Except Refusal P} {M : MachineSem P E} {i : I} {p : P}
    (hl : load i = .ok p) (h : ∀ s, ¬ M.load p s) (post : List E → UInt8 → Prop) :
    ¬ wlp (Runtime.ofMachine load M) post i :=
  not_wlp_of_undefined ((beh_ofMachine hl _).2 (.noInit h)) post

theorem wlp_transfer {P' : Type} {Rpar : Runtime I P' E} {Rseq : Runtime I P E} {i : I}
    (hagree : SeqAgrees Rpar Rseq i) {post : List E → UInt8 → Prop} (h : wlp Rseq post i) :
    wlp Rpar post i := fun b hb => h b (hagree b hb)

end Silmaril.Containers.Mach
