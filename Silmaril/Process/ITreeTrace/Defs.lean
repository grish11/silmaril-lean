module

public import Silmaril.Process.TypedSyscall.Defs
public import Silmaril.Semantics.ITree.Trace.Defs

/-! Finite, schedule-driven observations of typed syscall trees. -/

@[expose] public section

namespace Silmaril.Process.ITreeTrace

open TypedSyscall (Signature Kernel)
open Silmaril.Elgot.ITree (Tree Visible out Trace HasTrace)

/-- A typed syscall request as an event of the existing weak ITree. -/
inductive Event (sig : Signature) : Type → Type where
  | call (req : sig.Request) : Event sig (sig.Response req)

abbrev Program (sig : Signature) (A : Type) := Tree (Event sig) A

/-- A completed exchange retains the dependency between request and reply. -/
structure Exchange (sig : Signature) where
  request : sig.Request
  reply : sig.Response request

/-- Check every attempted request in a finite observation, including a pending one. -/
def Trace.Allows {sig : Signature} {A : Type} (permitted : sig.Request → Prop) :
    Trace (Event sig) A → Prop
  | .prefix | .result _ => True
  | .request (.call req) => permitted req
  | .exchange (.call req) _ tail => permitted req ∧ Trace.Allows permitted tail

/-- A syntactic safety predicate over all typed replies, independently of any kernel. -/
def Allows {sig : Signature} {A : Type} (prog : Program sig A)
    (permitted : sig.Request → Prop) : Prop :=
  ∀ trace, HasTrace prog trace → Trace.Allows permitted trace

abbrev Pool (sig : Signature) (Tid A : Type) := Tid → Program sig A

def singleton {sig : Signature} {A : Type} (prog : Program sig A) : Pool sig Unit A :=
  fun _ => prog

inductive End (sig : Signature) (Tid A : Type) where
  | returned (values : Tid → A)
  | exited (status : Nat)
  | exhausted
  | silent (tid : Tid)
  | blocked (tid : Tid) (req : sig.Request)

variable {sig : Signature} {Tid A S Label Obs : Type} [DecidableEq Tid]

/-- Every thread has reached a return. Inspecting these returns consumes no schedule.
A return is a tree value, while an exiting kernel completion is process-wide. -/
def Returned (pool : Pool sig Tid A) (values : Tid → A) : Prop :=
  ∀ tid, out (pool tid) = Part.some (.ret (values tid))

/-- Run a finite list of thread choices against one shared store. The kernel
relation supplies each typed answer, label and successor store atomically. A
choice spends one slot on a call or on skipping an already returned thread.
A blocked request stops this observation on the selected thread; it need not be
a deadlock. Silent divergence of that thread also stops the observation.
`observe` projects each completion (including exit) into one label. -/
inductive Flatten (kernel : Kernel sig S Label) (observe : Tid → Label → Obs) :
    List Tid → Pool sig Tid A → S → List Obs → End sig Tid A → S → Prop where
  | returned {schedule pool store values} (done : Returned pool values) :
      Flatten kernel observe schedule pool store [] (.returned values) store
  | exhausted {pool store} (live : ¬ ∃ values, Returned pool values) :
      Flatten kernel observe [] pool store [] .exhausted store
  | silent {tid schedule pool store} (root : out (pool tid) = Part.none) :
      Flatten kernel observe (tid :: schedule) pool store [] (.silent tid) store
  | blocked {tid schedule pool store req next}
      (root : out (pool tid) = Part.some (.vis (.call req) next))
      (pending : ¬ ∃ label completion, kernel req store label completion) :
      Flatten kernel observe (tid :: schedule) pool store [] (.blocked tid req) store
  | exited {tid schedule pool store req next label status after}
      (root : out (pool tid) = Part.some (.vis (.call req) next))
      (step : kernel req store label (.exited status after)) :
      Flatten kernel observe (tid :: schedule) pool store [observe tid label] (.exited status) after
  | exchange {tid schedule pool store req next label reply after trace stop final}
      (root : out (pool tid) = Part.some (.vis (.call req) next))
      (step : kernel req store label (.returned reply after))
      (tail : Flatten kernel observe schedule (Function.update pool tid (next reply))
        after trace stop final) :
      Flatten kernel observe (tid :: schedule) pool store (observe tid label :: trace) stop final
  | skip {tid schedule pool store value trace stop final}
      (root : out (pool tid) = Part.some (.ret value))
      (live : ¬ ∃ values, Returned pool values)
      (tail : Flatten kernel observe schedule pool store trace stop final) :
      Flatten kernel observe (tid :: schedule) pool store trace stop final

/-- Canonical interleaving observation, with the selected thread on each label. -/
abbrev Interleaving (kernel : Kernel sig S Label) :
    List Tid → Pool sig Tid A → S → List (Tid × Label) → End sig Tid A → S → Prop :=
  Flatten kernel Prod.mk

/-- Sequential flattening, with a bound on the number of completed calls.
A sequential return value `a` is reported as `.returned (fun _ => a)`. -/
def Sequential (kernel : Kernel sig S Label) (fuel : Nat) (prog : Program sig A)
    (before : S) (trace : List Label) (stop : End sig Unit A) (after : S) : Prop :=
  Flatten kernel (fun _ label => label) (List.replicate fuel ()) (singleton prog)
    before trace stop after

end Silmaril.Process.ITreeTrace
