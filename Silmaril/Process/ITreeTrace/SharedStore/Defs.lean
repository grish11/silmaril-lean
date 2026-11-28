module

public import Silmaril.Process.ITreeTrace.Defs
public import Silmaril.Semantics.Brookes.TreeSC.Defs

/-! Lock-free shared-store calls for the process ITree scheduler. -/

@[expose] public section

namespace Silmaril.Process.ITreeTrace.SharedStore

open Silmaril.Elgot.ITree (ret vis)
open Silmaril.Semantics.Brookes.TreeSC (Code Frame Request Store)
open Silmaril.Semantics.TrackA

/-- The process signature uses TreeSC's requests and dependent replies. -/
def signature (R : Type) : TypedSyscall.Signature := ⟨Request R, Request.Reply⟩

/-- A load returns the value at its call boundary. A store replaces one cell. -/
def access {R : Type} [DecidableEq R] (req : Request R) (before : Store R) :
    Request.Reply req × Store R :=
  match req with
  | .read _ loc => (before loc, before)
  | .write _ loc value => ((), Function.update before loc value)

/-- Both effects have exactly one atomic completion. The raw label contains
TreeSC's typed exchange and the stores at both sides of the call boundary. -/
def kernel {R : Type} [DecidableEq R] : TypedSyscall.Kernel (signature R) (Store R) (Frame R) :=
  fun req before frame completion =>
    let (reply, after) := access req before
    frame = ⟨⟨req, reply⟩, before, after⟩ ∧ completion = .returned reply after

/-- Present TreeSC's lock-free code through process calls. A load uses the
actual reply to choose the continuation. The only thread return value is unit. -/
noncomputable def program {R : Type} : Code R → Program (signature R) Unit
  | .done => ret ()
  | .load mode loc next =>
      vis (Event.call (sig := signature R) (Request.read mode loc)) fun value => program (next value)
  | .store mode loc value next =>
      vis (Event.call (sig := signature R) (Request.write mode loc value)) fun _ => program next
  | .acquire lock _ | .release lock _ => nomatch lock

noncomputable def pool {T R : Type} (code : T → Code R) : Pool (signature R) T Unit :=
  fun tid => program (code tid)

/-- The completed observation projects frames to the very same events used
by the SC scheduler, preserving thread, access mode, cell and read/write value. -/
abbrev Completes {T R : Type} [DecidableEq T] [DecidableEq R]
    (schedule : List T) (code : T → Code R) (before : Store R)
    (events : List (Concurrency.Event T Empty R)) (after : Store R) : Prop :=
  Flatten kernel (fun tid frame => frame.event tid) schedule (pool code) before events
    (.returned fun _ => ()) after

end Silmaril.Process.ITreeTrace.SharedStore
