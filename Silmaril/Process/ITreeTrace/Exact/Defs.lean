module

public import Silmaril.Process.ITreeTrace.Defs
public import Silmaril.Semantics.ExactITree.Defs

/-! Typed syscall trees as exact-lowering signatures and relational kernels. -/

@[expose] public section

namespace Silmaril.Process.ITreeTrace.Exact

open CategoryTheory
open Silmaril.Elgot.ITree.Exact (Signature Profile Kernel)

/-- The exact institution uses the same indexed events and weak trees as the finite scheduler. -/
abbrev eventSignature (sig : TypedSyscall.Signature) : Signature := ⟨Event sig⟩

/-- Translate one request and interpret its reply at the original request's response type. -/
def lowering {src dst : TypedSyscall.Signature} (hom : src.Hom dst) :
    eventSignature src ⟶ eventSignature dst where
  exchange
    | .call req => ⟨_, .call (hom.request req), hom.response req⟩

/-- The caller supplies the initial store. Each completion emits one label.
A typed syscall exit becomes a stop with an exit status and a final store. -/
abbrev profile (Store Label : Type) : Profile := ⟨Unit, Store, Label, Nat⟩

/-- An absent syscall completion stays absent, giving a blocked observation at a visible root. -/
def kernel {sig : TypedSyscall.Signature} {Store Label : Type}
    (K : TypedSyscall.Kernel sig Store Label) : Kernel (profile Store Label) (eventSignature sig) :=
  fun _ before {_} event completion =>
    match event with
    | .call req =>
      match completion with
      | .reply reply after batch =>
        ∃ label, batch = [label] ∧ K req before label (.returned reply after)
      | .stop status final batch =>
        ∃ after label, final = some after ∧ batch = [label] ∧ K req before label (.exited status after)

end Silmaril.Process.ITreeTrace.Exact
