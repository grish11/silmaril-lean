module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumRecursiveSchedule
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumRecursive

/-! # Compositional replay at literal guarded operand endpoints -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive

open Morphism.CaseSSA (erase)

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {A : Ty α} {p q : Region Φ}
  {before after : List (List Φ × Nat)}

/-- Plug a scheduled body into the singleton result of another schedule.
An injected argument can contract a case in the body. Surviving paths
retain their request order and the body's exact outward labels. -/
theorem splice (producer : Schedule Γ p [A] before) (body : Schedule (A :: Γ) q L after) :
    ∃ s routes, Schedule Γ s L routes ∧ List.Sublist routes (appendPaths before after) ∧
      Continuation.Eqv pe Γ (p.lsubst (fun _ => q)) s L :=
  splice_schedule_proof producer body rfl

/-- Induction on an exact operand derivation yields a native request
schedule for the literal guarded return and its actual reification. Every path retains the
chosen position in the original ordered exit list. -/
theorem normalize {n : Nat} {β : BoundCtx (Ty α) n} {i : Nat}
    (out : At L i A) (a : Operand Φ β A) (shape : Admitted (erase a.1)) :
    ∃ s, ∃ paths : List (List Φ), Schedule β.toList s L (paths.map fun fs => (fs, i)) ∧
      Continuation.Eqv pe β.toList ((Code.br a).guardedSSA i) s L ∧
      Continuation.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA i) s L :=
  normalize_at_proof pe out a shape

/-- Replay a typed empty elimination at both literal endpoints. The
producer can have effects, but no schedule path reaches an outward label. -/
theorem normalize_abort {n : Nat} {β : BoundCtx (Ty α) n} {i : Nat}
    (out : At L i A) (a : Operand Φ β Ty.empty) (shape : Admitted (erase a.1)) :
    ∃ s, Schedule β.toList s L [] ∧
      Continuation.Eqv pe β.toList ((Code.br ⟨.abort a.1, .abort (C := A) a.2⟩).guardedSSA i) s L ∧
      Continuation.Eqv pe β.toList ((Code.ofLetCase (.abort (C := A) a.2)).guardedSSA i) s L :=
  normalize_abort_at_proof pe out a shape

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive
