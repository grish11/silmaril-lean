module

public import Silmaril.Process.ITreeTrace.Exact.Defs
public import Silmaril.Semantics.ExactITree.Thms
import Silmaril.Proofs.Process.ITreeTrace.Exact.Sequential

/-! Agreement between exact completed returns and the sequential finite scheduler. -/

public section

namespace Silmaril.Process.ITreeTrace.Exact

open Silmaril.Elgot.ITree.Exact (Observes)

/-- Completed sequential returns agree on every label, the return value, and the final store,
provided the schedule has one slot per completed call. -/
theorem returned_iff_sequential {sig : TypedSyscall.Signature} {S Label A : Type}
    {K : TypedSyscall.Kernel sig S Label} {prog : Program sig A}
    {before after : S} {log : List Label} {value : A} {fuel : Nat} :
    Sequential K fuel prog before log (.returned fun _ => value) after ↔
      Observes (kernel K) () (prog, before) (.finished log (.returned value after)) ∧
        log.length ≤ fuel :=
  Proofs.returned_iff_sequential

end Silmaril.Process.ITreeTrace.Exact
