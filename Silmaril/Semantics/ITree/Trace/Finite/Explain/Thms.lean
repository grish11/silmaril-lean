module

public import Silmaril.Semantics.ITree.Trace.Finite.Explain.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Explain

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u
variable {Q : Type} {Reply : Q → Type} {R S T : Type u}
  [DecidableEq S] [DecidableEq T] [DecidableEq Q] [DecidableEq R] [∀ key, Fintype (Reply key)]

/-- With complete state and reply enumerations, the pruning explanation
is absent exactly on acceptance. A returned trace distinguishes the runs
in the direction of the comparison. -/
theorem explain_spec (replies : ∀ key, List (Reply key))
    (complete : ∀ key (reply : Reply key), reply ∈ replies key)
    (statesL : Finset S) (statesR : Finset T)
    (completeL : ∀ s, s ∈ statesL) (completeR : ∀ t, t ∈ statesR)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (s : S) (t : T) :
    (explain replies statesL statesR left right s t = none ↔ compare statesL statesR left right s t = true) ∧
    ∀ trace, explain replies statesL statesR left right s t = some trace →
      HasTrace (evaluate left s) trace ∧ ¬ HasTrace (evaluate right t) trace :=
  Proofs.Semantics.Elgot.ITree.Finite.explain_spec replies complete statesL statesR completeL completeR left right s t

end Silmaril.Elgot.ITree.Finite
