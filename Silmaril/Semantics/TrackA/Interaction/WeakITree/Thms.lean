module

public import Silmaril.Semantics.TrackA.Interaction.WeakITree.Defs
public import Silmaril.Semantics.TrackA.Interaction.Thms

public section

namespace Silmaril.Semantics.TrackA.Interaction.WeakITree

open Silmaril.Elgot.ITree (ret vis diverge)

universe u v

variable {S : Signature.{u,u}} {A : Type v}

@[simp] theorem unfold_ret (a : A) :
    unfold (ret (E := IndexedEvent S) a) = .ret a := by simp [unfold]

@[simp] theorem unfold_vis (q : S.Request) (next : S.Response q → WeakITree S A) :
    unfold (vis (.request q) next) = .vis q next := by simp [unfold]

@[simp] theorem unfold_diverge :
    unfold (diverge : WeakITree S A) = .tau diverge := by simp [unfold]

theorem observes_diverge :
    Trace.finite [] .diverge ∈ (toDelayed (diverge : WeakITree S A)).observes :=
  ⟨(), Coalgebra.observes_silent_loop unfold_diverge⟩

end Silmaril.Semantics.TrackA.Interaction.WeakITree
