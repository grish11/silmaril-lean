module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.Core

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeExitNumber)

theorem numbered {locals outputs : Nat} {α : Type 1} (port : Fin outputs) (value : Value α) :
    treeExitNumber ((List.finRange outputs).map fun i => (⟨.inr i⟩ : ULift.{1} (Label locals outputs)))
      (⟨.inr port⟩, value) = (port.val, value) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.numbered port value

theorem lookup_internal {I : Type} {K D : Type 1} [DecidableEq K]
    (key : I → K) (injective : Function.Injective key) (body : I → D) (keys : List I) (index : I)
    (member : index ∈ keys) :
    (keys.map fun i => (key i, body i)).lookup (key index) = some (body index) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.lookup_internal key injective body keys index member

theorem lookup_external {I : Type} {K D : Type 1} [DecidableEq K]
    (key : I → K) (body : I → D) (keys : List I) (port : K)
    (outside : ∀ i, port ≠ key i) :
    (keys.map fun i => (key i, body i)).lookup port = none :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.lookup_external key body keys port outside

theorem ret_eq_pure {Q Reply : Type} {X : Type 1} (x : X) : (ret x : Tree (Event Q Reply) X) = pure x := rfl

universe u v

/-- Change the iterative state and return encodings using a one-step square. -/
theorem iter_simulate {M : Type u → Type v} [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M]
    {X Y B C : Type u} (f : X → M (B ⊕ X)) (g : Y → M (C ⊕ Y)) (state : X → Y) (result : B → C)
    (square : ∀ x, (f x >>= fun p => pure (p.map result state)) = g (state x)) (x : X) :
    (iter f x >>= fun r => pure (result r)) = iter g (state x) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.iter_simulate f g state result square x

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime
