module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Defs
import Silmaril.Semantics.ITree.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Runtime

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope.Bridge.NamedFlat (treeExitNumber)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link (Label)

theorem numbered {locals outputs : Nat} {α : Type 1} (port : Fin outputs) (value : Silmaril.Isotope.Value α) :
    treeExitNumber ((List.finRange outputs).map fun i => (⟨.inr i⟩ : ULift.{1} (Label locals outputs)))
      (⟨.inr port⟩, value) = (port.val, value) := by
  let exits : List (ULift.{1} (Label locals outputs)) := (List.finRange outputs).map fun i => ⟨.inr i⟩
  let index : Fin exits.length := ⟨port, by simp [exits]⟩
  let isPort (x : ULift.{1} (Label locals outputs)) := decide ((⟨.inr port⟩ : ULift.{1} (Label locals outputs)) = x)
  have found : exits.findFinIdx? isPort = some index := by
    apply List.findFinIdx?_eq_some_iff.mpr
    constructor
    · simp [exits, index, isPort]
    · intro j hj
      change ¬ isPort (exits[j.val]'j.isLt)
      simp [exits, isPort]
      intro same
      exact (Nat.ne_of_gt hj) (congrArg (fun x : Fin outputs => x.val) same)
  change ((Option.map Fin.val (exits.findFinIdx? isPort)).getD exits.length, _) = _
  rw [found]
  rfl

theorem lookup_internal {I : Type} {K D : Type 1} [DecidableEq K]
    (key : I → K) (injective : Function.Injective key) (body : I → D) (keys : List I) (index : I)
    (member : index ∈ keys) :
    (keys.map fun i => (key i, body i)).lookup (key index) = some (body index) := by
  induction keys with
  | nil => simp at member
  | cons first rest ih =>
    classical
    by_cases same : index = first
    · subst first
      simp
    · have miss : key index ≠ key first := fun h => same (injective h)
      simp only [List.map_cons, List.lookup_cons, beq_false_of_ne miss]
      exact ih ((List.mem_cons.mp member).resolve_left same)

theorem lookup_external {I : Type} {K D : Type 1} [DecidableEq K]
    (key : I → K) (body : I → D) (keys : List I) (port : K)
    (outside : ∀ i, port ≠ key i) :
    (keys.map fun i => (key i, body i)).lookup port = none := by
  apply List.lookup_eq_none_iff.mpr
  rintro item member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  simpa using outside index

theorem ret_eq_pure {Q : Type} {X : Type 1} (x : X) : (ret x : Tree (Event Q) X) = pure x := rfl

universe u v

theorem iter_simulate {M : Type u → Type v} [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M]
    {X Y B C : Type u} (f : X → M (B ⊕ X)) (g : Y → M (C ⊕ Y)) (state : X → Y) (result : B → C)
    (square : ∀ x, (f x >>= fun p => pure (p.map result state)) = g (state x)) (x : X) :
    (iter f x >>= fun r => pure (result r)) = iter g (state x) := by
  let f' := mapReturn f (fun r => pure (result r))
  have commutes : (f' >=> liftPure (Sum.map id state)) = (liftPure state >=> g) := by
    funext x
    change (f' x >>= liftPure (Sum.map id state)) = (pure (state x) >>= g)
    rw [pure_bind, ← square]
    simp only [f', mapReturn, bind_assoc, liftPure]
    apply bind_congr
    intro p
    cases p <;> simp
  have natural := congrFun (LawfulElgotMonad.naturality f (fun r => pure (result r))) x
  have uniform := congrFun (LawfulElgotMonad.uniformity f' g state commutes) x
  exact (natural.trans uniform).trans (pure_bind _ _)

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Runtime
