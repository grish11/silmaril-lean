module

import Silmaril.SSA.Isotope.LetIter.Heap.Thms

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.Heap Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured (toSmall)

namespace Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Regression

/-- Allocate a unit payload, store a self-reference, then read it back. -/
def term : Tm Empty Prim 0 :=
  .let₁ (.op .alloc (.inl .unit))
    (.let₁ (.op .set (.pair (.bv 0) (.inr (.bv 0)))) (.op .get (.bv 1)))

def typed : Derivation Prim (.nil : Ctx Empty (Ty Unit)) .nil term valueTy :=
  .let₁ (.op (.inl .unit)) (.let₁ (.op (.pair .bv (.inr .bv))) (.op (.bv (ι := 1))))

abbrev Result (I : Type) := Ty.denote (fun _ : Unit => ULift.{1} I) valueTy

def liftValue (I : Type) : Value I ≃ Result I := (toSmall (Carrier I) valueTy).symm

noncomputable def program (I : Type) : ITree.Tree (Event I) (Result I) :=
  typed.denoteClosed (Ty.denote (fun _ : Unit => ULift.{1} I)) (instructions I)

def requests (I : Type) : ITree.Tree (Event I) (Result I) :=
  ITree.vis (allocEvent (.inl PUnit.unit)) fun i =>
    ITree.vis (setEvent i (.inr i)) fun _ =>
      ITree.vis (getEvent i) fun v =>
        ITree.ret (liftValue I v)

set_option backward.isDefEq.respectTransparency false in
theorem program_eq (I : Type) : program I = requests I := by
  have ret_bind {X Y : Type 1} (x : X) (f : X → ITree.Tree (Event I) Y) :
      (ITree.ret x >>= f) = f x := pure_bind x f
  simp only [program, typed, Derivation.denoteClosed, Derivation.denote, instructions,
    pure_bind, ITree.vis_bind, ret_bind]
  rfl

def resultEquiv {I J : Type} (e : I ≃ J) : Result I ≃ Result J :=
  (liftValue I).symm.trans ((valueEquiv e).trans (liftValue J))

theorem program_reindex {I J : Type} (e : I ≃ J) :
    (signatureEquiv e).tree (resultEquiv e) (program I) = program J := by
  rw [program_eq, program_eq]
  simp only [requests, ITree.SignatureEquiv.tree_vis, ITree.SignatureEquiv.tree_ret]
  change ITree.vis (allocEvent (.inl PUnit.unit))
    (fun i => ITree.vis (setEvent (e (e.symm i)) (.inr (e (e.symm i))))
      (fun _ => ITree.vis (getEvent (e (e.symm i)))
        (fun v => ITree.ret (resultEquiv e (liftValue I ((valueEquiv e).symm v)))))) = _
  simp [resultEquiv]

def completed {I : Type} (i : I) : ITree.Trace (Event I) (Result I) :=
  .exchange (allocEvent (.inl PUnit.unit)) i
    (.exchange (setEvent i (.inr i)) PUnit.unit
      (.exchange (getEvent i) (.inr i) (.result (liftValue I (.inr i)))))

theorem completed_admitted {I : Type} (i : I) :
    ITree.HandledTrace step (emptyStore I) (program I) (completed i) := by
  constructor
  · rw [program_eq]
    simp [requests, completed, ITree.HasTrace]
  · let allocated := write (emptyStore I) i (some (.inl PUnit.unit))
    let updated := write allocated i (some (.inr i))
    refine ⟨allocated, ⟨rfl, rfl⟩, updated, ⟨?_, rfl⟩, updated, ⟨?_, rfl⟩, trivial⟩
    · classical
      change allocated i ≠ none
      simp [allocated, write]
    · classical
      change updated i = some (.inr i)
      simp [updated, write]

def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

example : swap 0 = 1 := Equiv.swap_apply_left _ _

example :
    ITree.HandledTrace step (emptyStore (Fin 2)) (program (Fin 2)) (completed 1) := by
  have h := (trace_fixed_iff swap (resultEquiv swap) (emptyStore (Fin 2)) (program (Fin 2))
    (storeEquiv_empty swap) (program_reindex swap) (completed 0)).mpr (completed_admitted 0)
  change ITree.HandledTrace step (emptyStore (Fin 2)) (program (Fin 2)) (completed (swap 0)) at h
  rwa [show swap 0 = 1 from Equiv.swap_apply_left _ _] at h

example :
    ITree.HandledTrace step (emptyStore Bool) (program Bool)
      ((signatureEquiv finTwoEquiv).trace (resultEquiv finTwoEquiv) (completed (0 : Fin 2))) := by
  simpa only [storeEquiv_empty, program_reindex] using
    (trace_equivariant finTwoEquiv (resultEquiv finTwoEquiv) (emptyStore (Fin 2))
      (program (Fin 2)) (completed 0)).mpr (completed_admitted 0)

abbrev full : Store (Fin 2) := fun _ => some (.inl PUnit.unit)

example (i : Fin 2) (s : Store (Fin 2)) :
    ¬ step ⟨Fin 2, allocEvent (.inl PUnit.unit)⟩ full i s :=
  fun h => Option.some_ne_none _ h.1

example :
    ITree.HandledTrace step full (program (Fin 2)) (.request (allocEvent (.inl PUnit.unit))) := by
  rw [program_eq]
  exact ⟨ITree.hasTrace_vis_request _ _, trivial⟩

example (i : Fin 2) :
    step ⟨PUnit, freeEvent i⟩ full PUnit.unit (write full i none) ∧
    step ⟨Fin 2, allocEvent (.inl PUnit.unit)⟩ (write full i none) i
      (write (write full i none) i (some (.inl PUnit.unit))) := by
  classical
  refine ⟨⟨by simp [full], rfl⟩, ⟨?_, rfl⟩⟩
  simp [write]

end Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Regression
