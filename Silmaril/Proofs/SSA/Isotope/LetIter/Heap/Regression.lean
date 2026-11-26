module

import Silmaril.SSA.Isotope.LetIter.Heap.Native.Thms

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

abbrev Result (I : Type) := EvalType I valueTy

def liftValue (I : Type) : Value I ≃ Result I := (toSmall (Carrier I) valueTy).symm

noncomputable def program (I : Type) : ITree.Tree (Event I) (Result I) :=
  typed.denoteClosed (EvalType I) (instructions I)

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
    LetIter.Reindex.Structured.callInstructions, pure_bind, ITree.vis_bind, ret_bind]
  rfl

theorem program_reindex {I J : Type} (e : I ≃ J) :
    (signatureEquiv e).tree (resultEquiv e valueTy) (program I) = program J :=
  denoteClosed_natural e typed

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
  have h := (trace_fixed_iff swap (resultEquiv swap valueTy) (emptyStore (Fin 2)) (program (Fin 2))
    (storeEquiv_empty swap) (program_reindex swap) (completed 0)).mpr (completed_admitted 0)
  change ITree.HandledTrace step (emptyStore (Fin 2)) (program (Fin 2)) (completed (swap 0)) at h
  rwa [show swap 0 = 1 from Equiv.swap_apply_left _ _] at h

example :
    ITree.HandledTrace step (emptyStore Bool) (program Bool)
      ((signatureEquiv finTwoEquiv).trace (resultEquiv finTwoEquiv valueTy) (completed (0 : Fin 2))) := by
  simpa only [storeEquiv_empty, program_reindex] using
    (trace_equivariant finTwoEquiv (resultEquiv finTwoEquiv valueTy) (emptyStore (Fin 2))
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

/-- A unit state reads the self-reference and feeds it back. A reference
state frees that pointer and returns it. -/
def loopTerm : Tm Empty Prim 0 :=
  .let₁ (.op .alloc (.inl .unit))
    (.let₁ (.op .set (.pair (.bv 0) (.inr (.bv 0))))
      (.iter (.inl .unit)
        (.case (.bv 0)
          (.let₁ (.op .get (.bv 3)) (.inr (.bv 0)))
          (.let₁ (.op .free (.bv 0)) (.inl (.bv 1))))))

def loopTyped : Derivation Prim (.nil : Ctx Empty (Ty Unit)) .nil loopTerm refTy :=
  .let₁ (.op (.inl .unit)) (.let₁ (.op (.pair .bv (.inr .bv)))
    (.iter (A := valueTy) (.inl .unit)
      (.case .bv
        (.let₁ (.op (.bv (ι := 3))) (.inr .bv))
        (.let₁ (.op .bv) (.inl (.bv (ι := 1)))))))

noncomputable def loopProgram (I : Type) : ITree.Tree (Event I) (EvalType I refTy) :=
  loopTyped.denoteClosed (EvalType I) (instructions I)

def loopBody {I : Type} (i : I) : Result I → ITree.Tree (Event I) (EvalType I (.coprod refTy valueTy))
  | .inl _ => ITree.vis (getEvent i) fun v => ITree.ret (.inr (liftValue I v))
  | .inr r => ITree.vis (freeEvent r.down) fun _ => ITree.ret (.inl r)

set_option backward.isDefEq.respectTransparency false in
theorem loopProgram_eq (I : Type) : loopProgram I =
    ITree.vis (allocEvent (.inl PUnit.unit)) (fun i =>
      ITree.vis (setEvent i (.inr i)) (fun _ => iter (loopBody i) (.inl PUnit.unit))) := by
  have ret_bind {X Y : Type 1} (x : X) (f : X → ITree.Tree (Event I) Y) :
      (ITree.ret x >>= f) = f x := pure_bind x f
  have bindPure {X : Type 1} (t : ITree.Tree (Event I) X) : (t >>= pure) = t := bind_pure t
  have coprodValue (A B : Ty Unit) (s : EvalType I (.coprod A B)) :
      CoproductModel.coprodEquiv (D := EvalType I) A B s = s := rfl
  simp only [loopProgram, loopTyped, Derivation.denoteClosed, Derivation.denote, instructions,
    LetIter.Reindex.Structured.callInstructions, pure_bind, ITree.vis_bind, ret_bind,
    coprodValue, bindPure]
  congr 1
  funext i
  congr 1
  funext r
  congr 1
  funext s
  cases s <;> rfl

def loopCompleted {I : Type} (i : I) : ITree.Trace (Event I) (EvalType I refTy) :=
  .exchange (allocEvent (.inl PUnit.unit)) i
    (.exchange (setEvent i (.inr i)) PUnit.unit
      (.exchange (getEvent i) (.inr i)
        (.exchange (freeEvent i) PUnit.unit (.result ⟨i⟩))))

set_option backward.isDefEq.respectTransparency false in
theorem loopCompleted_admitted {I : Type} (i : I) :
    ITree.HandledTrace step (emptyStore I) (loopProgram I) (loopCompleted i) := by
  constructor
  · have unroll (s : Result I) : iter (loopBody i) s =
        loopBody i s >>= Sum.elim pure (iter (loopBody i)) :=
      congrFun (ITree.iterate_fixpoint (loopBody i)) s
    have ret_bind {X Y : Type 1} (x : X) (f : X → ITree.Tree (Event I) Y) :
        (ITree.ret x >>= f) = f x := pure_bind x f
    have readStep : iter (loopBody i) (.inl PUnit.unit) =
        ITree.vis (getEvent i) (fun v => iter (loopBody i) (liftValue I v)) := by
      rw [unroll (.inl PUnit.unit)]
      simp [loopBody, ret_bind]
    have freeStep : iter (loopBody i) (.inr ⟨i⟩) =
        ITree.vis (freeEvent i) (fun _ => ITree.ret ⟨i⟩) := by
      rw [unroll (.inr ⟨i⟩)]
      simp [loopBody, ret_bind]
      rfl
    rw [loopProgram_eq]
    simp [loopCompleted, ITree.HasTrace, readStep,
      show liftValue I (.inr i) = .inr ⟨i⟩ from rfl, freeStep]
  · let allocated := write (emptyStore I) i (some (.inl PUnit.unit))
    let updated := write allocated i (some (.inr i))
    refine ⟨allocated, ⟨rfl, rfl⟩, updated, ⟨?_, rfl⟩, updated, ⟨?_, rfl⟩,
      write updated i none, ⟨?_, rfl⟩, trivial⟩
    · classical
      simp [allocated, write]
    · classical
      simp [updated, write]
    · classical
      simp [updated, write]

theorem loopCompleted_rename {I J : Type} (e : I ≃ J) (i : I) :
    (signatureEquiv e).trace (resultEquiv e refTy) (loopCompleted i) = loopCompleted (e i) :=
  rfl

example : ITree.HandledTrace step (emptyStore (Fin 2)) (loopProgram (Fin 2)) (loopCompleted 1) := by
  have h := (denoteClosed_trace_rename_iff swap loopTyped (loopCompleted 0)).mpr
    (loopCompleted_admitted 0)
  rw [loopCompleted_rename, show swap 0 = 1 from Equiv.swap_apply_left _ _] at h
  exact h

example : ITree.HandledTrace step (emptyStore Bool) (loopProgram Bool) (loopCompleted true) := by
  have h := (denoteClosed_trace_image finTwoEquiv loopTyped (emptyStore (Fin 2))
    (loopCompleted true)).mpr ⟨loopCompleted 1, loopCompleted_admitted 1, by
      rw [loopCompleted_rename]
      rfl⟩
  simpa only [storeEquiv_empty, loopProgram] using h

end Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Regression
