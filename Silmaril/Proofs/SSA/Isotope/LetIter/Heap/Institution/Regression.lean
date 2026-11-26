module

public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Thms

public section

namespace Silmaril.Isotope.LetIter.Heap.InstitutionRegression

open CategoryTheory Silmaril.Elgot
open Silmaril.Logic.ITree (Model Sentence Runs Sat satisfaction runs_vis runs_ret runs_vis_zero runs_ret_succ)

variable {I : Type}

open Silmaril.Isotope.Semantics Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured (toSmall)

def lifecycleTerm : Tm Empty Prim 0 :=
  .let₁ (.op .alloc (.inl .unit))
    (.let₁ (.op .set (.pair (.bv 0) (.inr (.bv 0))))
      (.let₁ (.op .get (.bv 1))
        (.let₁ (.op .free (.bv 2)) (.pair (.bv 3) (.bv 1)))))

def lifecycleTyping :
    Derivation Prim (.nil : Ctx Empty (Ty Unit)) .nil lifecycleTerm (.product refTy valueTy) :=
  .let₁ (.op (.inl .unit))
    (.let₁ (.op (.pair .bv (.inr .bv)))
      (.let₁ (.op (.bv (ι := 1)))
        (.let₁ (.op (.bv (ι := 2))) (.pair (.bv (ι := 3)) (.bv (ι := 1))))))

set_option backward.isDefEq.respectTransparency false in
/-- The institution's program is the native LetIter denotation with small return values. -/
theorem lifecycle_denote (I : Type) :
    (𝟙 (heapSignature I) : heapSignature I ⟶ heapSignature I).tree
      (toSmall (Carrier I) (.product refTy valueTy))
      (lifecycleTyping.denoteClosed (Ty.denote (fun _ : Unit => ULift.{1} I)) (instructions I)) =
      (lifecycle (I := I)).program := by
  have ret_bind {X Y : Type 1} (x : X) (f : X → ITree.Tree (Event I) Y) :
      (ITree.ret x >>= f) = f x := pure_bind x f
  have eval_step (f : Prim) (x : Ty.denote (fun _ : Unit => ULift.{1} I) (instrSrc f)) :
      (instructions I).eval f x =
        ITree.vis (.call f (toSmall (Carrier I) (instrSrc f) x))
          (fun r => ITree.ret ((toSmall (Carrier I) (instrTrg f)).symm r)) := rfl
  have denote : lifecycleTyping.denoteClosed (Ty.denote (fun _ : Unit => ULift.{1} I))
        (instructions I) =
      ITree.vis (allocEvent (.inl PUnit.unit)) (fun i =>
        ITree.vis (setEvent i (.inr i)) fun _ =>
          ITree.vis (getEvent i) fun v =>
            ITree.vis (freeEvent i) fun _ =>
              ITree.ret ((toSmall (Carrier I) (.product refTy valueTy)).symm (i, v))) := by
    simp only [lifecycleTyping, Derivation.denoteClosed, Derivation.denote, eval_step,
      pure_bind, ITree.vis_bind, ret_bind]
    rfl
  rw [denote]
  simp only [lifecycle, ITree.Signature.Hom.tree_vis, ITree.Signature.Hom.tree_ret]
  change ITree.vis (allocEvent (.inl PUnit.unit)) (fun i =>
    ITree.vis (setEvent i (.inr i)) fun _ =>
      ITree.vis (getEvent i) fun v =>
        ITree.vis (freeEvent i) fun _ =>
          ITree.ret ((toSmall (Carrier I) (.product refTy valueTy))
            ((toSmall (Carrier I) (.product refTy valueTy)).symm (i, v)))) = _
  simp only [Equiv.apply_symm_apply]
  rfl

theorem lifecycle_sat (I : Type) : Sat (heapModel I) lifecycle := by
  intro x _ n a run
  simp only [lifecycle] at run
  cases n with
  | zero => exact (runs_vis_zero _ _ _ _ _ run).elim
  | succ n =>
    obtain ⟨i, allocated, _, run⟩ := (runs_vis _ _ _ _ _ _).mp run
    cases n with
    | zero => exact (runs_vis_zero _ _ _ _ _ run).elim
    | succ n =>
      obtain ⟨_, updated, ⟨_, rfl⟩, run⟩ := (runs_vis _ _ _ _ _ _).mp run
      cases n with
      | zero => exact (runs_vis_zero _ _ _ _ _ run).elim
      | succ n =>
        obtain ⟨v, read, hget, run⟩ := (runs_vis _ _ _ _ _ _).mp run
        have hv : v = (.inr i : Value I) := by
          classical
          have h : write allocated i (some (.inr i)) i = some v := hget.1
          have same : write allocated i (some (.inr i)) i = some (.inr i) := by
            exact Function.update_self i (some (.inr i)) allocated
          exact Option.some.inj (h.symm.trans same)
        cases n with
        | zero => exact (runs_vis_zero _ _ _ _ _ run).elim
        | succ n =>
          obtain ⟨_, _, _, run⟩ := (runs_vis _ _ _ _ _ _).mp run
          cases n with
          | zero =>
            obtain rfl := (runs_ret _ _ _ _).mp run
            exact hv
          | succ n => exact (runs_ret_succ _ _ _ _ _ run).elim

theorem lifecycle_runs (i : I) :
    Runs (heapModel I).step (i, .inr i) 4 (emptyStore I) (lifecycle (I := I)).program := by
  classical
  let allocated := write (emptyStore I) i (some (.inl PUnit.unit))
  let updated := write allocated i (some (.inr i))
  apply (runs_vis _ _ _ _ _ _).mpr
  refine ⟨i, allocated, ⟨rfl, rfl⟩, (runs_vis _ _ _ _ _ _).mpr ?_⟩
  refine ⟨PUnit.unit, updated, ⟨?_, rfl⟩, (runs_vis _ _ _ _ _ _).mpr ?_⟩
  · change allocated i ≠ none
    simp [allocated, write]
  refine ⟨.inr i, updated, ⟨?_, rfl⟩, (runs_vis _ _ _ _ _ _).mpr ?_⟩
  · change updated i = some (.inr i)
    simp [updated, write]
  refine ⟨PUnit.unit, write updated i none, ⟨?_, rfl⟩, (runs_ret _ _ _ _).mpr rfl⟩
  simp [updated, write]

theorem readLaw_sat (i : I) : Sat ((heapModel I).reduct (readInclusion I)) (readLaw i) := by
  intro x _ n a run
  simp only [readLaw] at run
  cases n with
  | zero => exact (runs_vis_zero _ _ _ _ _ run).elim
  | succ n =>
    obtain ⟨v, afterFirst, firstStep, tail⟩ := (runs_vis _ _ _ _ _ _).mp run
    obtain ⟨v', reply, hv, unchanged⟩ := firstStep
    change v' = v at reply
    subst v'
    subst afterFirst
    cases n with
    | zero => exact (runs_vis_zero _ _ _ _ _ tail).elim
    | succ n =>
      obtain ⟨w, afterSecond, secondStep, last⟩ := (runs_vis _ _ _ _ _ _).mp tail
      obtain ⟨w', reply, hw, unchanged⟩ := secondStep
      change w' = w at reply
      subst w'
      subst afterSecond
      cases n with
      | zero =>
        obtain rfl := (runs_ret _ _ _ _).mp last
        exact Option.some.inj (hv.symm.trans hw)
      | succ n => exact (runs_ret_succ _ _ _ _ _ last).elim

theorem lifecycle_finTwo_to_bool :
    Sat (heapModel Bool) ((lifecycle (I := Fin 2)).translate (heapRename finTwoEquiv)) :=
  (heap_sat_rename finTwoEquiv _).mpr (lifecycle_sat (Fin 2))

theorem readLaw_swap :
    Sat (heapModel (Fin 2))
      ((readLaw (0 : Fin 2)).translate (readInclusion _ ≫ heapRename (Equiv.swap 0 1))) := by
  rw [Sentence.translate_comp, translate_readInclusion, satisfaction]
  exact (read_sat_rename (Equiv.swap 0 1) _).mpr (readLaw_sat 0)

end Silmaril.Isotope.LetIter.Heap.InstitutionRegression
