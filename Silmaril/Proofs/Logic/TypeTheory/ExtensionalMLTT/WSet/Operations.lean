module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Operations.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet

universe u v

noncomputable section

@[simp]
theorem sup_equiv {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (a : A) (f : B a.val → Tree A B) :
    sup a (fun b => equiv A B (f b)) = equiv A B (.mk a f) := by
  simp only [sup, Equiv.symm_apply_apply]

@[simp]
theorem elim_equiv {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (C : carrier A B → Sort v) (s : ∀ a f, (∀ b, C (f b)) → C (sup a f))
    (t : Tree A B) : elim C s (equiv A B t) = nativeRec C s t :=
  Equiv.piCongrLeft_apply_apply C (equiv A B) (nativeRec C s) t


private theorem dependent_heq {α : Sort u} {D : α → Sort v} (f : ∀ a, D a)
    {x y : α} (h : x = y) : HEq (f x) (f y) := by
  cases h
  rfl

private theorem nativeStep_heq {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (C : carrier A B → Sort v) (s : ∀ a f, (∀ b, C (f b)) → C (sup a f))
    (a : A) (f : B a.val → Tree A B) (ih : ∀ b, C (equiv A B (f b))) :
    HEq (nativeStep C s a f ih) (s a (fun b => equiv A B (f b)) ih) := by
  unfold nativeStep
  exact cast_heq _ _

/-- The transported dependent recursor computes on a constructor. -/
theorem elim_sup {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (C : carrier A B → Sort v) (s : ∀ a f, (∀ b, C (f b)) → C (sup a f))
    (a : A) (f : B a.val → carrier A B) :
    elim C s (sup a f) = s a f (fun b => elim C s (f b)) := by
  obtain ⟨g, rfl⟩ := (Equiv.piCongrRight fun _ : B a.val => equiv A B).surjective f
  change elim C s (sup a (fun b => equiv A B (g b))) =
    s a (fun b => equiv A B (g b)) (fun b => elim C s (equiv A B (g b)))
  have hleft : HEq (elim C s (sup a (fun b => equiv A B (g b))))
      (nativeRec C s (.mk a g)) :=
    (dependent_heq (elim C s) (sup_equiv a g)).trans (heq_of_eq (elim_equiv C s _))
  have hstep : HEq (nativeRec C s (.mk a g))
      (s a (fun b => equiv A B (g b)) (fun b => nativeRec C s (g b))) :=
    nativeStep_heq C s a g _
  have hchildren : (fun b => nativeRec C s (g b)) =
      (fun b => elim C s (equiv A B (g b))) :=
    funext fun b => (elim_equiv C s (g b)).symm
  exact eq_of_heq (hleft.trans (hstep.trans (heq_of_eq (congrArg
    (s a (fun b => equiv A B (g b))) hchildren))))

/-- The constructor equation uniquely determines dependent recursion. -/
theorem elim_unique {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (C : carrier A B → Sort v) (s : ∀ a f, (∀ b, C (f b)) → C (sup a f))
    (g : ∀ t, C t)
    (hg : ∀ a f, g (sup a f) = s a f (fun b => g (f b))) : g = elim C s := by
  funext t
  apply elim (fun z => g z = elim C s z) ?_ t
  intro a f ih
  calc
    g (sup a f) = s a f (fun b => g (f b)) := hg a f
    _ = s a f (fun b => elim C s (f b)) := congrArg (s a f) (funext ih)
    _ = elim C s (sup a f) := (elim_sup C s a f).symm

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet
