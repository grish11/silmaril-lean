module

public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Thms

@[expose] public section

namespace Silmaril.Isotope.LetIter.Heap.InstitutionRegression

open CategoryTheory Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model Sentence Sat Runs runs_vis runs_ret runs_vis_zero runs_ret_succ)

inductive Clock : Type → Type where
  | tick : Clock Bool

inductive OptionalClock : Type → Type where
  | tick : OptionalClock (Option Bool)

abbrev clockSignature : ITree.Signature := ⟨Clock⟩

abbrev optionalClockSignature : ITree.Signature := ⟨OptionalClock⟩

/-- A clock with definite replies implements an interface with optional replies
by reporting `some` of the actual reply. The backward map misses `none`. -/
def optionalToClock : optionalClockSignature ⟶ clockSignature where
  request | ⟨_, .tick⟩ => ⟨Bool, .tick⟩
  reply | ⟨_, .tick⟩ => some

def clockStep : Handler Nat Clock
  | ⟨_, .tick⟩, x, r, y => r = true ∧ y = x + 1

def heapClockModel (I : Type) : Model.{0,0} ((heapSignature I).sum clockSignature) where
  State := Store I × Nat
  initial x := x.2 = 0
  step
    | ⟨_, .inl ev⟩, x, r, y => step ⟨_, ev⟩ x.1 r y.1 ∧ y.2 = x.2
    | ⟨_, .inr ev⟩, x, r, y => clockStep ⟨_, ev⟩ x.2 r y.2 ∧ y.1 = x.1

def optionalTick : Sentence.{0,0} optionalClockSignature where
  Result := Option Bool
  program := vis OptionalClock.tick ret
  post b := b = some true

private theorem optionalTick_sum_tree (I : Type) :
    (optionalTick.translate
      (optionalToClock ≫ ITree.Signature.inr (heapSignature I) clockSignature)).program =
      vis (.inr Clock.tick) (fun b => ret (some b)) := by
  let f := optionalToClock ≫ ITree.Signature.inr (heapSignature I) clockSignature
  change f.tree id (vis (E := optionalClockSignature.Event) OptionalClock.tick ret) = _
  refine (f.tree_vis id OptionalClock.tick ret).trans ?_
  change vis (.inr Clock.tick) (fun b => f.tree id (ret (some b))) = _
  congr 1
  funext b
  exact f.tree_ret id (some b)

theorem optionalTick_sum (I : Type) :
    Sat (heapClockModel I)
      (optionalTick.translate (optionalToClock ≫ ITree.Signature.inr (heapSignature I) clockSignature)) := by
  intro x _ n a run
  rw [optionalTick_sum_tree] at run
  cases n with
  | zero => exact (runs_vis_zero _ _ _ _ _ run).elim
  | succ n =>
    obtain ⟨b, y, h, run⟩ := (runs_vis _ _ _ _ _ _).mp run
    cases n with
    | zero =>
      obtain rfl := (runs_ret _ _ _ _).mp run
      exact congrArg some h.1.1
    | succ n => exact (runs_ret_succ _ _ _ _ _ run).elim

theorem optionalTick_sum_runs (I : Type) :
    Runs (heapClockModel I).step (some true) 1 (emptyStore I, 0)
      (optionalTick.translate (optionalToClock ≫ ITree.Signature.inr (heapSignature I) clockSignature)).program := by
  rw [optionalTick_sum_tree]
  exact (runs_vis _ _ _ _ _ _).mpr ⟨true, (emptyStore I, 1), ⟨⟨rfl, rfl⟩, rfl⟩,
    (runs_ret _ _ _ _).mpr rfl⟩

end Silmaril.Isotope.LetIter.Heap.InstitutionRegression
