module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Transfer

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split (Witness)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Pending)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open Silmaril.Elgot.ITree (Tree ret vis diverge cases_visible diverge_bind vis_bind resume)
open LambdaSSA.Semantics.Interaction (Primitive)

universe u v
variable {V W K J α : Type (u + 1)} {F : Type v} {E : Type u → Type u}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
variable (plan : Plan V W K J) (instr : Primitive E F α) (source : Graph V K F)

section OneHop

variable {A B C : Type (u + 1)}
  {f : A → Tree E (B ⊕ A)} {g : C → Tree E (B ⊕ C)}
  (routed aligned : A → C)

private noncomputable def mapBody (t : Tree E (B ⊕ A)) : Tree E (B ⊕ C) :=
  Sum.map id routed <$> t

private theorem map_pure (a : B ⊕ A) :
    mapBody routed (pure a : Tree E (B ⊕ A)) = pure (Sum.map id routed a) := by
  simp [mapBody]

private theorem map_diverge :
    mapBody routed (diverge : Tree E (B ⊕ A)) = diverge := by
  simp [mapBody, ← bind_pure_comp]

private theorem map_vis {R : Type u} (event : E R) (k : R → Tree E (B ⊕ A)) :
    mapBody routed (vis event k) = vis event (fun reply => mapBody routed (k reply)) := by
  simp only [mapBody, ← bind_pure_comp, vis_bind]

private def Forward (l : Tree E (B ⊕ A)) (r : Tree E (B ⊕ C)) : Prop :=
  r = mapBody routed l

private def Reverse (r : Tree E (B ⊕ C)) (l : Tree E (B ⊕ A)) : Prop :=
  r = mapBody routed l ∨ ∃ p, r = pure (.inr (aligned p)) ∧ l = pure (.inr p)

variable (hop : ∀ p, routed p = aligned p ∨ g (routed p) = pure (.inr (aligned p)))
include hop

private theorem forwardInspect {l r} (linked : Forward routed l r) :
    Layer f g (fun p q => q = aligned p) (Forward routed) l r := by
  rcases linked with rfl
  rcases cases_visible l with rfl | ⟨a, rfl⟩ | ⟨R, event, k, rfl⟩
  · exact .diverged _
  · change Layer _ _ _ _ (pure a) (mapBody routed (pure a))
    rw [map_pure]
    cases a with
    | inl b => exact .exit (.refl _)
    | inr p =>
      apply Layer.edge (rightPending := aligned p)
      · rcases hop p with same | one
        · rw [Sum.map_inr, same]
          exact .refl _
        · apply Silent.more
          rw [one]
          exact .refl _
      · rfl
  · rw [map_vis]
    exact .request event (.refl _) (fun _ => rfl)

private theorem backwardInspect {r l} (linked : Reverse routed aligned r l) :
    Layer g f (fun q p => q = aligned p) (Reverse routed aligned) r l := by
  rcases linked with rfl | ⟨p, rfl, rfl⟩
  · rcases cases_visible l with rfl | ⟨a, rfl⟩ | ⟨R, event, k, rfl⟩
    · rw [map_diverge]
      exact .diverged _
    · change Layer _ _ _ _ (mapBody routed (pure a)) (pure a)
      rw [map_pure]
      cases a with
      | inl b => exact .exit (.refl _)
      | inr p =>
        rcases hop p with same | one
        · rw [Sum.map_inr, same]
          exact .edge (.refl _) rfl
        · apply Layer.leftTransfer (.refl _)
          rw [one]
          exact Or.inr ⟨p, rfl, rfl⟩
    · rw [map_vis]
      exact .request event (.refl _) (fun _ => Or.inl rfl)
  · exact .edge (.refl _) rfl

theorem resume_eq_of_hop (step : ∀ p, g (aligned p) = Sum.map id routed <$> f p)
    {l : Tree E (B ⊕ A)} {r : Tree E (B ⊕ C)} (entry : r = Sum.map id routed <$> l) :
    resume f l = resume g r := by
  apply Silmaril.Elgot.ITree.TraceLE.antisymm
  · exact resume_le_of_layer (boundary := fun p q => q = aligned p)
      (related := Forward routed) (fun h => h ▸ step _)
      (fun h => forwardInspect routed aligned hop h) entry
  · exact resume_le_of_layer (boundary := fun q p => q = aligned p)
      (related := Reverse routed aligned) (fun h => Or.inl (h ▸ step _))
      (fun h => backwardInspect routed aligned hop h) (Or.inl entry)

end OneHop

omit [DecidableEq V] in
private theorem forward_cases (checked : plan.hasEdge source = true)
    (p : Pending V K (Value α)) :
    routed plan p = aligned plan p ∨
      stepTree instr (plan.rewrite source) (routed plan p) = pure (.inr (aligned plan p)) := by
  obtain ⟨control, store⟩ := p
  cases control with
  | returned value => exact .inl rfl
  | jump pred target =>
    by_cases selected : plan.selected pred target
    · obtain ⟨rfl, rfl⟩ := selected
      apply Or.inr
      simpa [routed, aligned, Plan.rekey, Plan.selected] using step_forward plan instr source checked store
    · exact .inl (by simp [routed, aligned, Plan.rekey, selected])

private def forwardSimulation (checked : plan.hasEdge source = true) :
    Simulation instr instr source (plan.rewrite source) where
  boundary l r := r = aligned plan l
  residual := Forward (routed plan)
  atBoundary := fun eq => eq ▸ step_aligned plan instr source _
  inspect := fun h => forwardInspect _ _ (forward_cases plan instr source checked) h

private def backwardSimulation (checked : plan.hasEdge source = true) :
    Simulation instr instr (plan.rewrite source) source where
  boundary r l := r = aligned plan l
  residual := Reverse (routed plan) (aligned plan)
  atBoundary := fun eq => Or.inl (eq ▸ step_aligned plan instr source _)
  inspect := fun h => backwardInspect _ _ (forward_cases plan instr source checked) h

def buildWitness {target : Graph W J F} (checked : Checked plan source target) :
    Witness plan instr source target := by
  obtain rfl := checked.rewritten
  exact
    { forward := forwardSimulation plan instr source checked.edge
      backward := backwardSimulation plan instr source checked.edge
      enterForward := entry_routed plan instr source
      enterBackward := fun store => by
        rw [entry_routed]
        exact Or.inl rfl }

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split
