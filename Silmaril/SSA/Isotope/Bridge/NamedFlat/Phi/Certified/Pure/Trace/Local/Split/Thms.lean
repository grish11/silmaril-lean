module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Simulation

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open LambdaSSA.Semantics.Interaction (Primitive)
open Silmaril.Elgot.ITree (Tree resume)

universe u v
variable {V W K J Base α : Type (u + 1)} {F : Type v} {E : Type u → Type u} {n : Nat}
  {plan : Plan V W K J}
  {leftNames : Fin n → Option V} {rightNames : Fin n → Option W}
  {leftProfile rightProfile : BoundCtx (Ty Base) n} {leftExit rightExit : Fin 1 → Ty Base}

/-- A renamed store agrees positionally with the original store at the
aligned, typed capture slots. -/
@[expose] def InputAlignment.matched (alignment : InputAlignment plan leftProfile rightProfile
    leftExit rightExit leftNames rightNames) (store : V → Value α) :
    MatchedInputs (α := α) leftProfile rightProfile leftExit rightExit leftNames rightNames :=
  ⟨alignment.interface, store, plan.renameStore store, fun i => by
    simp only [Certified.captureEnv, i.isLt, dite_true, alignment.captures i]
    cases leftNames i <;> simp [Plan.renameStore]⟩

/-- Reuse the single-forwarding-hop simulation with any common return
observation. A routed transfer is already aligned or takes one pure step
to align, with matching requests and replies on the paired bodies. -/
theorem resume_eq_of_hop {A B C : Type (u + 1)}
    {f : A → Tree E (B ⊕ A)} {g : C → Tree E (B ⊕ C)} (routed aligned : A → C)
    (hop : ∀ p, routed p = aligned p ∨ g (routed p) = pure (.inr (aligned p)))
    (step : ∀ p, g (aligned p) = Sum.map id routed <$> f p)
    {l : Tree E (B ⊕ A)} {r : Tree E (B ⊕ C)} (entry : r = Sum.map id routed <$> l) :
    resume f l = resume g r :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split.resume_eq_of_hop routed aligned hop step entry

variable [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {source : Graph V K F} {target : Graph W J F}

/-- Synthesize the local relations in both directions from the checked
syntax. The right-hand simulation takes one silent hop on the split edge. -/
noncomputable def witness (checked : Checked plan source target) (instr : Primitive E F α) :
    Witness plan instr source target :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split.buildWitness plan instr source checked

/-- Both finite-trace inclusions hold, hence the weak observation trees are
equal. Both evaluators interpret the unchanged primitive syntax with `instr`. -/
theorem source_eq (checked : Checked plan source target) (instr : Primitive E F α)
    (store : V → Value α) :
    sourceObservation instr source store = sourceObservation instr target (plan.renameStore store) :=
  let sim := witness checked instr
  (sim.forward.source_le (sim.enterForward store)).antisymm
    (sim.backward.source_le (sim.enterBackward store))

variable [HasTy F (Ty Base)]
  {leftInputs : List V} {rightInputs : List W}
  {leftBlocks : Fin (blockCount source) → Ty Base} {rightBlocks : Fin (blockCount target) → Ty Base}
  {leftAdmission : Admission source leftInputs leftNames leftProfile leftBlocks leftExit}
  {rightAdmission : Admission target rightInputs rightNames rightProfile rightBlocks rightExit}

/-- The checked rewrite preserves the actual canonical pure packed execution
at every input transported along the typed capture alignment. -/
theorem packed_eq (checked : Checked plan source target) (instr : Primitive E F α)
    (leftClosed : Closed leftAdmission) (rightClosed : Closed rightAdmission)
    (alignment : InputAlignment plan leftProfile rightProfile leftExit rightExit leftNames rightNames)
    (store : V → Value α) :
    packedObservation leftClosed instr (alignment.matched store).leftStore =
      packedObservation rightClosed instr (alignment.matched store).rightStore := by
  rw [packedObservation_eq_sourceObservation, packedObservation_eq_sourceObservation]
  exact source_eq checked instr store

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
