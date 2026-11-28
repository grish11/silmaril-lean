module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse.Complete

/-! # Finite observations of the recovered mixed case -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open PureRow (encodeExit)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A P B C : τ} {g : Graph Φ ε A P C}

section Recognition

variable [DecidableEq τ] [DecidableEq Φ]

omit [DecidableEq Φ] in
theorem candidate_generated (s : Branch Φ ε A P B C) (pureFirst : Bool) :
    candidate (s.compile pureFirst) = some ⟨B, s, pureFirst⟩ :=
  Proofs.candidate_generated s pureFirst

theorem recover_generated (s : Branch Φ ε A P B C) (pureFirst : Bool) :
    recover (s.compile pureFirst) = some ⟨B, s, pureFirst, rfl⟩ :=
  Proofs.recover_generated s pureFirst

/-- Exactly the two emitted left-child placements are accepted, with the
right child in its emitted order and all addresses preserved. -/
theorem recover_isSome_iff (g : Graph Φ ε A P C) :
    (recover g).isSome = true ↔ ∃ (B : τ) (s : Branch Φ ε A P B C) (pureFirst : Bool), s.compile pureFirst = g :=
  Proofs.recover_isSome_iff g

theorem reject_wiring (c : Σ B, Branch Φ ε A P B C × Bool) (parsed : candidate g = some c)
    (different : c.2.1.compile c.2.2 ≠ g) : recover g = none := by
  simp [recover, parsed, certify, different]

end Recognition

variable {σ : Type u} [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem Fibre.region_observe (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (entry env.2 initial) =
      Part.map (encodeExit (P := P) (C := C))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial) := by
  rcases f with ⟨B, s, pureFirst, rfl⟩
  exact s.region_observe pureFirst coherent env initial

theorem Fibre.run_iff (f : Fibre g) (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (exit : LabelDen [Silmaril.product P C]) (initial final : σ) :
    (∃ fuel, NestedTheta.Partial.Executable.run (actions base) g fuel (entry env.2 initial) =
        some (encodeExit (exit, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial =
        Part.some (exit, final) := by
  rcases f with ⟨B, s, pureFirst, rfl⟩
  exact s.run_iff base pureFirst coherent env exit initial final

theorem Fibre.no_return_iff (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (entry env.2 initial) = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial = Part.none := by
  rw [f.region_observe coherent env initial]
  refine Part.eq_none_iff'.trans ?_
  change ¬((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial).Dom ↔ _
  exact Part.eq_none_iff'.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse
