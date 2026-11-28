module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Complete

/-! # Exact observations of a recovered mixed θ -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (exit point)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A : τ} {g : Graph Φ ε A}

section Recognition

variable [DecidableEq τ] [DecidableEq Φ]

omit [DecidableEq Φ] in
theorem candidate_generated (s : Loop Φ ε A) (pureFirst : Bool) :
    candidate (s.compile pureFirst) = some (s, pureFirst) :=
  Proofs.candidate_generated s pureFirst

theorem recover_generated (s : Loop Φ ε A) (pureFirst : Bool) :
    recover (s.compile pureFirst) = some ⟨s, pureFirst, rfl⟩ :=
  Proofs.recover_generated s pureFirst

/-- Both emitted body orders are recovered at their original numbering. -/
theorem recover_isSome_iff (g : Graph Φ ε A) :
    (recover g).isSome = true ↔ ∃ (s : Loop Φ ε A) (pureFirst : Bool), s.compile pureFirst = g :=
  Proofs.recover_isSome_iff g

theorem reject_wiring (c : Loop Φ ε A × Bool) (parsed : candidate g = some c)
    (different : c.1.compile c.2 ≠ g) : recover g = none := by
  simp [recover, parsed, certify, different]

end Recognition

variable {σ : Type u} [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem Fibre.region_observe (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point env.2 initial) =
      Part.map encodeExit ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial) := by
  rcases f with ⟨s, pureFirst, rfl⟩
  exact s.region_observe pureFirst coherent env initial

theorem Fibre.run_iff (f : Fibre g) (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (output : TyDen A) (initial final : σ) :
    (∃ fuel, NestedTheta.Partial.Executable.run (PureGamma.actions base) g fuel (point env.2 initial) =
        some (point output final)) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial =
        Part.some (exit output, final) := by
  rcases f with ⟨s, pureFirst, rfl⟩
  exact s.run_iff base pureFirst coherent env output initial final

theorem Fibre.no_return_iff (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point env.2 initial) = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial = Part.none := by
  rcases f with ⟨s, pureFirst, rfl⟩
  exact s.no_return_iff pureFirst coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse
