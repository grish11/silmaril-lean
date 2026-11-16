module

public import Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented.Thms
public import Silmaril.Logic.Algebraic.Initial.Matching.FinitePresented.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open FinitePresentedCompiler
namespace Controls
open FinitePresentedCompiler.Examples

def equated : GlobalPresented.Sentence constants.signature :=
  ⟨constants, equations, 𝟙 _⟩

/-- The genuine equation quotient is accepted by the actual global target room. -/
theorem equation_quotient :
    (target.obj constants.signature).Sat
      (GuardedFOL.expand (SignedSpectrum.structureOf
        (Initial.Presented.quotientModel (theory constants equations)).obj))
      (compile equated) :=
  (compile_satisfaction _ equated).mpr compiled_quotient

def collided : GlobalPresented.Sentence constants.signature :=
  ⟨constants, ∅, collapse⟩

/-- Even when the ambient map identifies symbols, the original negative
spectrum is retained and rejects every native model. -/
theorem symbol_collision (N : GlobalPresented.NativeModel constants.signature) :
    ¬ (target.obj constants.signature).Sat N (compile collided) := by
  intro h
  exact collision_rejected N ((compile_satisfaction N collided).mp h)

def unary : GlobalPresented.Sentence unaryOnly.signature :=
  ⟨unaryOnly, unaryEquations, 𝟙 _⟩

/-- No nullary constructor or active carrier inhabitant is required. -/
theorem empty_active_accepted :
    (target.obj unaryOnly.signature).Sat
      (emptyNative unaryOnly unary_positive) (compile unary) :=
  (compile_satisfaction _ unary).mpr unary_equation_compiled

theorem empty_active_carrier :
    IsEmpty ((SignedSpectrum.decode (emptyNative unaryOnly unary_positive)).carrier ()) :=
  unary_active_empty

theorem padded_raw_inhabited :
    Nonempty ((emptyNative unaryOnly unary_positive).base.carrier
      (FinitePresentedCompiler.targetSort (𝟙 unaryOnly.signature))) :=
  raw_nonempty unaryOnly unary_positive

/-- Full original context remains unavailable for grounding, even though
one declared variable is unused. -/
theorem original_context_retained :
    ¬ Nonempty (∀ i : Fin unaryEquation.k,
      Initial.Presented.Characterization.Ground unaryOnly.signature (unaryEquation.ctx i)) :=
  unary_no_complete_ground_instance

end Controls
end Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented.Examples
