module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Defs
public import Silmaril.Semantics.ElgotMonads.Thms
public import Mathlib.Algebra.FreeMonoid.Basic

/-! # A concrete ordered trace interpretation of the restricted grammar -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open CategoryTheory
open Silmaril.Elgot
open Isotope.Semantics (BoundEnv FreeEnv)
open Isotope.LetCase.LocallyNameless (Derivation Tm)
open LetIter.Semantics.Categorical (ofTypeModel ofInstructionModel)

/-- Empty-producing calls raise a terminal error. Its position outside the
writer preserves the words emitted before the error. -/
abbrev Trace := ExceptT Bool (WriterT (FreeMonoid Bool) Part)

abbrev value := Kleisli.value

def model : Isotope.Semantics.InstructionModel value signature.Instr Trace where
  eval
    | .emit bit => fun _ => ExceptT.mk (WriterT.mk (Part.some (.ok PUnit.unit, FreeMonoid.of bit)))
    | .stop bit => fun _ => ExceptT.mk (WriterT.mk (Part.some (.error bit, 1)))

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

def noFree : FreeEnv value Γ₀ := Kleisli.noFree

/-- Observe the actual monadic evaluation at a chosen bound environment. -/
def run {n : Nat} {β : BoundCtx Sorts n} {t : Tm Empty signature.Instr n} {A : Sorts}
    (d : Derivation signature.Instr Γ₀ β t A) (ρ : BoundEnv value β) :
    Part (Except Bool (value A) × FreeMonoid Bool) :=
  (d.denote value model noFree ρ).run.run

/-- The trace data predicted by the independent normal form. -/
def Normal.observe {A : Type} (nf : Normal) (success : A) :
    Part (Except Bool A × FreeMonoid Bool) :=
  Part.some (nf.2.elim (.ok success) Except.error, FreeMonoid.ofList nf.1)

abbrev traceJ := Kleisli.Adjunction.toKleisli (ofTypeMonad Trace)

noncomputable abbrev traceTypes := ofTypeModel value
noncomputable abbrev traceInstructions := ofInstructionModel value model

/-- The operation algebra uses the standard distributive Kleisli Freyd
interpretation and the same primitive computations. -/
noncomputable def traceAlgebra : CaseAlgebra signature :=
  Kleisli.algebra model

/-- Place the trace algebra in the existing room given exact region typing
coherence for its primitive interpretation. -/
noncomputable def validatedTrace
    (coherent : letI := traceInstructions
      LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr)
        traceJ traceTypes) :
    (grammarRoom traceJ signature).Mod :=
  Kleisli.validated model coherent

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
