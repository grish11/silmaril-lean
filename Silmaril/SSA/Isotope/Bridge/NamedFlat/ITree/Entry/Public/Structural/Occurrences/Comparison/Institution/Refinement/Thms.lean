module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Refinement.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Refinement

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.Elgot.ITree (HandledTrace)

universe u

variable {V K : Type 1} [DecidableEq V] [DecidableEq K]
  {S T : OpcodeSignature} {exits : List K} {fields : K → List V}

theorem Sentence.swap_map (φ : Sentence S exits fields) (f : S ⟶ T) :
    φ.swap.map f = (φ.map f).swap :=
  Subtype.ext rfl

/-- The compiled sentence compares the original left and right runners
under the same reduced policy at their common store. The exact trace
already carries the replay evidence needed on both sides. -/
theorem Sentence.compile_sat_map_iff (φ : Sentence S exits fields) (f : S ⟶ T)
    (policy : Model.{0, u} T.primitive.traceSignature.toSignature) :
    TraceInstitution.Sat policy (φ.map f).compile ↔
      let reduced := policy.reduct f.events.hom
      ∀ x, reduced.initial x → ∀ trace,
        HandledTrace reduced.step x (LiveOut.observeRaw S.primitive.primitive exits fields φ.val.left φ.val.initial)
          trace →
        HandledTrace reduced.step x (LiveOut.observeRaw S.primitive.primitive exits fields φ.val.right φ.val.initial)
          trace := by
  rw [(φ.map f).compile_eq_original]
  exact (φ.sat_map_iff f policy).trans
    (Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.sat_directed φ.val _)

/-- Universal directed validity is preserved and reflected. Trace
reflection uses injective complete keys and surjectivity of backward
typed replies, which the existing trace arrow supplies by bijectivity. -/
theorem Sentence.valid_map_iff (φ : Sentence S exits fields) (f : S ⟶ T) :
    (∀ policy : Model.{0, 0} T.primitive.traceSignature.toSignature,
      TraceInstitution.Sat policy (φ.map f).compile) ↔
    (∀ policy : Model.{0, 0} S.primitive.traceSignature.toSignature,
      TraceInstitution.Sat policy φ.compile) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.valid_map φ f

/-- The existing pointwise directed checker decides validity of the
translated occurrence sentence for an admitted original comparison. -/
theorem Admission.refinement_iff_valid_map {point : Endpoints V K S} [DecidableEq S.Opcode]
    (a : Admission point exits fields) (f : S ⟶ T) :
    a.comparison.fromStore? point.initial = some true ↔
      ∀ policy : Model.{0, 0} T.primitive.traceSignature.toSignature,
        TraceInstitution.Sat policy (a.toSentence.map f).compile := by
  rw [a.toSentence.valid_map_iff f, a.toSentence.compile_eq_admitted a]
  exact Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.verdict_valid a

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
